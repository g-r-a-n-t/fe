#!/usr/bin/env python3
"""Streaming compiler fuzzing harness (infinite by default).

This is the long-run version of Stack A:
- repeatedly generate ONE mutant at a time (UniversalMutator `--fuzz`)
- compile under timeout
- bucket + save interesting results (panic/ICE/crash/hang)

Unlike the batch harness, this mode does NOT persist the full mutant set.
It is designed to run indefinitely with bounded disk usage (only crash buckets grow).

See `README.md` next to this script for usage.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import random
import re
import shlex
import shutil
import subprocess
import sys
import threading
import time
from pathlib import Path
from typing import Optional

INTERESTING_RE = re.compile(
    r"(internal compiler error|\bICE\b|panic|assert|segmentation fault|SIGSEGV|stack overflow|AddressSanitizer|UBSan)",
    re.IGNORECASE,
)

PANIC_LOC_RE = re.compile(r"panicked at ([^:]+):(\d+)(?::(\d+))?:")
PID_IN_KEYLINE_RE = re.compile(r"(thread 'main') \(\d+\) (panicked at)")

def _int0(s: str) -> int:
    # Accept decimal or "0x..." style integers.
    return int(s, 0)


def _run(
    cmd: str,
    *,
    timeout_s: int,
    cwd: Optional[Path] = None,
    env: Optional[dict[str, str]] = None,
) -> tuple[int, str]:
    # Important: we run via a shell for user-supplied command templates.
    # On timeout we MUST kill the whole process group, otherwise the compiler can
    # keep running as an orphan and create a cascade of "hang" false-positives.
    p = subprocess.Popen(
        cmd,
        shell=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        cwd=str(cwd) if cwd else None,
        env=env,
        start_new_session=True,
    )
    try:
        out, err = p.communicate(timeout=timeout_s)
        rc = p.returncode
        if rc is None:
            rc = 0
        # Normalize "killed by signal" to the conventional 128+SIGNAL code.
        if isinstance(rc, int) and rc < 0:
            rc = 128 + (-rc)
        return int(rc), (out or "") + (err or "")
    except subprocess.TimeoutExpired:
        try:
            if os.name == "posix":
                import signal

                os.killpg(p.pid, signal.SIGKILL)
            else:
                p.kill()
        except Exception:
            pass
        out, err = p.communicate()
        return 124, (out or "") + (err or "")


def _signature(output: str, rc: int) -> tuple[str, str]:
    lines = [ln.strip() for ln in output.splitlines() if ln.strip()]
    key = None
    for ln in lines[:400]:
        if INTERESTING_RE.search(ln):
            key = ln
            break
    if key is None:
        key = lines[0] if lines else "<no-output>"

    # Normalize some high-entropy bits (notably the PID in `thread 'main' (123)`).
    key_norm = _normalize_key_line(key)
    h = hashlib.sha256(f"{rc}:{key_norm}".encode("utf-8", errors="replace")).hexdigest()[:16]
    return h, key


def _slug(s: str) -> str:
    s = s.strip()
    s = re.sub(r"[^A-Za-z0-9]+", "_", s)
    s = re.sub(r"_+", "_", s)
    return s.strip("_") or "unknown"


def _normalize_key_line(key_line: str) -> str:
    # Remove PID variability: `thread 'main' (12345) panicked at ...`
    return PID_IN_KEYLINE_RE.sub(r"\1 \2", key_line)


def _classify(rc: int, output: str, key_line: str, timeout_s: int) -> tuple[str, str, str, dict]:
    """Return (kind, location_slug, key_line_normalized, details)."""
    key_line_norm = _normalize_key_line(key_line)

    if rc == 124:
        return "hang", _slug(f"timeout_{int(timeout_s)}s"), key_line_norm, {}

    # Rust panic aborts commonly show up as 101.
    if rc == 101 or "panicked at" in key_line_norm or "panicked at" in output:
        m = PANIC_LOC_RE.search(key_line_norm)
        if m:
            path_s = m.group(1)
            line_s = m.group(2)
            col_s = m.group(3)
            file_slug = _slug(path_s.replace("/", "_").replace("\\", "_").replace(".", "_"))
            loc_slug = _slug(f"{file_slug}_{line_s}")
            return (
                "panic",
                loc_slug,
                key_line_norm,
                {
                    "panic_path": path_s,
                    "panic_line": int(line_s),
                    "panic_col": int(col_s) if col_s is not None else None,
                },
            )
        return "panic", "unknown_location", key_line_norm, {}

    if rc >= 128:
        return "signal", _slug(f"rc_{rc}"), key_line_norm, {}

    # Otherwise, keep an unopinionated bucket.
    return "other", "unknown", key_line_norm, {}


def _bucket_dir(crashes_dir: Path, layout: str, kind: str, loc_slug: str, sig: str) -> Path:
    if layout == "legacy":
        return crashes_dir / sig
    return crashes_dir / kind / loc_slug / f"sig_{sig}"


def _safe_name(name: str, *, max_len: int = 200) -> str:
    if len(name) <= max_len:
        return name
    h = hashlib.sha256(name.encode("utf-8", errors="replace")).hexdigest()[:16]
    if name.endswith(".fe"):
        return f"{name[: max_len - (len(h) + 5)]}__{h}.fe"
    return f"{name[: max_len - (len(h) + 3)]}__{h}"


def _unique_path(dest_dir: Path, filename: str) -> Path:
    p = dest_dir / filename
    if not p.exists():
        return p
    stem = p.stem
    suf = "".join(p.suffixes) or ""
    for i in range(2, 10_000):
        cand = dest_dir / f"{stem}__dup{i}{suf}"
        if not cand.exists():
            return cand
    raise RuntimeError(f"failed to allocate unique filename for {p}")


def _is_interesting(rc: int, output: str) -> bool:
    if rc == 124:
        return True
    if rc >= 128:
        return True
    if rc == 101:
        return True
    return bool(INTERESTING_RE.search(output))


def _seed_slug(seed: Path, seeds_dir: Path) -> str:
    try:
        rel = seed.relative_to(seeds_dir)
        s = str(rel)
    except ValueError:
        s = seed.name
    return re.sub(r"[^A-Za-z0-9._-]+", "_", s)


def _clean_dir(d: Path) -> None:
    if not d.exists():
        return
    for p in d.iterdir():
        try:
            if p.is_dir():
                shutil.rmtree(p)
            else:
                p.unlink()
        except Exception:
            # Best-effort cleanup only.
            pass


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--seeds", required=True, help="Directory containing seed programs")
    ap.add_argument("--out", required=True, help="Output directory")
    ap.add_argument(
        "--crash-dir",
        default="",
        help="Where to write crash buckets. Default: <out>/crashes",
    )
    ap.add_argument(
        "--crash-layout",
        choices=["legacy", "structured"],
        default="legacy",
        help="Crash bucket layout. legacy=<crash-dir>/<sig>, structured=<crash-dir>/<kind>/<location>/sig_<sig>",
    )
    ap.add_argument(
        "--descriptive-names",
        action="store_true",
        help="Save crash inputs with descriptive filenames (kind/location/sig/etc)",
    )
    ap.add_argument(
        "--compiler-cmd",
        required=True,
        help="Compiler command template. Use @@ where the input filename should go.",
    )
    ap.add_argument("--timeout", type=int, default=5)
    ap.add_argument(
        "--timeout-confirm",
        type=int,
        default=30,
        help="If a compile times out at --timeout, re-run once with this timeout before saving a hang (default: 30). Set 0 to disable.",
    )
    ap.add_argument(
        "--jobs",
        type=int,
        default=10,
        help="Parallel workers (default: 10)",
    )
    ap.add_argument(
        "--mutate-flags",
        default="--noCheck --swap",
        help="Extra args forwarded to UniversalMutator (stream mode always adds --fuzz)",
    )
    ap.add_argument(
        "--mutate-cmd",
        default="",
        help="Mutation command to run. Default: python3 fuzzing/compiler_file/mutate.py",
    )
    ap.add_argument(
        "--iters",
        type=int,
        default=0,
        help="Iterations per worker. 0 = run indefinitely (default)",
    )
    ap.add_argument(
        "--status-every",
        type=float,
        default=30.0,
        help="Print status every N seconds (default: 30)",
    )
    ap.add_argument(
        "--env",
        action="append",
        default=[],
        help="Extra env vars for the compiler, as KEY=VALUE (repeatable)",
    )
    ap.add_argument(
        "--ext",
        default=".fe",
        help="Seed file extension to include (default: .fe)",
    )
    ap.add_argument(
        "--rng-seed",
        type=_int0,
        default=None,
        help="Base RNG seed for seed/mutant selection. Default: random per run. Accepts e.g. 123 or 0x7b.",
    )

    args = ap.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    seeds_dir = Path(args.seeds).expanduser().resolve()
    out_dir = Path(args.out).expanduser().resolve()

    if args.jobs < 1:
        args.jobs = os.cpu_count() or 1

    mutate_cmd = args.mutate_cmd.strip()
    if not mutate_cmd:
        mutate_cmd = f"{shlex.quote(sys.executable)} {shlex.quote(str(repo_root / 'fuzzing' / 'compiler_file' / 'mutate.py'))}"

    logs_dir = out_dir / "logs"
    work_root = out_dir / "work"
    crashes_dir = (
        Path(args.crash_dir).expanduser().resolve()
        if args.crash_dir.strip()
        else (out_dir / "crashes")
    )
    for d in (crashes_dir, logs_dir, work_root):
        d.mkdir(parents=True, exist_ok=True)

    seeds = sorted([p for p in seeds_dir.rglob(f"*{args.ext}") if p.is_file()])
    if not seeds:
        print(f"No seeds found in {seeds_dir}", file=sys.stderr)
        return 2

    compiler_env = os.environ.copy()
    for item in args.env:
        if "=" not in item:
            raise SystemExit(f"--env must be KEY=VALUE, got: {item!r}")
        k, v = item.split("=", 1)
        compiler_env[k] = v

    run_seed = args.rng_seed
    if run_seed is None:
        run_seed = int.from_bytes(os.urandom(8), "big")

    stop = threading.Event()

    # Shared counters (best-effort stats only).
    counter_lock = threading.Lock()
    next_id = 0
    attempts = 0
    interesting = 0

    def alloc_id() -> int:
        nonlocal next_id
        with counter_lock:
            i = next_id
            next_id += 1
            return i

    def inc_attempt(inc_i: int = 0) -> tuple[int, int]:
        nonlocal attempts, interesting
        with counter_lock:
            attempts += 1
            interesting += inc_i
            return attempts, interesting

    def worker(worker_id: int) -> None:
        worker_seed = int.from_bytes(
            hashlib.sha256(f"{run_seed}:{worker_id}".encode("utf-8", errors="replace")).digest()[:8],
            "big",
        )
        rnd = random.Random(worker_seed)
        work_dir = work_root / f"worker_{worker_id}"
        work_dir.mkdir(parents=True, exist_ok=True)

        it = 0
        while not stop.is_set():
            if args.iters and it >= args.iters:
                return
            it += 1

            try:
                seed = rnd.choice(seeds)
                seed_abs = seed.resolve()
                seed_slug = _seed_slug(seed, seeds_dir)

                # Keep the worker directory small.
                _clean_dir(work_dir)

                mutate_seed = rnd.getrandbits(64)
                mutate_env = os.environ.copy()
                mutate_env["FE_MUTATE_SEED"] = str(mutate_seed)

                mutate_full_cmd = (
                    f"{mutate_cmd} {shlex.quote(str(seed_abs))} --mutantDir {shlex.quote(str(work_dir))} "
                    f"--fuzz {args.mutate_flags}"
                )
                mrc, mout = _run(
                    mutate_full_cmd,
                    timeout_s=max(args.timeout, 30),
                    cwd=work_dir,
                    env=mutate_env,
                )

                # 255 is UniversalMutator's "no mutants" exit for `--fuzz`.
                if mrc == 255:
                    continue

                fuzz_out = work_dir / "fuzz.out"
                if not fuzz_out.exists():
                    # Keep mutate output for debugging.
                    (logs_dir / f"mutate__worker{worker_id}.txt").write_text(
                        mout, encoding="utf-8", errors="replace"
                    )
                    continue

                case_id = alloc_id()
                case_name = f"{seed_slug}.w{worker_id}.i{case_id:09d}{args.ext}"
                case_path = work_dir / case_name
                shutil.copy2(fuzz_out, case_path)

                compile_cmd = args.compiler_cmd.replace("@@", str(case_path.resolve()))
                rc, out = _run(
                    compile_cmd,
                    timeout_s=args.timeout,
                    cwd=repo_root,
                    env=compiler_env,
                )

                fast_timeout_out: Optional[str] = None
                if rc == 124 and args.timeout_confirm and args.timeout_confirm > args.timeout:
                    # Confirm timeouts with a longer run to avoid "hang" false-positives.
                    fast_timeout_out = out
                    rc2, out2 = _run(
                        compile_cmd,
                        timeout_s=args.timeout_confirm,
                        cwd=repo_root,
                        env=compiler_env,
                    )
                    rc, out = rc2, out2

                is_int = _is_interesting(rc, out)
                _, _ = inc_attempt(1 if is_int else 0)
                if not is_int:
                    # Confirmed false timeout (or just a normal compile error).
                    continue

                sig, key_line = _signature(out, rc)
                classify_timeout = (
                    args.timeout_confirm if (fast_timeout_out is not None and rc == 124) else args.timeout
                )
                kind, loc_slug, key_line_norm, details = _classify(
                    rc, out, key_line, classify_timeout
                )
                bucket = _bucket_dir(crashes_dir, args.crash_layout, kind, loc_slug, sig)
                bucket.mkdir(parents=True, exist_ok=True)

                # Save input + log.
                save_name = case_path.name
                if args.descriptive_names or args.crash_layout == "structured":
                    case_slug = _slug(case_path.stem)
                    save_name = _safe_name(
                        f"{kind}__{loc_slug}__{seed_slug}__{case_slug}__sig_{sig}{args.ext}"
                    )

                dst_fe = _unique_path(bucket, save_name)
                shutil.copy2(case_path, dst_fe)
                (bucket / f"{dst_fe.name}.log.txt").write_text(out, encoding="utf-8", errors="replace")
                if fast_timeout_out is not None:
                    (bucket / f"{dst_fe.name}.fast_timeout.log.txt").write_text(
                        fast_timeout_out, encoding="utf-8", errors="replace"
                    )

                meta_path = bucket / "meta.json"
                if not meta_path.exists():
                    env_overrides = {
                        k: compiler_env[k]
                        for k in sorted(set(compiler_env) & {e.split("=", 1)[0] for e in args.env})
                    }

                    meta = {
                        "signature": sig,
                        "key_line": key_line,
                        "key_line_normalized": key_line_norm,
                        "exit_code": rc,
                        "kind": kind,
                        "location_slug": loc_slug,
                        "seed": str(seed_abs),
                        "compiler_cmd_template": args.compiler_cmd,
                        "compiler_cmd": compile_cmd,
                        "timeout_s": args.timeout,
                        "timeout_confirm_s": args.timeout_confirm if fast_timeout_out is not None else 0,
                        "env": env_overrides,
                        "mutate_cmd": mutate_cmd,
                        "mutate_flags": f"--fuzz {args.mutate_flags}",
                    }
                    meta.update(details)
                    meta_path.write_text(
                        json.dumps(meta, indent=2, sort_keys=True) + "\n", encoding="utf-8"
                    )

                    # Reproducer scripts (bucket-level; points at the first saved input).
                    repro_input = dst_fe.name

                    repro_py = bucket / "repro.py"
                    repro_py.write_text(
                        """#!/usr/bin/env python3\n"""
                        """\n"""
                        """from __future__ import annotations\n\n"""
                        """import os\n"""
                        """import subprocess\n"""
                        """import sys\n"""
                        """from pathlib import Path\n\n"""
                        f"DEFAULT_INPUT = {json.dumps(repro_input)}\n"
                        f"CMD_TEMPLATE = {json.dumps(args.compiler_cmd)}\n"
                        f"TIMEOUT_S = {int(args.timeout)}\n"
                        f"ENV_OVERRIDES = {json.dumps(env_overrides, sort_keys=True)}\n\n"
                        """def find_repo_root(start: Path) -> Path:\n"""
                        """    env_root = os.environ.get('FE_REPO_ROOT') or os.environ.get('REPO_ROOT')\n"""
                        """    if env_root:\n"""
                        """        return Path(env_root).expanduser().resolve()\n\n"""
                        """    try:\n"""
                        """        out = subprocess.check_output(\n"""
                        """            ['git', '-C', str(start), 'rev-parse', '--show-toplevel'],\n"""
                        """            text=True,\n"""
                        """            stderr=subprocess.DEVNULL,\n"""
                        """        ).strip()\n"""
                        """        if out:\n"""
                        """            return Path(out).resolve()\n"""
                        """    except Exception:\n"""
                        """        pass\n\n"""
                        """    for p in [start] + list(start.parents):\n"""
                        """        if (p / 'Cargo.toml').is_file() and (p / 'fe.toml').is_file():\n"""
                        """            return p\n"""
                        """    return start\n\n"""
                        """def main() -> int:\n"""
                        """    bucket_dir = Path(__file__).resolve().parent\n"""
                        """    repo_root = find_repo_root(bucket_dir)\n"""
                        """\n"""
                        """    inp = DEFAULT_INPUT\n"""
                        """    if len(sys.argv) >= 2:\n"""
                        """        inp = sys.argv[1]\n"""
                        """    input_path = (bucket_dir / inp).resolve()\n"""
                        """\n"""
                        """    cmd_template = os.environ.get('FE_COMPILER_CMD', CMD_TEMPLATE)\n"""
                        """    cmd = cmd_template.replace('@@', str(input_path))\n"""
                        """\n"""
                        """    env = os.environ.copy()\n"""
                        """    env.update(ENV_OVERRIDES)\n"""
                        """\n"""
                        """    if './target/debug/fe' in cmd_template and not (repo_root / 'target' / 'debug' / 'fe').exists():\n"""
                        """        print('hint: build the compiler first: cargo build -p fe', file=sys.stderr)\n"""
                        """\n"""
                        """    print(cmd)\n"""
                        """    try:\n"""
                        """        p = subprocess.run(cmd, shell=True, cwd=str(repo_root), env=env, timeout=TIMEOUT_S)\n"""
                        """        return p.returncode\n"""
                        """    except subprocess.TimeoutExpired:\n"""
                        """        print('timeout', file=sys.stderr)\n"""
                        """        return 124\n\n"""
                        """if __name__ == '__main__':\n"""
                        """    raise SystemExit(main())\n""",
                        encoding="utf-8",
                    )
                    repro_py.chmod(0o755)

                    repro_sh = bucket / "repro.sh"
                    repro_sh.write_text(
                        "#!/usr/bin/env bash\n"
                        "set -euo pipefail\n"
                        "\n"
                        "BUCKET_DIR=$(cd \"$(dirname \"${BASH_SOURCE[0]}\")\" && pwd)\n"
                        f"DEFAULT_INPUT={shlex.quote(repro_input)}\n"
                        f"CMD_TEMPLATE={shlex.quote(args.compiler_cmd)}\n"
                        f"TIMEOUT_S={int(args.timeout)}\n"
                        "\n"
                        "INPUT=${1:-$DEFAULT_INPUT}\n"
                        "INPUT=\"$BUCKET_DIR/$INPUT\"\n"
                        "\n"
                        "REPO_ROOT=${FE_REPO_ROOT:-}\n"
                        "if [[ -z \"$REPO_ROOT\" ]]; then\n"
                        "  if git -C \"$BUCKET_DIR\" rev-parse --show-toplevel >/dev/null 2>&1; then\n"
                        "    REPO_ROOT=$(git -C \"$BUCKET_DIR\" rev-parse --show-toplevel)\n"
                        "  else\n"
                        "    REPO_ROOT=\"$BUCKET_DIR\"\n"
                        "  fi\n"
                        "fi\n"
                        "\n"
                        "CMD=${CMD_TEMPLATE//@@/$INPUT}\n"
                        "echo \"$CMD\"\n"
                        "cd \"$REPO_ROOT\"\n"
                        "if command -v timeout >/dev/null 2>&1; then\n"
                        "  timeout \"${TIMEOUT_S}s\" bash -lc \"$CMD\"\n"
                        "else\n"
                        "  echo \"warning: timeout(1) not found; running without timeout\" >&2\n"
                        "  bash -lc \"$CMD\"\n"
                        "fi\n",
                        encoding="utf-8",
                    )
                    repro_sh.chmod(0o755)

                print(
                    f"[!] interesting kind={kind} sig={sig} rc={rc} input={dst_fe.name}",
                    file=sys.stderr,
                )
            except Exception as e:
                print(f"[worker {worker_id}] error: {e}", file=sys.stderr)
                continue

    def status_printer() -> None:
        last = time.time()
        last_attempts = 0
        while not stop.is_set():
            time.sleep(max(args.status_every, 1.0))
            now = time.time()
            with counter_lock:
                a = attempts
                i = interesting
            delta = a - last_attempts
            dt = now - last
            rate = delta / dt if dt > 0 else 0.0
            print(f"[status] attempts={a} interesting={i} rate={rate:.1f}/s", file=sys.stderr)
            last = now
            last_attempts = a

    print(
        f"[cfg] seeds={seeds_dir} out={out_dir} jobs={args.jobs} timeout={args.timeout}s timeout_confirm={args.timeout_confirm}s iters={args.iters or 'inf'} rng_seed={run_seed}",
        file=sys.stderr,
    )

    status_thread = threading.Thread(target=status_printer, name="status", daemon=True)
    status_thread.start()

    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
            futures = [ex.submit(worker, wid) for wid in range(args.jobs)]
            for fut in concurrent.futures.as_completed(futures):
                # Propagate exceptions (should be rare; most failures are handled in-worker).
                fut.result()
    except KeyboardInterrupt:
        print("[!] stopping (KeyboardInterrupt)", file=sys.stderr)
        stop.set()
        return 130

    stop.set()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
