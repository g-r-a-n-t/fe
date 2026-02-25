#!/usr/bin/env python3
"""Crash-finding compiler fuzzing harness (Stack A).

This is an out-of-process loop:
- take a seed corpus of `.fe` source files
- generate mutants using UniversalMutator (vendored in-repo)
- compile each mutant under a timeout
- bucket + save interesting results (panic/ICE/crash/hang)

See `README.md` next to this script for usage.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Optional

# Heuristic patterns for "interesting" failures.
INTERESTING_RE = re.compile(
    r"(internal compiler error|\bICE\b|panic|assert|segmentation fault|SIGSEGV|stack overflow|AddressSanitizer|UBSan)",
    re.IGNORECASE,
)

PANIC_LOC_RE = re.compile(r"panicked at ([^:]+):(\d+)(?::(\d+))?:")
PID_IN_KEYLINE_RE = re.compile(r"(thread 'main') \(\d+\) (panicked at)")


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
    """Return (sig, key_line).

    We keep it simple: rc + the first matching "interesting" line.
    """

    lines = [ln.strip() for ln in output.splitlines() if ln.strip()]
    key = None
    for ln in lines[:400]:
        if INTERESTING_RE.search(ln):
            key = ln
            break
    if key is None:
        key = lines[0] if lines else "<no-output>"

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
    # 124 = our timeout marker.
    if rc == 124:
        return True

    # "Killed by signal" style exits.
    if rc >= 128:
        return True

    # Rust panic aborts commonly show up as 101.
    if rc == 101:
        return True

    return bool(INTERESTING_RE.search(output))


def _seed_slug(seed: Path, seeds_dir: Path) -> str:
    try:
        rel = seed.relative_to(seeds_dir)
        s = str(rel)
    except ValueError:
        s = seed.name
    # Keep filesystem friendly.
    return re.sub(r"[^A-Za-z0-9._-]+", "_", s)


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
        help="Parallel compiler jobs (default: 10)",
    )
    ap.add_argument(
        "--mutate-flags",
        default="--noCheck --swap",
        help="Args forwarded to UniversalMutator.",
    )
    ap.add_argument(
        "--mutate-cmd",
        default="",
        help="Mutation command to run. Default: python3 fuzzing/compiler_file/mutate.py",
    )
    ap.add_argument(
        "--max-mutants-per-seed",
        type=int,
        default=0,
        help="0 = unlimited",
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

    args = ap.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    seeds_dir = Path(args.seeds).expanduser().resolve()
    out_dir = Path(args.out).expanduser().resolve()

    mutate_cmd = args.mutate_cmd.strip()
    if not mutate_cmd:
        mutate_cmd = f"{shlex.quote(sys.executable)} {shlex.quote(str(repo_root / 'fuzzing' / 'compiler_file' / 'mutate.py'))}"

    mutants_dir = out_dir / "mutants"
    logs_dir = out_dir / "logs"
    crashes_dir = (
        Path(args.crash_dir).expanduser().resolve()
        if args.crash_dir.strip()
        else (out_dir / "crashes")
    )
    for d in (mutants_dir, crashes_dir, logs_dir):
        d.mkdir(parents=True, exist_ok=True)

    seeds = sorted([p for p in seeds_dir.rglob(f"*{args.ext}") if p.is_file()])
    if not seeds:
        print(f"No seeds found in {seeds_dir}", file=sys.stderr)
        return 2

    # Compiler env (kept deterministic-ish; callers can add overrides).
    compiler_env = os.environ.copy()
    for item in args.env:
        if "=" not in item:
            raise SystemExit(f"--env must be KEY=VALUE, got: {item!r}")
        k, v = item.split("=", 1)
        compiler_env[k] = v

    jobs = args.jobs
    if jobs < 1:
        jobs = os.cpu_count() or 1

    total_interesting = 0

    def compile_one(m: Path) -> tuple[Path, int, str, str, Optional[str]]:
        compile_cmd = args.compiler_cmd.replace("@@", str(m.resolve()))
        rc, out = _run(
            compile_cmd,
            timeout_s=args.timeout,
            cwd=repo_root,
            env=compiler_env,
        )
        fast_timeout_out: Optional[str] = None
        if rc == 124 and args.timeout_confirm and args.timeout_confirm > args.timeout:
            fast_timeout_out = out
            rc2, out2 = _run(
                compile_cmd,
                timeout_s=args.timeout_confirm,
                cwd=repo_root,
                env=compiler_env,
            )
            rc, out = rc2, out2
        return m, rc, out, compile_cmd, fast_timeout_out

    print(
        f"[cfg] seeds={seeds_dir} out={out_dir} crash_dir={crashes_dir} jobs={jobs} timeout={args.timeout}s timeout_confirm={args.timeout_confirm}s",
        file=sys.stderr,
    )

    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
        for seed in seeds:
            seed_abs = seed.resolve()
            seed_slug = _seed_slug(seed, seeds_dir)
            print(f"[seed] {seed_slug}: mutating {seed_abs}", file=sys.stderr)

            # Put each seed's mutants in its own subdir to avoid name collisions.
            seed_mut_dir = mutants_dir / seed_slug
            seed_mut_dir.mkdir(parents=True, exist_ok=True)

            mutate_log = logs_dir / f"mutate__{seed_slug}.txt"
            mutate_log.write_text("", encoding="utf-8")

            # Keep temporary `.tmp_mutant.*` files out of the repo root.
            mutate_full_cmd = (
                f"{mutate_cmd} {shlex.quote(str(seed_abs))} --mutantDir {shlex.quote(str(seed_mut_dir))} {args.mutate_flags}"
            )
            mrc, mout = _run(
                mutate_full_cmd,
                timeout_s=max(args.timeout, 30),
                cwd=seed_mut_dir,
            )
            mutate_log.write_text(mout, encoding="utf-8", errors="replace")
            if mrc != 0:
                # UniversalMutator sometimes returns nonzero for partial issues; keep going.
                print(f"[!] mutate rc={mrc} for {seed}", file=sys.stderr)

            mutants = [p for p in seed_mut_dir.iterdir() if p.is_file()]
            mutants = [p for p in mutants if p.suffix == args.ext and not p.name.startswith(".tmp_mutant")]
            # Prefer numeric ordering for the usual `<base>.mutant.<n>.fe` naming.
            num_re = re.compile(rf"\.mutant\.(\d+){re.escape(args.ext)}$")
            mutants.sort(
                key=lambda p: (
                    int(m.group(1)) if (m := num_re.search(p.name)) else 1_000_000_000,
                    p.name,
                )
            )
            print(f"[seed] {seed_slug}: mutants={len(mutants)}", file=sys.stderr)
            if args.max_mutants_per_seed and len(mutants) > args.max_mutants_per_seed:
                mutants = mutants[: args.max_mutants_per_seed]
            print(f"[seed] {seed_slug}: compiling={len(mutants)}", file=sys.stderr)

            if not mutants:
                continue

            started = time.time()
            completed = 0

            mutant_iter = iter(mutants)
            in_flight: set[concurrent.futures.Future[tuple[Path, int, str, str]]] = set()

            max_in_flight = max(jobs * 4, jobs)

            def submit_next() -> None:
                try:
                    m = next(mutant_iter)
                except StopIteration:
                    return
                in_flight.add(ex.submit(compile_one, m))

            while len(in_flight) < max_in_flight:
                before = len(in_flight)
                submit_next()
                if len(in_flight) == before:
                    break

            while in_flight:
                done, not_done = concurrent.futures.wait(
                    in_flight, return_when=concurrent.futures.FIRST_COMPLETED
                )
                in_flight = not_done

                for fut in done:
                    m, rc, out, compile_cmd, fast_timeout_out = fut.result()
                    completed += 1

                    log_path = logs_dir / f"compile__{seed_slug}__{m.name}.txt"
                    log_path.write_text(out, encoding="utf-8", errors="replace")

                    if _is_interesting(rc, out):
                        sig, key_line = _signature(out, rc)
                        classify_timeout = (
                            args.timeout_confirm
                            if (fast_timeout_out is not None and rc == 124)
                            else args.timeout
                        )
                        kind, loc_slug, key_line_norm, details = _classify(
                            rc, out, key_line, classify_timeout
                        )
                        bucket = _bucket_dir(crashes_dir, args.crash_layout, kind, loc_slug, sig)
                        bucket.mkdir(parents=True, exist_ok=True)

                        save_name = m.name
                        if args.descriptive_names or args.crash_layout == "structured":
                            case_slug = _slug(m.stem)
                            save_name = _safe_name(
                                f"{kind}__{loc_slug}__{seed_slug}__{case_slug}__sig_{sig}{args.ext}"
                            )

                        dst_fe = _unique_path(bucket, save_name)
                        dst_log = dst_fe.with_name(dst_fe.name + ".log.txt")
                        shutil.copy2(m, dst_fe)
                        shutil.copy2(log_path, dst_log)
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
                                "seed": str(seed),
                                "mutant": str(m),
                                "compiler_cmd_template": args.compiler_cmd,
                                "compiler_cmd": compile_cmd,
                                "timeout_s": args.timeout,
                                "timeout_confirm_s": args.timeout_confirm if fast_timeout_out is not None else 0,
                                "env": env_overrides,
                                "mutate_cmd": mutate_cmd,
                                "mutate_flags": args.mutate_flags,
                            }
                            meta.update(details)
                            meta_path.write_text(
                                json.dumps(meta, indent=2, sort_keys=True) + "\n", encoding="utf-8"
                            )

                            bucket_dir = bucket

                            # Portable reproducer: tries FE_REPO_ROOT, git, then walks parents.
                            repro_py = bucket_dir / "repro.py"
                            repro_py.write_text(
                                """#!/usr/bin/env python3\n"""
                                """\n"""
                                """from __future__ import annotations\n\n"""
                                """import os\n"""
                                """import subprocess\n"""
                                """import sys\n"""
                                """from pathlib import Path\n\n"""
                                f"DEFAULT_INPUT = {json.dumps(dst_fe.name)}\n"
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
                                """    # Helpful hint if using the default debug binary path.\n"""
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

                            repro_sh = bucket_dir / "repro.sh"
                            repro_sh.write_text(
                                "#!/usr/bin/env bash\n"
                                "set -euo pipefail\n"
                                "\n"
                                "BUCKET_DIR=$(cd \"$(dirname \"${BASH_SOURCE[0]}\")\" && pwd)\n"
                                f"DEFAULT_INPUT={shlex.quote(dst_fe.name)}\n"
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

                        total_interesting += 1
                        print(
                            f"[!] interesting kind={kind} sig={sig} input={dst_fe.name} rc={rc}",
                            file=sys.stderr,
                        )

                    if completed % 25 == 0 or completed == len(mutants):
                        elapsed = time.time() - started
                        rate = completed / elapsed if elapsed > 0 else 0.0
                        print(
                            f"[seed] {seed_slug}: compiled {completed}/{len(mutants)} ({rate:.1f}/s)",
                            file=sys.stderr,
                        )

                    while len(in_flight) < max_in_flight:
                        before = len(in_flight)
                        submit_next()
                        if len(in_flight) == before:
                            break

    print(f"Done. Buckets in {crashes_dir} (interesting={total_interesting})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
