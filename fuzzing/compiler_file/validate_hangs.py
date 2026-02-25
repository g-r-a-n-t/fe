#!/usr/bin/env python3
"""Validate (and prune) hang buckets under crashers/open.

Motivation:
- Many "hang" buckets were created with a small timeout (e.g. 5s) and high
  concurrency, which can yield false positives.
- This script re-runs each `hang/**/sig_*/**/*.fe` with a longer timeout.

Actions:
- If it still times out: keep it as hang.
- If it panics/crashes: move it into the appropriate `open/panic/...` (or
  `open/signal/...`) bucket (with a descriptive filename) and keep the original
  timeout artifacts alongside.
- If it finishes without crashing: delete it from the hang bucket.

This script is destructive (it deletes false-positive hangers). Use `--dry-run`
to preview.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Optional

INTERESTING_RE = re.compile(
    r"(internal compiler error|\bICE\b|panic|assert|segmentation fault|SIGSEGV|stack overflow|AddressSanitizer|UBSan)",
    re.IGNORECASE,
)

PANIC_LOC_RE = re.compile(r"panicked at ([^:]+):(\d+)(?::(\d+))?:")
PID_IN_KEYLINE_RE = re.compile(r"(thread 'main') \(\d+\) (panicked at)")


def _slug(s: str) -> str:
    s = s.strip()
    s = re.sub(r"[^A-Za-z0-9]+", "_", s)
    s = re.sub(r"_+", "_", s)
    return s.strip("_") or "unknown"


def _normalize_key_line(key_line: str) -> str:
    return PID_IN_KEYLINE_RE.sub(r"\1 \2", key_line)


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


def _signature(output: str, rc: int) -> tuple[str, str, str]:
    lines = [ln.strip() for ln in output.splitlines() if ln.strip()]
    key = None
    for ln in lines[:400]:
        if INTERESTING_RE.search(ln):
            key = ln
            break
    if key is None:
        key = lines[0] if lines else "<no-output>"
    key_norm = _normalize_key_line(key)
    sig = hashlib.sha256(f"{rc}:{key_norm}".encode("utf-8", errors="replace")).hexdigest()[:16]
    return sig, key, key_norm


def _extract_location_slug(output: str) -> tuple[str, dict[str, Any]]:
    """Return (location_slug, details)."""
    m = PANIC_LOC_RE.search(output)
    if not m:
        return "unknown_location", {}

    path_s = m.group(1)
    line_s = m.group(2)
    col_s = m.group(3)

    file_slug = _slug(path_s.replace("/", "_").replace("\\", "_").replace(".", "_"))
    loc_slug = _slug(f"{file_slug}_{line_s}")
    return (
        loc_slug,
        {
            "panic_path": path_s,
            "panic_line": int(line_s),
            "panic_col": int(col_s) if col_s is not None else None,
        },
    )


def _case_part_from_filename(p: Path) -> str:
    stem = p.stem
    parts = stem.split("__")
    sig_idx = None
    for i, part in enumerate(parts):
        if part.startswith("sig_"):
            sig_idx = i
            break
    if sig_idx is None:
        return _slug(stem)
    # Our importer format: <kind>__<loc>__<seed>__<case>__sig_<sig>(__dupN)
    if sig_idx >= 4:
        case_parts = parts[3:sig_idx]
        case = "__".join(case_parts)
        return _slug(case)
    return _slug("__".join(parts[:sig_idx]))


def _write_repro(bucket_dir: Path, *, default_input: str, cmd_template: str, timeout_s: int, env_overrides: dict) -> None:
    repro_py = bucket_dir / "repro.py"
    if not repro_py.exists():
        repro_py.write_text(
            "#!/usr/bin/env python3\n"
            "\n"
            "from __future__ import annotations\n"
            "\n"
            "import os\n"
            "import subprocess\n"
            "import sys\n"
            "from pathlib import Path\n"
            "\n"
            f"DEFAULT_INPUT = {json.dumps(default_input)}\n"
            f"CMD_TEMPLATE = {json.dumps(cmd_template)}\n"
            f"TIMEOUT_S = {int(timeout_s)}\n"
            f"ENV_OVERRIDES = {json.dumps(env_overrides, sort_keys=True)}\n"
            "\n"
            "def find_repo_root(start: Path) -> Path:\n"
            "    env_root = os.environ.get('FE_REPO_ROOT') or os.environ.get('REPO_ROOT')\n"
            "    if env_root:\n"
            "        return Path(env_root).expanduser().resolve()\n"
            "    try:\n"
            "        out = subprocess.check_output(\n"
            "            ['git', '-C', str(start), 'rev-parse', '--show-toplevel'],\n"
            "            text=True,\n"
            "            stderr=subprocess.DEVNULL,\n"
            "        ).strip()\n"
            "        if out:\n"
            "            return Path(out).resolve()\n"
            "    except Exception:\n"
            "        pass\n"
            "    for p in [start] + list(start.parents):\n"
            "        if (p / 'Cargo.toml').is_file() and (p / 'fe.toml').is_file():\n"
            "            return p\n"
            "    return start\n"
            "\n"
            "def main() -> int:\n"
            "    bucket_dir = Path(__file__).resolve().parent\n"
            "    repo_root = find_repo_root(bucket_dir)\n"
            "\n"
            "    inp = DEFAULT_INPUT\n"
            "    if len(sys.argv) >= 2:\n"
            "        inp = sys.argv[1]\n"
            "    input_path = (bucket_dir / inp).resolve()\n"
            "\n"
            "    cmd_template = os.environ.get('FE_COMPILER_CMD', CMD_TEMPLATE)\n"
            "    if not cmd_template:\n"
            "        cmd_template = str(repo_root / 'target' / 'debug' / 'fe') + ' check --standalone --color never @@'\n"
            "    cmd = cmd_template.replace('@@', str(input_path))\n"
            "\n"
            "    env = os.environ.copy()\n"
            "    env.update(ENV_OVERRIDES)\n"
            "\n"
            "    print(cmd)\n"
            "    try:\n"
            "        p = subprocess.run(cmd, shell=True, cwd=str(repo_root), env=env, timeout=TIMEOUT_S)\n"
            "        return p.returncode\n"
            "    except subprocess.TimeoutExpired:\n"
            "        print('timeout', file=sys.stderr)\n"
            "        return 124\n"
            "\n"
            "if __name__ == '__main__':\n"
            "    raise SystemExit(main())\n",
            encoding="utf-8",
        )
        repro_py.chmod(0o755)

    repro_sh = bucket_dir / "repro.sh"
    if not repro_sh.exists():
        def sh_quote(s: str) -> str:
            if s == "":
                return "''"
            if re.fullmatch(r"[A-Za-z0-9_./:-]+", s):
                return s
            return "'" + s.replace("'", "'\"'\"'") + "'"

        repro_sh.write_text(
            "#!/usr/bin/env bash\n"
            "set -euo pipefail\n"
            "\n"
            "BUCKET_DIR=$(cd \"$(dirname \"${BASH_SOURCE[0]}\")\" && pwd)\n"
            f"DEFAULT_INPUT={sh_quote(default_input)}\n"
            f"CMD_TEMPLATE={sh_quote(cmd_template)}\n"
            f"TIMEOUT_S={int(timeout_s)}\n"
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
            "if [[ -z \"$CMD_TEMPLATE\" ]]; then\n"
            "  CMD_TEMPLATE=\"$REPO_ROOT/target/debug/fe check --standalone --color never @@\"\n"
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


@dataclass(frozen=True)
class Task:
    bucket_dir: Path
    meta_path: Path
    file_path: Path


@dataclass(frozen=True)
class Result:
    task: Task
    timed_out: bool
    rc: int
    output: str
    dt_s: float


def _discover_tasks(hang_root: Path, ext: str) -> list[Task]:
    tasks: list[Task] = []
    for meta_path in sorted(hang_root.rglob("meta.json")):
        bucket_dir = meta_path.parent
        if not bucket_dir.name.startswith("sig_"):
            continue
        for fe in sorted(bucket_dir.iterdir()):
            if not fe.is_file():
                continue
            if fe.suffix != ext:
                continue
            tasks.append(Task(bucket_dir=bucket_dir, meta_path=meta_path, file_path=fe))
    return tasks


def _run_one(task: Task, *, cmd_template: str, timeout_s: int, env: dict[str, str]) -> Result:
    cmd = cmd_template.replace("@@", str(task.file_path.resolve()))
    started = time.time()
    p = subprocess.Popen(
        cmd,
        shell=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=env,
        start_new_session=True,
    )
    try:
        out, err = p.communicate(timeout=timeout_s)
        combined = (out or "") + (err or "")
        rc = p.returncode
        if rc is None:
            rc = 0
        # Normalize "killed by signal" to the conventional 128+SIGNAL code.
        if isinstance(rc, int) and rc < 0:
            rc = 128 + (-rc)
        return Result(
            task=task,
            timed_out=False,
            rc=int(rc),
            output=combined,
            dt_s=time.time() - started,
        )
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
        combined = (out or "") + (err or "")
        return Result(task=task, timed_out=True, rc=124, output=combined, dt_s=time.time() - started)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--hang-root",
        default="fuzzing/compiler_file/crashers/open/hang",
        help="Root of hang buckets to validate (default: fuzzing/compiler_file/crashers/open/hang)",
    )
    ap.add_argument(
        "--open-root",
        default="fuzzing/compiler_file/crashers/open",
        help="Root of open crashers (default: fuzzing/compiler_file/crashers/open)",
    )
    ap.add_argument(
        "--compiler-cmd",
        default="./target/debug/fe check --standalone --color never @@",
        help="Compiler command template, use @@ for input path",
    )
    ap.add_argument("--timeout", type=int, default=30, help="Validation timeout seconds (default: 30)")
    ap.add_argument("--jobs", type=int, default=4, help="Parallel validation jobs (default: 4)")
    ap.add_argument("--ext", default=".fe", help="File extension to validate (default: .fe)")
    ap.add_argument("--limit", type=int, default=0, help="Only validate the first N files (default: 0=all)")
    ap.add_argument("--dry-run", action="store_true", help="Do not modify the filesystem")
    args = ap.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    hang_root = Path(args.hang_root).expanduser().resolve()
    open_root = Path(args.open_root).expanduser().resolve()

    if "@@" not in args.compiler_cmd:
        raise SystemExit("--compiler-cmd must contain @@")

    if not hang_root.is_dir():
        print(f"hang root does not exist: {hang_root}", file=sys.stderr)
        return 2

    if not args.dry_run:
        open_root.mkdir(parents=True, exist_ok=True)

    tasks = _discover_tasks(hang_root, args.ext)
    if args.limit:
        tasks = tasks[: args.limit]

    if not tasks:
        print(f"no hang files under {hang_root}", file=sys.stderr)
        return 0

    env = os.environ.copy()
    env["NO_COLOR"] = "1"
    env.setdefault("RUST_BACKTRACE", "1")

    started = time.time()
    print(f"[cfg] files={len(tasks)} jobs={args.jobs} timeout={args.timeout}s", file=sys.stderr)

    results: list[Result] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(args.jobs, 1)) as ex:
        futs = [
            ex.submit(_run_one, t, cmd_template=args.compiler_cmd, timeout_s=args.timeout, env=env)
            for t in tasks
        ]
        for i, fut in enumerate(concurrent.futures.as_completed(futs), 1):
            res = fut.result()
            results.append(res)
            if i % 25 == 0 or i == len(futs):
                print(f"[run] {i}/{len(futs)}", file=sys.stderr)

    # Filesystem mutations are done single-threaded to avoid races in shared bucket dirs.
    report_dir = open_root / "_reports"
    if not args.dry_run:
        report_dir.mkdir(parents=True, exist_ok=True)
    report_path = report_dir / "hang_validation_report.jsonl"
    report_fh = None if args.dry_run else report_path.open("a", encoding="utf-8")

    # Cache meta.json per bucket.
    meta_cache: dict[Path, dict[str, Any]] = {}

    keep_hang = 0
    moved_panic = 0
    moved_signal = 0
    deleted = 0

    touched_hang_buckets: set[Path] = set()

    def load_meta(meta_path: Path) -> dict[str, Any]:
        if meta_path in meta_cache:
            return meta_cache[meta_path]
        try:
            meta = json.loads(meta_path.read_text(encoding="utf-8"))
        except Exception:
            meta = {}
        meta_cache[meta_path] = meta
        return meta

    try:
        for res in results:
            bucket_dir = res.task.bucket_dir
            meta_path = res.task.meta_path
            fe_path = res.task.file_path

            touched_hang_buckets.add(bucket_dir)

            meta = load_meta(meta_path)
            seed_stem = Path(str(meta.get("seed") or "")).stem or "seed"
            case_part = _case_part_from_filename(fe_path)

            rec: dict[str, Any] = {
                "hang_bucket": str(bucket_dir),
                "hang_meta": str(meta_path),
                "hang_file": str(fe_path),
                "validation_timeout_s": args.timeout,
                "validation_rc": res.rc,
                "validation_timed_out": res.timed_out,
                "validation_dt_s": round(res.dt_s, 3),
            }

            if res.timed_out:
                keep_hang += 1
                rec["action"] = "keep_hang"
                if report_fh:
                    report_fh.write(json.dumps(rec, sort_keys=True) + "\n")
                continue

            out = res.output
            is_interesting = bool(INTERESTING_RE.search(out)) or res.rc == 101 or res.rc >= 128
            if not is_interesting:
                # False positive timeout: delete it from hang bucket.
                deleted += 1
                rec["action"] = "delete"
                if not args.dry_run:
                    try:
                        fe_path.unlink()
                    except FileNotFoundError:
                        pass
                    log_path = fe_path.with_name(fe_path.name + ".log.txt")
                    try:
                        log_path.unlink()
                    except FileNotFoundError:
                        pass
                if report_fh:
                    report_fh.write(json.dumps(rec, sort_keys=True) + "\n")
                continue

            # Reclassify.
            if res.rc >= 128 and "panicked at" not in out:
                kind = "signal"
                loc_slug = _slug(f"rc_{res.rc}")
                moved_signal += 1
            else:
                kind = "panic"
                loc_slug, details = _extract_location_slug(out)
                rec.update(details)
                moved_panic += 1

            sig, key_line, key_line_norm = _signature(out, res.rc)
            dest_bucket = open_root / kind / loc_slug / f"sig_{sig}"

            rec.update(
                {
                    "action": f"move_to_{kind}",
                    "dest_bucket": str(dest_bucket),
                    "dest_signature": sig,
                    "dest_key_line": key_line,
                    "dest_key_line_normalized": key_line_norm,
                }
            )

            if not args.dry_run:
                dest_bucket.mkdir(parents=True, exist_ok=True)

                filename = _safe_name(f"{kind}__{loc_slug}__{seed_stem}__{case_part}__sig_{sig}{args.ext}")
                dst_fe = _unique_path(dest_bucket, filename)
                dst_log = dst_fe.with_name(dst_fe.name + ".log.txt")

                # Preserve original timeout artifacts alongside the new crash output.
                old_timeout_log = fe_path.with_name(fe_path.name + ".log.txt")
                old_meta = bucket_dir / "meta.json"
                old_meta_orig = bucket_dir / "meta.original.json"
                hang_sig_dir = bucket_dir.name  # e.g. "sig_deadbeef..."

                # Move the input itself.
                shutil.move(str(fe_path), str(dst_fe))

                # Save validation output as the new log.
                dst_log.write_text(out, encoding="utf-8", errors="replace")

                # Keep the old timeout log/meta under stable names (best-effort).
                if old_timeout_log.is_file():
                    shutil.move(
                        str(old_timeout_log),
                        str(dst_fe.with_name(dst_fe.name + ".timeout.log.txt")),
                    )
                if old_meta.is_file():
                    shutil.copy2(old_meta, dest_bucket / f"meta.from_hang.{hang_sig_dir}.json")
                if old_meta_orig.is_file():
                    shutil.copy2(
                        old_meta_orig,
                        dest_bucket / f"meta.from_hang.{hang_sig_dir}.original.json",
                    )

                # Create meta/repro if bucket is new.
                meta_dst = dest_bucket / "meta.json"
                if not meta_dst.exists():
                    env_overrides = {"RUST_BACKTRACE": env.get("RUST_BACKTRACE", "1")}
                    meta_dst.write_text(
                        json.dumps(
                            {
                                "signature": sig,
                                "key_line": key_line,
                                "key_line_normalized": key_line_norm,
                                "exit_code": res.rc,
                                "kind": kind,
                                "location_slug": loc_slug,
                                "seed": str(meta.get("seed") or ""),
                                "compiler_cmd_template": args.compiler_cmd,
                                "timeout_s": args.timeout,
                                "env": env_overrides,
                                "import": {
                                    "reclassified_from_hang_bucket": str(bucket_dir),
                                    "reclassified_at": time.strftime(
                                        "%Y-%m-%dT%H:%M:%SZ", time.gmtime()
                                    ),
                                },
                            },
                            indent=2,
                            sort_keys=True,
                        )
                        + "\n",
                        encoding="utf-8",
                    )
                    _write_repro(
                        dest_bucket,
                        default_input=dst_fe.name,
                        cmd_template=args.compiler_cmd,
                        timeout_s=args.timeout,
                        env_overrides={"RUST_BACKTRACE": env.get("RUST_BACKTRACE", "1")},
                    )

            if report_fh:
                report_fh.write(json.dumps(rec, sort_keys=True) + "\n")
    finally:
        if report_fh:
            report_fh.close()

    # Cleanup empty hang bucket dirs.
    removed_buckets = 0
    if not args.dry_run:
        for b in sorted(touched_hang_buckets):
            if not b.is_dir():
                continue
            fe_left = list(b.glob(f"*{args.ext}"))
            if fe_left:
                continue
            shutil.rmtree(b, ignore_errors=True)
            removed_buckets += 1

    dt = time.time() - started
    print(
        f"[done] keep_hang={keep_hang} moved_panic={moved_panic} moved_signal={moved_signal} "
        f"deleted={deleted} removed_empty_hang_buckets={removed_buckets} dt={dt:.1f}s",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
