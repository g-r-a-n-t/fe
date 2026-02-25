#!/usr/bin/env python3
"""Line-deletion minimizer for compiler crashers.

This is a pragmatic ddmin-style reducer:
- tries to delete chunks of lines
- keeps changes only if the failure still reproduces

By default it tries to preserve the *same* bucket signature (rc + first interesting line).
"""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import subprocess
import sys
import tempfile
from math import ceil
from pathlib import Path

INTERESTING_RE = re.compile(
    r"(internal compiler error|\bICE\b|panic|assert|segmentation fault|SIGSEGV|stack overflow|AddressSanitizer|UBSan)",
    re.IGNORECASE,
)
PID_IN_KEYLINE_RE = re.compile(r"(thread 'main') \(\d+\) (panicked at)")


def _run(cmd: str, *, timeout_s: int, cwd: Path, env: dict[str, str]) -> tuple[int, str]:
    p = subprocess.Popen(
        cmd,
        shell=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        cwd=str(cwd),
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


def _is_interesting(rc: int, output: str) -> bool:
    if rc == 124:
        return True
    if rc >= 128:
        return True
    if rc == 101:
        return True
    return bool(INTERESTING_RE.search(output))


def _signature(output: str, rc: int) -> tuple[str, str]:
    lines = [ln.strip() for ln in output.splitlines() if ln.strip()]
    key = None
    for ln in lines[:400]:
        if INTERESTING_RE.search(ln):
            key = ln
            break
    if key is None:
        key = lines[0] if lines else "<no-output>"

    # Keep panic signatures stable across runs where the thread PID changes.
    key_norm = _normalize_key_line(key)
    h = hashlib.sha256(f"{rc}:{key_norm}".encode("utf-8", errors="replace")).hexdigest()[:16]
    return h, key


def _normalize_key_line(key_line: str) -> str:
    return PID_IN_KEYLINE_RE.sub(r"\1 \2", key_line)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", required=True, help="Input file to minimize")
    ap.add_argument("--output", required=True, help="Where to write the minimized file")
    ap.add_argument(
        "--compiler-cmd",
        required=True,
        help="Compiler command template. Use @@ where the input filename should go.",
    )
    ap.add_argument("--timeout", type=int, default=5)
    ap.add_argument(
        "--same-sig",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Require the exact same signature to reproduce (default: true)",
    )
    ap.add_argument(
        "--env",
        action="append",
        default=[],
        help="Extra env vars for the compiler, as KEY=VALUE (repeatable)",
    )

    args = ap.parse_args()

    repo_root = Path(__file__).resolve().parents[2]

    inp = Path(args.input)
    if not inp.is_file():
        print(f"Not a file: {inp}", file=sys.stderr)
        return 2

    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    env = os.environ.copy()
    for item in args.env:
        if "=" not in item:
            raise SystemExit(f"--env must be KEY=VALUE, got: {item!r}")
        k, v = item.split("=", 1)
        env[k] = v

    base_cmd = args.compiler_cmd.replace("@@", str(inp))
    base_rc, base_out = _run(base_cmd, timeout_s=args.timeout, cwd=repo_root, env=env)
    if not _is_interesting(base_rc, base_out):
        print("Input is not interesting under the provided compiler command.", file=sys.stderr)
        return 2

    base_sig, base_key = _signature(base_out, base_rc)
    print(f"baseline: rc={base_rc} sig={base_sig} key={base_key}")

    lines = inp.read_text(encoding="utf-8", errors="replace").splitlines(keepends=True)
    if len(lines) < 2:
        out_path.write_text("".join(lines), encoding="utf-8")
        print(f"wrote {out_path} (already minimal)")
        return 0

    def reproduces(candidate_lines: list[str]) -> bool:
        with tempfile.NamedTemporaryFile("w", suffix=inp.suffix, delete=False) as tf:
            tf.write("".join(candidate_lines))
            tmp_name = tf.name

        cmd = args.compiler_cmd.replace("@@", tmp_name)
        rc, out = _run(cmd, timeout_s=args.timeout, cwd=repo_root, env=env)

        try:
            Path(tmp_name).unlink(missing_ok=True)
        except Exception:
            pass

        if not _is_interesting(rc, out):
            return False
        if not args.same_sig:
            return True

        sig, _ = _signature(out, rc)
        return sig == base_sig

    n = 2
    while len(lines) >= 2:
        chunk_size = ceil(len(lines) / n)
        found = False

        for i in range(n):
            start = i * chunk_size
            if start >= len(lines):
                break
            end = min((i + 1) * chunk_size, len(lines))

            candidate = lines[:start] + lines[end:]
            if not candidate:
                continue

            if reproduces(candidate):
                lines = candidate
                n = max(n - 1, 2)
                found = True
                print(f"reduced: lines={len(lines)} n={n}")
                break

        if found:
            continue

        if n >= len(lines):
            break
        n = min(n * 2, len(lines))

    out_path.write_text("".join(lines), encoding="utf-8")
    print(f"wrote {out_path} (lines={len(lines)})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
