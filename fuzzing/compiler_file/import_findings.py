#!/usr/bin/env python3
"""Import crash artifacts into the tracked in-repo crashers layout.

Why:
- Fuzzing runs usually write into `output/` (gitignored), which makes it hard to
  publish crashers and collaborate.
- This importer copies (or moves) crash buckets into:
    fuzzing/compiler_file/crashers/open/<kind>/<location>/sig_<signature>/
  and renames every `.fe` file to be descriptive.

This script is safe by default (copy, do not delete sources).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import sys
import time
from pathlib import Path
from typing import Any


PANIC_LOC_RE = re.compile(r"panicked at ([^:]+):(\d+)(?::(\d+))?:")
PID_IN_KEYLINE_RE = re.compile(r"(thread 'main') \(\d+\) (panicked at)")


def _slug(s: str) -> str:
    s = s.strip()
    s = re.sub(r"[^A-Za-z0-9]+", "_", s)
    s = re.sub(r"_+", "_", s)
    return s.strip("_") or "unknown"


def _normalize_key_line(key_line: str) -> str:
    # Remove PID variability: `thread 'main' (12345) panicked at ...`
    return PID_IN_KEYLINE_RE.sub(r"\1 \2", key_line)


def _classify(meta: dict[str, Any]) -> tuple[str, str, dict[str, Any]]:
    """Return (kind, location_slug, details)."""
    rc = int(meta.get("exit_code", -1))
    key_line = str(meta.get("key_line") or "")
    key_line_norm = _normalize_key_line(key_line)
    timeout_s = meta.get("timeout_s")

    # NOTE: Our harness uses 124 for timeouts.
    if rc == 124:
        kind = "hang"
        loc = f"timeout_{int(timeout_s)}s" if isinstance(timeout_s, int) else "timeout"
        return kind, _slug(loc), {"key_line_normalized": key_line_norm}

    if rc == 101 or "panicked at" in key_line_norm:
        kind = "panic"
        m = PANIC_LOC_RE.search(key_line_norm)
        if m:
            path_s = m.group(1)
            line_s = m.group(2)
            col_s = m.group(3)
            file_slug = _slug(path_s.replace("/", "_").replace("\\", "_").replace(".", "_"))
            loc = f"{file_slug}_{line_s}"
            details = {
                "panic_path": path_s,
                "panic_line": int(line_s),
                "panic_col": int(col_s) if col_s is not None else None,
                "key_line_normalized": key_line_norm,
            }
            return kind, _slug(loc), details

        return kind, "unknown_location", {"key_line_normalized": key_line_norm}

    if rc >= 128:
        kind = "signal"
        return kind, _slug(f"rc_{rc}"), {"key_line_normalized": key_line_norm}

    kind = "other"
    # Keep "location" filesystem-friendly; key_line can include absolute paths.
    fallback = key_line_norm.split(" ", 1)[0] if key_line_norm else "unknown"
    return kind, _slug(fallback), {"key_line_normalized": key_line_norm}


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


def _safe_name(name: str, *, max_len: int = 200) -> str:
    if len(name) <= max_len:
        return name
    h = hashlib.sha256(name.encode("utf-8", errors="replace")).hexdigest()[:16]
    # Keep extension stable.
    if name.endswith(".fe"):
        return f"{name[: max_len - (len(h) + 5)]}__{h}.fe"
    return f"{name[: max_len - (len(h) + 3)]}__{h}"


def _write_repro(bucket_dir: Path, *, default_input: str, meta: dict[str, Any]) -> None:
    # Keep scripts stable and overwrite on import; they should reference the new filenames.
    cmd_template = str(meta.get("compiler_cmd_template") or "").strip()
    timeout_s = int(meta.get("timeout_s") or 5)
    env_overrides = meta.get("env") or {}
    if not isinstance(env_overrides, dict):
        env_overrides = {}

    repro_py = bucket_dir / "repro.py"
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
        f"TIMEOUT_S = {timeout_s}\n"
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
        "        # Reasonable default for this repo.\n"
        "        cmd_template = str(repo_root / 'target' / 'debug' / 'fe') + ' check --standalone --color never @@'\n"
        "    cmd = cmd_template.replace('@@', str(input_path))\n"
        "\n"
        "    env = os.environ.copy()\n"
        "    env.update(ENV_OVERRIDES)\n"
        "\n"
        "    if './target/debug/fe' in cmd_template and not (repo_root / 'target' / 'debug' / 'fe').exists():\n"
        "        print('hint: build the compiler first: cargo build -p fe', file=sys.stderr)\n"
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
    repro_sh.write_text(
        "#!/usr/bin/env bash\n"
        "set -euo pipefail\n"
        "\n"
        "BUCKET_DIR=$(cd \"$(dirname \"${BASH_SOURCE[0]}\")\" && pwd)\n"
        f"DEFAULT_INPUT={shlex_quote(default_input)}\n"
        f"CMD_TEMPLATE={shlex_quote(cmd_template)}\n"
        f"TIMEOUT_S={timeout_s}\n"
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


def shlex_quote(s: str) -> str:
    # Minimal POSIX shell quoting.
    if s == "":
        return "''"
    if re.fullmatch(r"[A-Za-z0-9_./:-]+", s):
        return s
    return "'" + s.replace("'", "'\"'\"'") + "'"


def _iter_bucket_dirs(src: Path) -> list[Path]:
    # Buckets are directories containing meta.json.
    if not src.exists():
        return []
    out: list[Path] = []
    for p in sorted(src.iterdir()):
        if not p.is_dir():
            continue
        if (p / "meta.json").is_file():
            out.append(p)
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--src",
        action="append",
        default=[],
        help="Source crashes directory containing per-bucket subdirs with meta.json (repeatable)",
    )
    ap.add_argument(
        "--dest",
        default="fuzzing/compiler_file/crashers/open",
        help="Destination root (default: fuzzing/compiler_file/crashers/open)",
    )
    ap.add_argument(
        "--move",
        action="store_true",
        help="Move inputs/logs instead of copying (safer default is copy)",
    )
    ap.add_argument("--ext", default=".fe", help="Input file extension to import (default: .fe)")
    ap.add_argument(
        "--dry-run",
        action="store_true",
        help="Show what would be imported, without writing anything",
    )
    args = ap.parse_args()

    repo_root = Path(__file__).resolve().parents[2]

    srcs = [Path(s).expanduser().resolve() for s in args.src]
    if not srcs:
        # Reasonable defaults for this repo.
        defaults = [
            repo_root / "output" / "compiler_file_fuzz_stream" / "crashes",
            repo_root / "output" / "compiler_file_fuzz_demo" / "crashes",
            repo_root / "fuzzing" / "compiler_file" / "findings" / "2026-02-25",
        ]
        srcs = [p for p in defaults if p.exists()]

    if not srcs:
        print("no --src provided and no default sources exist", file=sys.stderr)
        return 2

    dest_root = Path(args.dest).expanduser().resolve()
    if not args.dry_run:
        dest_root.mkdir(parents=True, exist_ok=True)

    manifest_path = dest_root / "IMPORT_MANIFEST.jsonl"
    manifest_fh = None if args.dry_run else manifest_path.open("a", encoding="utf-8")

    started = time.time()
    buckets_total = 0
    cases_total = 0
    by_kind: dict[str, int] = {}

    try:
        for src in srcs:
            bucket_dirs = _iter_bucket_dirs(src)
            if not bucket_dirs:
                print(f"[skip] no buckets in {src}", file=sys.stderr)
                continue

            print(f"[src] {src} buckets={len(bucket_dirs)}", file=sys.stderr)
            for bucket_dir in bucket_dirs:
                buckets_total += 1
                meta_path = bucket_dir / "meta.json"
                try:
                    meta = json.loads(meta_path.read_text(encoding="utf-8"))
                except Exception as e:
                    print(f"[warn] failed to read {meta_path}: {e}", file=sys.stderr)
                    continue

                sig = str(meta.get("signature") or bucket_dir.name)
                kind, loc_slug, details = _classify(meta)
                by_kind[kind] = by_kind.get(kind, 0) + 1

                dest_bucket = dest_root / kind / loc_slug / f"sig_{sig}"
                if not args.dry_run:
                    dest_bucket.mkdir(parents=True, exist_ok=True)

                # Preserve original meta as-is, and also write a normalized/annotated meta.
                if not args.dry_run:
                    orig_meta_dst = dest_bucket / "meta.original.json"
                    if not orig_meta_dst.exists():
                        shutil.copy2(meta_path, orig_meta_dst)

                    norm_meta = dict(meta)
                    norm_meta.update(
                        {
                            "import": {
                                "source_bucket_dir": str(bucket_dir),
                                "source_meta": str(meta_path),
                                "imported_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                            },
                            "kind": kind,
                            "location_slug": loc_slug,
                        }
                    )
                    norm_meta.update(details)
                    (dest_bucket / "meta.json").write_text(
                        json.dumps(norm_meta, indent=2, sort_keys=True) + "\n",
                        encoding="utf-8",
                    )

                # Import each `.fe` in this bucket.
                fe_files = [p for p in sorted(bucket_dir.iterdir()) if p.is_file() and p.suffix == args.ext]
                if not fe_files:
                    continue

                default_repro_input: str | None = None
                seed_stem = Path(str(meta.get("seed") or "")).stem or "seed"

                for fe_path in fe_files:
                    cases_total += 1
                    case_stem = fe_path.stem  # strips one suffix (".fe")
                    case_slug = _slug(case_stem)

                    filename = _safe_name(
                        f"{kind}__{loc_slug}__{seed_stem}__{case_slug}__sig_{sig}{args.ext}"
                    )
                    dst_fe = _unique_path(dest_bucket, filename)

                    log_src = fe_path.with_name(fe_path.name + ".log.txt")
                    dst_log = dst_fe.with_name(dst_fe.name + ".log.txt")

                    if args.dry_run:
                        print(f"[dry] {fe_path} -> {dst_fe}", file=sys.stderr)
                        continue

                    # Copy first; optionally delete sources afterwards.
                    shutil.copy2(fe_path, dst_fe)
                    if log_src.is_file():
                        shutil.copy2(log_src, dst_log)

                    if args.move:
                        try:
                            fe_path.unlink()
                        except Exception:
                            pass
                        try:
                            if log_src.is_file():
                                log_src.unlink()
                        except Exception:
                            pass

                    if default_repro_input is None:
                        default_repro_input = dst_fe.name

                    if manifest_fh is not None:
                        rec = {
                            "src_bucket_dir": str(bucket_dir),
                            "src_file": str(fe_path),
                            "src_log": str(log_src) if log_src.is_file() else None,
                            "dest_bucket_dir": str(dest_bucket),
                            "dest_file": str(dst_fe),
                            "dest_log": str(dst_log) if log_src.is_file() else None,
                            "signature": sig,
                            "kind": kind,
                            "location_slug": loc_slug,
                        }
                        manifest_fh.write(json.dumps(rec, sort_keys=True) + "\n")

                # Refresh repro scripts for this bucket based on the first imported case.
                if not args.dry_run and default_repro_input is not None:
                    _write_repro(dest_bucket, default_input=default_repro_input, meta=meta)
    finally:
        if manifest_fh is not None:
            manifest_fh.close()

    dt = time.time() - started
    print(
        f"[done] buckets={buckets_total} cases={cases_total} kinds={by_kind} dt={dt:.1f}s dest={dest_root}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

