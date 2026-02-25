#!/usr/bin/env bash
set -euo pipefail

# Convenience wrapper around run_compile_loop.py.
#
# Example:
#   ./fuzzing/compiler_file/run_demo.sh

REPO_ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)

OUT=${OUT:-"$REPO_ROOT/output/compiler_file_fuzz"}
CRASH_DIR=${CRASH_DIR:-"$REPO_ROOT/fuzzing/compiler_file/crashers/open"}
CRASH_LAYOUT=${CRASH_LAYOUT:-structured}
DESCRIPTIVE_NAMES=${DESCRIPTIVE_NAMES:-1}
SEEDS=${SEEDS:-"$REPO_ROOT/fuzzing/compiler_file/seeds"}
TIMEOUT=${TIMEOUT:-5}
TIMEOUT_CONFIRM=${TIMEOUT_CONFIRM:-30}
MAX_MUTANTS_PER_SEED=${MAX_MUTANTS_PER_SEED:-500}
JOBS=${JOBS:-10}

# Default to release for fuzzing speed. Override via FE_BIN=/path/to/fe if needed.
FE_BIN=${FE_BIN:-"$REPO_ROOT/target/release/fe"}

if [[ ! -x "$FE_BIN" ]]; then
  echo "fe binary not found at $FE_BIN" >&2
  echo "hint: build it with: cargo build -p fe --release" >&2
  exit 2
fi

DESCRIPTIVE_FLAG=()
if [[ "$DESCRIPTIVE_NAMES" != "0" ]]; then
  DESCRIPTIVE_FLAG=(--descriptive-names)
fi

python3 "$REPO_ROOT/fuzzing/compiler_file/run_compile_loop.py" \
  --seeds "$SEEDS" \
  --out "$OUT" \
  --crash-dir "$CRASH_DIR" \
  --crash-layout "$CRASH_LAYOUT" \
  "${DESCRIPTIVE_FLAG[@]}" \
  --compiler-cmd "${FE_BIN} check --standalone --color never @@" \
  --timeout "$TIMEOUT" \
  --timeout-confirm "$TIMEOUT_CONFIRM" \
  --jobs "$JOBS" \
  --max-mutants-per-seed "$MAX_MUTANTS_PER_SEED" \
  --env RUST_BACKTRACE=1
