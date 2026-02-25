#!/usr/bin/env bash
set -euo pipefail

# Convenience wrapper around run_stream_loop.py.
#
# Runs indefinitely by default. Stop with Ctrl+C.
#
# Example:
#   ./fuzzing/compiler_file/run_stream.sh

REPO_ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)

OUT=${OUT:-"$REPO_ROOT/output/compiler_file_fuzz_stream"}
CRASH_DIR=${CRASH_DIR:-"$REPO_ROOT/fuzzing/compiler_file/crashers/open"}
CRASH_LAYOUT=${CRASH_LAYOUT:-structured}
DESCRIPTIVE_NAMES=${DESCRIPTIVE_NAMES:-1}
SEEDS=${SEEDS:-"$REPO_ROOT/fuzzing/compiler_file/seeds"}
TIMEOUT=${TIMEOUT:-5}
TIMEOUT_CONFIRM=${TIMEOUT_CONFIRM:-30}
JOBS=${JOBS:-10}
RNG_SEED=${RNG_SEED:-}

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

RNG_SEED_FLAG=()
if [[ -n "$RNG_SEED" ]]; then
  RNG_SEED_FLAG=(--rng-seed "$RNG_SEED")
fi

python3 "$REPO_ROOT/fuzzing/compiler_file/run_stream_loop.py" \
  --seeds "$SEEDS" \
  --out "$OUT" \
  --crash-dir "$CRASH_DIR" \
  --crash-layout "$CRASH_LAYOUT" \
  "${DESCRIPTIVE_FLAG[@]}" \
  "${RNG_SEED_FLAG[@]}" \
  --compiler-cmd "${FE_BIN} check --standalone --color never @@" \
  --timeout "$TIMEOUT" \
  --timeout-confirm "$TIMEOUT_CONFIRM" \
  --jobs "$JOBS" \
  --env RUST_BACKTRACE=1
