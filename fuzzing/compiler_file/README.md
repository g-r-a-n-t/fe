# Compiler File Fuzzing (Mutation-Based)

Goal: find **compiler crashes / panics / ICEs / timeouts** by mutating `.fe` source files and compiling them.

This is an out-of-process mutation loop ("Stack A") based on `compiler_fuzzing_reference.zip`.

## What You Get

- A small starter seed corpus: `fuzzing/compiler_file/seeds/`
- A vendored mutation engine (Universal Mutator): `fuzzing/vendor/universalmutator/`
- A parallel compile loop harness:
  - `fuzzing/compiler_file/run_compile_loop.py`
  - buckets interesting results into a crashers directory (see `--crash-dir`)
  - saves logs + `meta.json` + portable repro scripts (`repro.py`, `repro.sh`)
- A pragmatic minimizer (optional): `fuzzing/compiler_file/minimize_ddmin.py`
- A tracked, in-repo crashers area (for publishing open bugs): `fuzzing/compiler_file/crashers/`

## Directory Layout

- `fuzzing/compiler_file/`
  - `mutate.py`: offline-friendly wrapper for the vendored Universal Mutator
  - `run_compile_loop.py`: main harness (mutate -> compile -> bucket)
  - `run_stream_loop.py`: streaming harness (mutate one-at-a-time; runs indefinitely)
  - `run_stream.sh`: convenience wrapper for `run_stream_loop.py`
  - `minimize_ddmin.py`: line-deletion reducer
  - `seeds/`: starter corpus (add more!)
- `fuzzing/vendor/universalmutator/`: snapshot of the `universalmutator` Python package (Apache-2.0)

## Requirements

- `python3`
- a built `fe` binary (release recommended):

```bash
cargo build -p fe --release
```

If `cargo` has trouble fetching git dependencies, try:

```bash
CARGO_NET_GIT_FETCH_WITH_CLI=true cargo build -p fe --release
```

Optional (for better stack traces):

- `RUST_BACKTRACE=1` or `RUST_BACKTRACE=full`

## Quick Start (Crash-Finding)

Run (defaults to the release binary):

```bash
./fuzzing/compiler_file/run_demo.sh
```

Or run the harness directly:

```bash
python3 fuzzing/compiler_file/run_compile_loop.py \
  --seeds fuzzing/compiler_file/seeds \
  --out output/compiler_file_fuzz \
  --crash-dir fuzzing/compiler_file/crashers/open \
  --crash-layout structured \
  --descriptive-names \
  --compiler-cmd './target/release/fe check --standalone --color never @@' \
  --timeout 5 \
  --jobs 12 \
  --max-mutants-per-seed 500 \
  --env RUST_BACKTRACE=1
```

Notes:
- `--jobs` is parallelism for compiler invocations. Default is `10` (override as needed).
- `--color never` makes logs stable (no ANSI noise).
- `--standalone` compiles the file without needing an ingot/workspace.

## Why `fe check` (Not `fe build`)?

For this harness, `fe check` is the recommended default because it does not write build artifacts.

If you fuzz `fe build` in parallel, be careful: many mutants may try to write into the same default `out/` directory, which can cause contention and flaky results. If you want to fuzz codegen via `fe build`, either:
- run with `--jobs 1`, or
- wrap the compiler command in a script that chooses a unique `--out-dir` per mutant.

For debugging, you can use the debug binary:

```bash
cargo build -p fe

python3 fuzzing/compiler_file/run_compile_loop.py \
  --seeds fuzzing/compiler_file/seeds \
  --out output/compiler_file_fuzz \
  --crash-dir fuzzing/compiler_file/crashers/open \
  --crash-layout structured \
  --descriptive-names \
  --compiler-cmd './target/debug/fe check --standalone --color never @@' \
  --timeout 5 \
  --jobs 12 \
  --max-mutants-per-seed 2000 \
  --env RUST_BACKTRACE=1
```

## Run Indefinitely (Streaming Mode)

Batch mode is finite (it compiles a fixed set of mutants). For long fuzzing runs, use streaming mode which generates one mutant at a time with UniversalMutator `--fuzz` and runs until you stop it.

```bash
./fuzzing/compiler_file/run_stream.sh
```

Streaming mode writes findings automatically under:

- If using `--crash-layout legacy`: `<crash-dir>/<sig>/...`
- If using `--crash-layout structured`: `<crash-dir>/<kind>/<location>/sig_<sig>/...`

Stop with Ctrl+C.

To reduce false hang buckets under heavy load, streaming mode re-runs any `--timeout` timeout once with a longer timeout (`--timeout-confirm`, default: 30s). You can override via:

```bash
TIMEOUT_CONFIRM=60 ./fuzzing/compiler_file/run_stream.sh
```

## Output Format

Given `--out output/compiler_file_fuzz`, the harness writes:

- `output/compiler_file_fuzz/mutants/<seed>/...` mutated `.fe` files
- `output/compiler_file_fuzz/logs/compile__<seed>__<mutant>.txt` compiler output per mutant
- a crashers directory (default: `output/compiler_file_fuzz/crashes/`, or set via `--crash-dir`)

Recommended (publishable) setup:

- `--out output/compiler_file_fuzz` (gitignored scratch space)
- `--crash-dir fuzzing/compiler_file/crashers/open --crash-layout structured` (tracked in-repo)

Each crash bucket contains:

- `<mutant>.fe`: the input
- `<mutant>.fe.log.txt`: compiler stdout+stderr
- `meta.json`: signature + command + metadata
- `repro.py`: portable reproducer (auto-finds repo root via `git` or `FE_REPO_ROOT`)
- `repro.sh`: shell reproducer (same idea)

Reproduce a bucket:

```bash
python3 fuzzing/compiler_file/crashers/open/<kind>/<location>/sig_<sig>/repro.py
```

If the bucket is outside the repo (or `git` cannot find the toplevel), set:

```bash
export FE_REPO_ROOT=/path/to/your/fe/clone
```

## How Mutation Works (Universal Mutator)

The harness uses Universal Mutator rule-based mutations on `.fe` files.

By default we pass:
- `--noCheck`: do not try to compile/validate mutants during mutation generation
- `--swap`: also try adjacent-line swaps

Important: the upstream `universalmutator` includes a historical `fe_handler.py` that expects an older `fe` CLI.
For this repo's `fe` CLI, you should keep using `--noCheck` unless you update the handler.

You can generate mutants manually:

```bash
python3 fuzzing/compiler_file/mutate.py fuzzing/compiler_file/seeds/simple.fe \
  --mutantDir /tmp/fe_mutants \
  --noCheck --swap
```

## Tuning / Useful Flags

`run_compile_loop.py` flags:

- `--jobs N`: parallel compiler processes (default: 10)
- `--timeout SECONDS`: per-compile timeout (hang detection)
- `--timeout-confirm SECONDS`: if a compile hits `--timeout`, re-run once with this longer timeout before saving a hang (reduces false hangs)
- `--max-mutants-per-seed N`: cap work per seed (0 = unlimited)
- `--mutate-flags '...'`: forwarded to Universal Mutator
- `--mutate-cmd '...'`: override mutation command (default: `python3 .../mutate.py`)
- `--env KEY=VALUE`: add environment variables for the compiler (repeatable)
- `--crash-dir DIR`: where to write crash buckets
- `--crash-layout legacy|structured`: bucket directory layout
- `--descriptive-names`: make saved `*.fe` filenames include kind/location/sig info

Practical recommendations:
- Start with `--max-mutants-per-seed 200` until everything is stable.
- Then raise to `2000+` and add more seeds.
- Use a mixed corpus: small programs + real-world contracts.

## Minimization (Optional)

`minimize_ddmin.py` is a ddmin-style line deletion reducer. It repeatedly deletes chunks of lines and keeps the change if the failure still reproduces.

Example:

```bash
python3 fuzzing/compiler_file/minimize_ddmin.py \
  --input output/compiler_file_fuzz/crashes/<sig>/<file>.fe \
  --output /tmp/min.fe \
  --compiler-cmd './target/release/fe check --standalone --color never @@' \
  --timeout 5 \
  --env RUST_BACKTRACE=1
```

By default it tries to preserve the *same* bucket signature. To allow any "interesting" failure, pass `--no-same-sig`.

## Troubleshooting

- `mutate.py` fails with missing `comby`:
  - You're using `--comby`. Either install the `comby` Python package or remove `--comby`.
- No crash buckets:
  - Increase `--max-mutants-per-seed`.
  - Add more seeds (real contracts tend to work better than tiny snippets).
  - Ensure your `--compiler-cmd` is correct and includes `@@`.
- Buckets are too coarse:
  - The signature is heuristic (exit code + first "interesting" line). It's expected that unrelated failures may collide.

## Importing From `output/`

If you already have crash buckets under `output/**/crashes/` (gitignored), import them into the tracked tree:

```bash
python3 fuzzing/compiler_file/import_findings.py \
  --src output/compiler_file_fuzz_stream/crashes \
  --src output/compiler_file_fuzz_demo/crashes \
  --dest fuzzing/compiler_file/crashers/open
```
