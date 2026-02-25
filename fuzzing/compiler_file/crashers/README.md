# Compiler File Crashers (Tracked)

This directory is the canonical, in-repo location for compiler fuzzing crashers.

## Layout

- `open/`
  - Crashers for **known-unfixed** bugs. These are intended to be pushed to the repo.
  - Organized as: `open/<kind>/<location>/sig_<signature>/...`
- `fixed/`
  - Optional holding area for crashers that are believed fixed but not yet moved to test fixtures.

Each `sig_<...>/` bucket typically contains:

- One or more `*.fe` inputs (each with a descriptive filename)
- Matching `*.log.txt` compiler output (stdout+stderr)
- `meta.json` (normalized + import annotations)
- `meta.original.json` (verbatim meta from the harness)
- `repro.sh` / `repro.py` (reproduce locally; accepts optional input filename)

## Workflow

1. Fuzz and collect crashers into `open/` (either directly, or by importing from `output/`).
2. File issues / fix compiler bugs.
3. When a crasher no longer crashes, move **one representative** `.fe` into:
   - `crates/fe/tests/fixtures/crash_regressions/`
4. The `crash_regressions` test should ensure the compiler does not panic/hang/signal on those files.

## Importing Existing Artifacts

If you already have crashes under `output/**/crashes/` (gitignored), import them into `open/`:

```bash
python3 fuzzing/compiler_file/import_findings.py \
  --src output/compiler_file_fuzz_stream/crashes \
  --src output/compiler_file_fuzz_demo/crashes \
  --dest fuzzing/compiler_file/crashers/open
```

The importer does **not** delete sources unless you pass `--move`.

## Validating / Pruning Hang Buckets

Timeout buckets can be noisy when fuzzing with a short timeout and high parallelism.
To re-run every hang input with a larger timeout (and prune false positives), use:

```bash
python3 fuzzing/compiler_file/validate_hangs.py --timeout 30 --jobs 4
```

This will:
- keep inputs that still time out
- move inputs that actually panic/crash into `open/panic/...`
- delete inputs that finish without crashing

The validator appends an audit log to:

- `fuzzing/compiler_file/crashers/open/_reports/hang_validation_report.jsonl`
