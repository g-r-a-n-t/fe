# Findings (Sample Crash Buckets)

This directory is intended to contain a few **real crash buckets** produced by the mutation-based compiler file fuzzing harness:

- `fuzzing/compiler_file/run_compile_loop.py`

At the moment it is intentionally empty (old findings were purged after fixes landed on `master`).

When new crash buckets are found, you can optionally copy a small representative sample here for:
- a sanity check that the harness works end-to-end
- a starting point for filing issues / writing regression tests

## Reproduce

If/when a bucket exists under `fuzzing/compiler_file/findings/<date>/<sig>/`, you can:

1) Build the compiler (release recommended):

```bash
cargo build -p fe --release
```

2) Run one bucket's reproducer:

```bash
python3 fuzzing/compiler_file/findings/<date>/<sig>/repro.py
```

If the bucket is moved outside the git checkout, set:

```bash
export FE_REPO_ROOT=/path/to/your/fe/clone
```

## Notes

- Buckets are keyed by a heuristic signature (exit code + first "interesting" line). Different bugs can collide.
- For sharing, `repro.py` is preferred (it doesn't require `timeout(1)`).
