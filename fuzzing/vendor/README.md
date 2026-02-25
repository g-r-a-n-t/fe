# Vendored Fuzzing Dependencies

This directory is intentionally small and self-contained so fuzzing scripts can run offline.

## universalmutator

- Path: `fuzzing/vendor/universalmutator/`
- Source: snapshot included in `compiler_fuzzing_reference.zip` (upstream: https://github.com/agroce/universalmutator)
- License: Apache-2.0 (see `fuzzing/vendor/universalmutator/LICENSE`)

Local modifications:
- `mutator.py`: make the `comby` dependency optional unless `--comby` is used.
- `genmutants.py`: make the `tabulate` dependency optional unless `--printStat` is used.
