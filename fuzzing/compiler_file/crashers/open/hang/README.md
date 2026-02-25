This directory is for **confirmed** compiler hangs (timeouts that still time out under `--timeout-confirm`).

With the current harness defaults (`--timeout 5 --timeout-confirm 30`) and proper timeout process-group killing,
this directory is expected to stay empty unless there is a real hang in the compiler.

If you see hang buckets show up, you can re-validate/prune them with:

```bash
python3 fuzzing/compiler_file/validate_hangs.py --timeout 60 --jobs 4
```

