This directory contains the compiler-file fuzzing seed corpus.

`run_stream.sh` and `run_compile_loop.py` discover seeds recursively (`rglob("*.fe")`),
so subdirectories are intentional and recommended.

Current layout:
- Top-level: tiny sanity seeds (`simple.fe`, `move_reinit.fe`, `contract_counter.fe`)
- `type_system/`: HKT/effects/associated-type/generics-heavy programs
- `patterns/`: pattern-matching heavy programs (including larger stress-style cases)
- `contracts/`: contract-heavy programs (`init`, `recv`, storage maps, dispatch)
- `codegen/`: codegen-oriented programs (newtypes, effect pointers, const-heavy flows)

Seed quality rules:
- Prefer seeds that pass `fe check --standalone`.
- Prefer diversity over many near-duplicates.
- Keep a mix of short and medium-sized files to balance mutation speed and feature depth.

Quick validation:

```bash
find fuzzing/compiler_file/seeds -type f -name '*.fe' -print0 \
  | xargs -0 -n1 -P8 ./target/release/fe check --standalone --color never
```
