# Desktop Handoff - 2026-03-24

## Branch / worktree state

Current branch:
- `std-release`

Current git status when this file was written:
- `M Makefile`
- `M crates/fe-web/vendor/tree-sitter-fe.wasm`
- `?? benchmarks/`

Notes:
- I did **not** touch git history.
- `crates/fe-web/vendor/tree-sitter-fe.wasm` was already modified in the worktree when I checked status during this handoff. I did not intentionally edit it as part of the Foundry work.

## What was being built

Goal:
- Add a repo-contained Foundry harness with matching Solidity and Fe contracts that only decode ABI input and re-encode it on return.
- Use it for:
  1. raw-byte equivalence checks between Solidity and Fe
  2. gas-reportable wrapper calls in Foundry

I chose a subproject instead of a repo-root Foundry workspace:
- `benchmarks/foundry-abi/`

Why:
- There is already some transient Foundry integration test code in `crates/fe/tests/build_foundry.rs`.
- A self-contained subproject is easier to move, run, and delete without infecting the repo root.

## Files added / changed for this work

New directory:
- `benchmarks/foundry-abi/`

Files in it:
- `benchmarks/foundry-abi/.gitignore`
- `benchmarks/foundry-abi/README.md`
- `benchmarks/foundry-abi/foundry.toml`
- `benchmarks/foundry-abi/fe/AbiRoundtrip.fe`
- `benchmarks/foundry-abi/src/AbiRoundtripSol.sol`
- `benchmarks/foundry-abi/test/AbiRoundtripEquivalence.t.sol`

Generated local artifacts currently present:
- `benchmarks/foundry-abi/fe-out/AbiRoundtripFe.bin`
- `benchmarks/foundry-abi/fe-out/AbiRoundtripFe.runtime.bin`
- `benchmarks/foundry-abi/fe-out/AbiRoundtripFe.abi.json`
- `benchmarks/foundry-abi/cache/...`
- `benchmarks/foundry-abi/out/...`

Makefile additions:
- `foundry-abi-build-fe`
- `foundry-abi-test`
- `foundry-abi-gas`

## Current contents of the harness

### Fe contract

Path:
- `benchmarks/foundry-abi/fe/AbiRoundtrip.fe`

Current shape coverage:
- `echoUint(uint256) -> uint256`
- `echoString(string) -> string`
- `echoStringU64(string,uint64) -> (string,uint64)`

Important:
- This uses `String<32>` on the Fe side.
- So this harness is currently only valid for strings of length `<= 32` bytes.

### Solidity side

Path:
- `benchmarks/foundry-abi/src/AbiRoundtripSol.sol`

Contracts:
- `AbiRoundtripSol`
- `SolBenchCaller`
- `FeBenchCaller`

Design:
- `AbiRoundtripSol` is the direct Solidity roundtrip target.
- `SolBenchCaller` and `FeBenchCaller` are Solidity wrappers around the Solidity and Fe targets so `forge --gas-report` can attribute gas to named Solidity functions.

### Foundry tests

Path:
- `benchmarks/foundry-abi/test/AbiRoundtripEquivalence.t.sol`

What it does:
- deploys the Solidity target
- reads the Fe `.bin` artifact from `fe-out`
- deploys the Fe target with `create`
- does low-level `.call(...)` against both using identical calldata
- compares raw return bytes with `keccak256(outSol) == keccak256(outFe)`
- also runs benchmark-style wrapper tests through `SolBenchCaller` and `FeBenchCaller`

## Very important: current verification state

I originally tried a nested tuple contract shape:
- Solidity: `echoPair((string,uint64))`
- Fe: nested tuple message/return

That version failed in Foundry:
- `testEchoPairEquivalence()` failed with `return bytes mismatch`
- `testBenchEchoPair()` failed with `panic: memory allocation error (0x41)`

After that, I changed the harness to the current narrower shape:
- `echoStringU64(string,uint64) -> (string,uint64)`

That was done to keep a mixed dynamic/static ABI case while avoiding the currently-broken nested tuple equivalence case.

## Very important: what is stale right now

I changed these source files **after** the previous Fe build / Foundry run:
- `benchmarks/foundry-abi/fe/AbiRoundtrip.fe`
- `benchmarks/foundry-abi/src/AbiRoundtripSol.sol`
- `benchmarks/foundry-abi/test/AbiRoundtripEquivalence.t.sol`

That means the current generated artifacts are stale relative to source:
- `benchmarks/foundry-abi/fe-out/*` is stale
- `benchmarks/foundry-abi/cache/*` is stale
- `benchmarks/foundry-abi/out/*` is stale

So the current important truth is:
- The **source files** are updated to the narrowed `echoStringU64` version.
- The **generated outputs** still reflect the earlier run and should not be trusted.

## Exact commands already run

I confirmed these tools exist on this machine:
- `forge` at `/home/grantwuerker/.foundry/bin/forge`
- `solc` at `/usr/bin/solc`

I successfully built the Fe artifact once using the older contract version:
```sh
cargo run -q -p fe -- build --backend sonatina --contract AbiRoundtripFe --out-dir benchmarks/foundry-abi/fe-out benchmarks/foundry-abi/fe/AbiRoundtrip.fe
```

That wrote:
- `benchmarks/foundry-abi/fe-out/AbiRoundtripFe.bin`
- `benchmarks/foundry-abi/fe-out/AbiRoundtripFe.runtime.bin`
- `benchmarks/foundry-abi/fe-out/AbiRoundtripFe.abi.json`

I then ran Foundry once against the older nested-tuple version:
```sh
forge test --root benchmarks/foundry-abi --offline
```

That result was:
- 5 tests passed
- 2 failed
- failing tests were the nested tuple ones described above

I did **not** get to rerun after narrowing to `echoStringU64` because the user interrupted the turn.

## Next commands to run on the desktop

From repo root:

1. Rebuild the Fe artifact:
```sh
make foundry-abi-build-fe
```

Equivalent direct command:
```sh
cargo run -q -p fe -- build --backend sonatina --contract AbiRoundtripFe --out-dir benchmarks/foundry-abi/fe-out benchmarks/foundry-abi/fe/AbiRoundtrip.fe
```

2. Run the Foundry tests:
```sh
make foundry-abi-test
```

Equivalent direct command:
```sh
forge test --root benchmarks/foundry-abi --offline
```

3. If it passes, get gas numbers:
```sh
make foundry-abi-gas
```

Equivalent direct command:
```sh
forge test --root benchmarks/foundry-abi --offline --gas-report
```

## If you want to clean generated noise first

From repo root:
```sh
rm -rf benchmarks/foundry-abi/cache benchmarks/foundry-abi/out benchmarks/foundry-abi/fe-out
```

Then rerun:
```sh
make foundry-abi-build-fe
make foundry-abi-test
```

## Known constraints / assumptions in the harness

- Fe side uses `String<32>`, so strings must stay at `<= 32` bytes.
- This harness is for ABI roundtrip equivalence only. It does not yet include fuzzing.
- The current narrowed dynamic case is `string + u64`, not nested tuple input.
- If nested tuple equivalence is important, the previous failing result suggests there is still a real mismatch or runtime bug in that path.

## Sandbox / tooling failure that wasted time here

The Codex sandbox wrapper is broken in this environment.

Concrete facts I verified:
- `/usr/bin/bwrap`
- `bubblewrap 0.6.1`
- `bwrap --help` does **not** support `--argv0`
- the Codex wrapper is trying to invoke `bwrap --argv0 ...`
- that causes:
  - `bwrap: Unknown option --argv0`

Package facts on this machine:
- OS: `Pop!_OS 22.04 LTS`
- apt package available for bubblewrap is still only `0.6.1-1ubuntu0.1`
- so `apt` alone does not solve it on this machine
- Nix is also old here, which made the easy Nix fallback annoying

Practical implication:
- The repo is fine.
- The branch is fine.
- The local Codex sandbox path is what is broken.

## Recommendation on the desktop

When you move this to the desktop:
- start from the **source files**, not the generated `fe-out` / `out` / `cache`
- rerun the Fe build and Foundry test from scratch
- if you want to extend the harness, the cleanest next additions are probably:
  - more scalar cases (`bool`, `address`, signed ints)
  - additional mixed static/dynamic function signatures
  - only after that, retry nested tuple input/output once you want to chase the mismatch explicitly

