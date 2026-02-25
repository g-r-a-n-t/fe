#!/usr/bin/env python3
"""Offline-friendly wrapper for UniversalMutator.

The reference bundle includes a snapshot of the `universalmutator` Python package.
This script makes it runnable without installing anything from PyPI.

Usage is intentionally compatible with the upstream `mutate` console script:
  mutate.py <sourcefile> [<language>] [<rule1> <rule2>...] [--noCheck] ...

Example:
  ./mutate.py seeds/simple.fe --mutantDir out/mutants --noCheck --swap
"""

from __future__ import annotations

import os
import random
import sys
from pathlib import Path


def main() -> int:
    seed_s = os.environ.get("FE_MUTATE_SEED", "").strip()
    if seed_s:
        try:
            random.seed(int(seed_s, 0))
        except ValueError:
            # Best-effort only; mutation will still work without an explicit seed.
            pass

    repo_root = Path(__file__).resolve().parents[2]
    vendor_dir = repo_root / "fuzzing" / "vendor"

    # Make vendored `universalmutator/` importable as `import universalmutator`.
    sys.path.insert(0, str(vendor_dir))

    from universalmutator import genmutants  # type: ignore

    genmutants.main()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
