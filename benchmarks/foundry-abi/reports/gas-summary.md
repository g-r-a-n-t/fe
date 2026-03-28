# ABI Gas Summary

Generated: 2026-03-27T22:51:40.854399+00:00

Suite summary: 339 suites, 615 passed, 0 failed, 0 skipped

Raw report: `reports/gas-report.txt`

CSV: `reports/gas-deltas.csv`

## Overall

- Bench functions compared: 111
- Mean Fe minus Solidity delta: 1594.33 gas
- Median Fe minus Solidity delta: 1419.00 gas
- Best delta: `benchEchoAddress` = -118 gas (-0.45%)
- Worst delta: `benchEchoStringU64PairArray` = 6656 gas (12.51%)

## By Category

| Category | Functions | Mean Delta | Median Delta | Best | Worst |
| --- | ---: | ---: | ---: | ---: | ---: |
| `tuple-fixed-array-dynamic` | 2 | 6322.50 | 6322.50 | 5989 | 6656 |
| `dynamic-fixed-array` | 2 | 5287.50 | 5287.50 | 4512 | 6063 |
| `tuple-dynamic` | 2 | 4822.50 | 4822.50 | 4713 | 4932 |
| `fixed-array` | 25 | 2542.20 | 2509.00 | 1734 | 3105 |
| `dynamic-string` | 1 | 2243.00 | 2243.00 | 2243 | 2243 |
| `tuple-static` | 3 | 2203.00 | 2176.00 | 2159 | 2274 |
| `nested-fixed-array` | 6 | 1833.33 | 1761.00 | 1472 | 2470 |
| `custom-signed` | 26 | 1451.54 | 1425.50 | 1148 | 1770 |
| `custom-unsigned` | 26 | 691.46 | 696.00 | 380 | 1000 |
| `tuple-fixed-array` | 4 | 663.25 | 524.50 | 63 | 1541 |
| `native-signed` | 6 | 255.50 | 252.00 | 185 | 351 |
| `native-unsigned` | 6 | 153.83 | 159.00 | 76 | 246 |
| `scalar-bool` | 1 | -10.00 | -10.00 | -10 | -10 |
| `scalar-address` | 1 | -118.00 | -118.00 | -118 | -118 |

## Notable Patterns

- Highest mean regression category: `tuple-fixed-array-dynamic` at 6322.50 gas across 2 functions.
- Lowest mean regression category: `scalar-address` at -118.00 gas across 1 functions.

## Largest Regressions

| Function | Solidity Avg | Fe Avg | Delta | Delta % |
| --- | ---: | ---: | ---: | ---: |
| `benchEchoStringU64PairArray` | 53195 | 59851 | 6656 | 12.51% |
| `benchEchoStringArray2` | 35984 | 42047 | 6063 | 16.85% |
| `benchEchoStringU64PairArray2` | 40469 | 46458 | 5989 | 14.80% |
| `benchEchoStringBoolU64Triple` | 31781 | 36713 | 4932 | 15.52% |
| `benchEchoPair` | 30558 | 35271 | 4713 | 15.42% |
| `benchEchoStringArray` | 43702 | 48214 | 4512 | 10.32% |
| `benchEchoUintArray` | 31308 | 34413 | 3105 | 9.92% |
| `benchEchoInt96Array4` | 33236 | 36273 | 3037 | 9.14% |
| `benchEchoInt248Array4` | 33012 | 36047 | 3035 | 9.19% |
| `benchEchoInt40Array4` | 33322 | 36353 | 3031 | 9.10% |
| `benchEchoInt24Array4` | 33323 | 36328 | 3005 | 9.02% |
| `benchEchoInt160Array4` | 33132 | 36098 | 2966 | 8.95% |
| `benchEchoUint248Array4` | 32527 | 35154 | 2627 | 8.08% |
| `benchEchoUint160Array4` | 32353 | 34974 | 2621 | 8.10% |
| `benchEchoUint40Array4` | 32218 | 34815 | 2597 | 8.06% |

## Largest Improvements

| Function | Solidity Avg | Fe Avg | Delta | Delta % |
| --- | ---: | ---: | ---: | ---: |
| `benchEchoAddress` | 26076 | 25958 | -118 | -0.45% |
| `benchEchoBool` | 25792 | 25782 | -10 | -0.04% |
| `benchEchoBoolAddressPairArray4` | 43300 | 43363 | 63 | 0.15% |
| `benchEchoUint8` | 25881 | 25957 | 76 | 0.29% |
| `benchEchoUint` | 25758 | 25855 | 97 | 0.38% |
| `benchEchoBoolAddressU256TripleArray4` | 47891 | 48030 | 139 | 0.29% |
| `benchEchoUint16` | 25836 | 25981 | 145 | 0.56% |
| `benchEchoUint32` | 25791 | 25964 | 173 | 0.67% |
| `benchEchoInt8` | 26237 | 26422 | 185 | 0.71% |
| `benchEchoUint64` | 25749 | 25935 | 186 | 0.72% |
| `benchEchoInt256` | 26127 | 26337 | 210 | 0.80% |
| `benchEchoUint128` | 25748 | 25994 | 246 | 0.96% |
| `benchEchoInt16` | 26198 | 26448 | 250 | 0.95% |
| `benchEchoInt32` | 26243 | 26497 | 254 | 0.97% |
| `benchEchoInt64` | 26173 | 26456 | 283 | 1.08% |
