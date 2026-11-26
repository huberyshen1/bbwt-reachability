# Computational verification

## Independent Python checks

From this directory, run the certificate checker against the recorded data. It reconstructs the generators, checks the indicated block or primitivity tests, and replays 74 prime-cycle witnesses.

```sh
python3 check_certificates.py data/audit_results.json
```

To regenerate the finite search data and check the algebraic examples, run the following commands. These write new files in the working directory. The recorded reference results are under `data/`. The scripts use the standard library and were run with Python 3.14.7.

```sh
python3 audit_verify.py --out audit_results.json
python3 check_certificates.py audit_results.json
python3 proof_details.py
```

- [Group certificates and bounded search results](data/audit_results.json)
- [Proof-detail checks](data/proof_details_results.json)

## Earlier C++ search

The [C++ source](fast_search.cpp), [per-vector results](data/exhaustive_search_raw.tsv), and [summary](data/exhaustive_search_results.json) record the earlier search over 4,095 Parikh vectors of degree at most 200,000. A subsequent run reproduced all 1,035 rows of degree at most 12,000, including 73 rows of degree above 10,000. For those larger classes the fast branch computes orbit size and writes `0` in the uncomputed depth field. The remaining rows preserve the earlier run's results.

To repeat the smaller run from this directory, compile the search and write its output to a separate location.

```sh
bbwt_run_dir=$(mktemp -d)
c++ -std=c++17 -O2 -pthread fast_search.cpp -o "$bbwt_run_dir/fast_search"
"$bbwt_run_dir/fast_search" 12000 5 "$bbwt_run_dir/replay.tsv"
```
