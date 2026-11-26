# Singleton Ternary Families and Permutation Groups for BBWT Reachability

Research draft

| Manuscript | PDF | LaTeX | Markdown |
| --- | --- | --- | --- |
| English | [Read the paper](en/main.pdf) | [Source](en/main.tex) | [Read online](en/manuscript.md) |

## Results

Badkobeh, Bannai, I, and Köppl conjectured that the bijective Burrows–Wheeler transform and cyclic rotation act transitively on the words with any fixed vector of letter multiplicities. The draft proves transitivity for every positive ternary vector with a singleton entry. It separates a corollary of the earlier descent lemma from the additional minimal- and maximal-singleton descent arguments. [Original conjecture](https://doi.org/10.1007/s00224-025-10235-w)

The draft also gives a dihedral position quotient for the $(1,k,1)$ family and an equivariant projection that merges the two smallest singleton letters. The finite group classifications and bounded descent checks are recorded separately from the general reachability conjecture. [Mathematical results](notes/mathematical_results.md) · [Literature notes](notes/literature_review.md)

## Lean proofs

Lean 4.19.0 verifies the stable LF inverse-cycle computations underlying the transfer in Theorem 3(c) and the position reflection in Theorem 4(a). It also verifies the strict lexicographic descent after the transfer, the position relations, and selected cycle steps used in Theorems 3(b3) and 4(b). Connecting the inverse-cycle model to the paper's forward definition via Chen–Fox–Lyndon factorization remains a formalization task. [Proof scope and build instructions](lean/README.md) · [Lean source](lean/BBWT.lean)

## Computational verification

The bundled certificates cover all 113 positive ternary Parikh vectors of degree at most 500. The bounded descent computation checks all 4,017 obstruction necklaces of length at most 13. Replay the stored group certificates or run the other checks with Python 3 and its standard library. [Code, data and commands](code/README.md)

```sh
python3 code/check_certificates.py code/data/audit_results.json
```

## Build the manuscript

```sh
cd en
tectonic --untrusted main.tex
```

The bibliography source is [references.bib](en/references.bib). OpenAI Codex assisted with manuscript review, editing, computational verification, and Lean formalization.
