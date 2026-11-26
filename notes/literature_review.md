# Literature and provenance notes for the revised BBWT manuscript

This companion note supersedes the earlier working literature review. The complete statements and proofs are in `manuscript.md` and `main.tex`; bibliographic records are maintained in `references.bib`.

## Primary reachability sources

- Golnaz Badkobeh, Hideo Bannai, and Dominik Köppl, *Bijective BWT Based Compression Schemes*, SPIRE 2024, LNCS 14899, 16–25. [Conference DOI](https://doi.org/10.1007/978-3-031-72200-4_2); [arXiv version](https://arxiv.org/abs/2406.16475).
- Golnaz Badkobeh, Hideo Bannai, Tomohiro I, and Dominik Köppl, *Bijective BWT Based Compression Schemes*, Theory of Computing Systems 70, Article 42 (2026). [Journal DOI](https://doi.org/10.1007/s00224-025-10235-w). The journal version contains the descent lemma numbered Lemma 4 and the binary/all-distinct result numbered Theorem 5. The revised bibliography uses the publisher's article-number citation; it does not rely on the earlier draft's unconfirmed issue number.
- Hideo Bannai, Dominik Köppl, and Zsuzsanna Lipták, *A Survey of the Bijective Burrows-Wheeler Transform*, OASIcs 131, 2:1–2:26 (2025). [Survey](https://doi.org/10.4230/OASIcs.Manzini.2). Section 5.5 records the reachability conjecture as Conjecture 21 and the binary/all-distinct cases as Theorem 22.

The three-author conference attribution and the four-author journal attribution should remain separate. The cited publications explicitly prove the binary and all-distinct cases and report ternary checks through length 17. Their absence of a separately stated singleton-family theorem is not evidence that all singleton families require a new argument.

## Direct consequences and additional arguments

For a nonsorted necklace, the earlier descent lemma applies when the final matching-prefix symbol differs from the last symbol. If it fails, the prefix-gathering argument in revised Theorem 1 forces that repeated symbol to be an interior alphabet letter. Thus, when every interior multiplicity equals 1, failure is impossible. Consequently,

$$
(e_1,1,\ldots,1,e_\sigma)
$$

is a direct corollary of the earlier lemma. This includes `(k,1,1)` and `(1,1,k)`. Revised Theorem 3(a) retains the proof with that attribution.

The additional descent constructions are revised Theorem 3(b), for `(1,e_b,e_c)`, and Theorem 3(c), for `(e_a,e_b,1)`. The repeated-middle-symbol cases are the parts not covered by the direct corollary. The two structural projections in Theorem 4 concern stronger information about generated permutation groups and invariant block systems.

Within the primary sources examined, no explicit proof of those additional statements was located. This is a bounded literature assessment, not a global priority certification. The revised manuscript therefore avoids claiming the first infinite families beyond the explicitly stated earlier cases.

## Algorithmic references

The revised bibliography adds formal publication records where available:

- *Constructing the Bijective and the Extended Burrows-Wheeler Transform in Linear Time*, CPM 2021, LIPIcs 191, 7:1–7:16. [Official record](https://doi.org/10.4230/LIPIcs.CPM.2021.7). The earlier preprint identifier is arXiv:1911.06985.
- *Constructing and Indexing the Bijective and Extended Burrows-Wheeler Transform*, Information and Computation 297, 105153 (2024). [Journal DOI](https://doi.org/10.1016/j.ic.2024.105153).
- *In-Place Bijective Burrows-Wheeler Transforms*, CPM 2020, LIPIcs 161, 21:1–21:15. [Official record](https://doi.org/10.4230/LIPIcs.CPM.2020.21). The correct formal DOI ends in `.21`; the arXiv related-resource link ending in `.23` points to a different paper.
- *Sensitivity of Repetitiveness Measures to String Reversal*, [arXiv:2602.14385](https://arxiv.org/abs/2602.14385).
- *Revisiting (Bijective) Burrows-Wheeler Transform Space-Time Trade-Off Constructions*, [arXiv:2611.02969](https://arxiv.org/abs/2611.02969).

## Corrections to the earlier computational discussion

The largest ternary Parikh class at length 17 has

$$
\frac{17!}{6!6!5!}=5{,}717{,}712
$$

states. The previous value 17,153,136 was incorrect. A state-count threshold of 200,000 complements the length-17 scope; it does not contain all of it.

For fixed alphabet size and fixed length, the number of positive Parikh vectors is polynomial in the length. The reachability search still visits up to a multinomial number of states per vector. Vector-count savings do not imply polynomial total running time.

The original reachability script is [reachability.py](https://github.com/koeppl/bbwtreachability/blob/master/reachability.py). It initializes a new visited set for each generated Lyndon word, permitting repeated searches of the same Parikh class. The BBWT dependency's implementation is [bwt/bbwt/bbwt.py](https://github.com/ushitora/bwt/blob/master/bwt/bbwt/bbwt.py), rather than the package initializer path given in the earlier review.

The Fine–Wilf bound on a common prefix of distinct periodic words is `p+q−gcd(p,q)−1`. This bound reaches `max(p,q)+1` when `min(p,q)−gcd(p,q)≥2`, and strictly exceeds it when the difference is at least 3. These inequalities identify a possible truncation-key collision, not a complete BBWT-output error certificate. Any claim of an implementation bug requires an actual input and differing complete outputs, with stable tie handling accounted for.

The accompanying independent Python implementation uses the exact `uv < vu` comparison. The repository also includes the earlier C++ verifier and per-vector results. Section 6 of the draft records the reproduced subset and the scope counts separately. [Code and data](../code/README.md)

## Citation presentation

The revised main file retains `plain.bst` and adds printable `note` fields for DOI URLs, article 42, and arXiv identifiers, because the style otherwise omits several electronic-metadata fields. The Markdown references are generated from the same records. The formal CPM 2021 key is now `Bannai2021LinearBBWT`; the survey and 2024 journal extension have separate keys.
