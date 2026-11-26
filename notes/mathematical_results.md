# Mathematical results and evidence in the revised BBWT manuscript

This companion note supersedes the earlier exploratory results file. The full proof text is in `manuscript.md`, synchronized from `main.tex`. Mathematical positions are one-based; implementation positions and certificate state labels are zero-based.

## Results and proof provenance

| Result in revised manuscript | Scope and status |
| --- | --- |
| Lemma 1 | Standard exact comparison of periodic words; used as a foundational tool. |
| Proposition 1 | The earlier paper's Lemma 4, with `i=lcp(x,y_min)` interpreted as a prefix length. |
| Theorem 1 | Prefix gathering as a consequence of that descent lemma. Start from the smallest rotation and stop at `y_min` before testing the lemma. |
| Corollary 1 | Ternary obstruction `a^{e_a}b^{e′}cwb^r`; `r` is the maximal trailing b-run, and `w` is empty or ends in c. |
| Theorem 2(1) | Exact sentinel-BWT embedding for a prefix-gathered word. |
| Theorem 2(2) | Exact inner-BBWT simulation by a specified composite; no full suffix-group action is asserted. |
| Theorem 2(3) | Four-run BBWT identity. |
| Theorem 3(a) | Interior-singleton family, explicitly attributed as a direct corollary of the earlier lemma. |
| Theorem 3(b)(c) | Additional constructive descent arguments for minimal- and maximal-singleton ternary families. |
| Corollary 2 | All positive ternary vectors with a singleton entry; at most two BBWT or inverse-BBWT applications per descent step. |
| Theorem 4(a)(b) | Dihedral position quotient and equivariant smallest-singleton merge. |
| Remark 1 | Finite group classification for all 113 positive ternary vectors of degree at most 500; this replaces the earlier working label Theorem 4(c). |
| Proposition 2 | Pointwise inner-rotation simulation suffices by induction; a uniform group element on the slice is not needed. |

## Proof details added in the revision

In Theorem 3(b1), maximality of the trailing run gives `m*=n−r` for the last c. The two displayed c symbols are distinct when `e′+r<e_b`, so `e_c≥2`. The prescribed inverse cycle has a prefix with one extra b, giving strict descent.

In Theorem 3(b3), put `d=r+1` and write `e_c=q d+h`, with `0≤h<d`. When `e_c≥d`, the c-block indices visited from `j_0=e′+e_c+1` decrease by d. Exactly

$$
q=\left\lfloor\frac{e_c}{r+1}\right\rfloor<e_c
$$

c symbols are read. If `h>0`, the cycle next enters the b-block. If `h=0`, it closes at the unique a; remaining c-indices cannot form a c-only cycle because each decreases, so another b-initial Lyndon factor exists. Cyclic concatenation supplies the smaller prefix.

For Theorem 3(c), the exact identity is

$$
\mathsf{BBWT}^{-1}\!\left(\rho\!\left(\mathsf{BBWT}(a^{e_a}b^{e'}cb^r)\right)\right)
=ab^{e'+1}cb^{r-1}a^{e_a-1}.
$$

At `r=1`, the descending b-index segment is empty. The final arrow closes the cycle directly at `e_a`.

Theorem 4(b) uses cycles `(1,U)` and `(2,V)`, or `(1,U,2,V)`, with U and V excluding the displayed endpoints. Swapping the two outgoing edges merges or splits the cycles. Reading each endpoint once gives the same projected word after descending Lyndon-factor concatenation. This removes the endpoint ambiguity in the exploratory proof.

The sentinel example is corrected to `BWT_$(bcbb)=bbc$b`, with suffix `w_u=bcab`; hence `BBWT(aaabcbb)=baabcab`. There are five rotations of `bcbb$`, not six.

## Executed finite checks

The independent verification program, deterministic certificate checker, and recorded JSON results are in [code/](../code/README.md).

| Check | Executed range | Result |
| --- | --- | --- |
| Both round-trip directions | 1,092 ternary and 5,460 quaternary nonempty words of length at most 6 | No failures |
| Four-run identity | 4,096 tuples with every parameter in 1 through 8 | No failures |
| Constructive branches | Length at most 15: b1 7,814; b2 78; b3 286; c 286 | All prescribed paths strictly descend |
| Two-step descent | 4,017 obstruction necklaces of length at most 13 | One step 3,247; exactly two steps 770; no failures |
| Dihedral position formula | All 3,540 states for 1≤k≤20 | No failures |
| Merge equivariance, forward and inverse | 61,718 states across alphabet sizes 3, 4, 5 with degree at most 2,000 | No failures |
| Finite group classification | All 113 positive ternary vectors of degree at most 500 | 34 symmetric; 40 alternating; 39 imprimitive |
| Jordan witnesses | All 74 primitive cases | Every recorded single-prime-cycle witness replays successfully |

The two-step tests include 2,201 singleton-boundary and 1,816 interior obstructions; the total should not be described as 4,017 unresolved interior cases.

The [proof-detail checker](../code/proof_details.py) and its [recorded results](../code/data/proof_details_results.json) cover the following cases.

- 3,800 b3 parameter instances with `1≤e′,e_c,r≤20` and `e_c≥r+1` verify the exact q formula and exit/closure condition.
- 1,000 tuples `1≤e_a,e′,r≤10` verify the exact maximal-singleton transfer identity, including `r=1`.
- 2,040 inputs with suffix length at most 8 over `{b,c}` and smallest-letter multiplicity at most 4 verify the sentinel embedding and both inner-BBWT identities.

All additional checks passed. These finite checks support the stated identities; the manuscript's general proofs remain separate arguments.

## Group certificates and distances

States are ordered lexicographically. Generator codes 0, 1, 2, 3 denote BBWT, left rotation, inverse BBWT, and right rotation, applied successively from left to right. A primitive certificate gives a generator word and a power yielding one nontrivial q-cycle, where q is prime and `q≤N−3`. Exact primitivity and generator parities complete the Jordan argument. An imprimitive certificate gives concrete invariant blocks.

For `(1,98,1)`, BFS over all 9,900 states gives forward eccentricity 102 and symmetric eccentricity 101 from the sorted word. The position quotient has eccentricity 50 in each metric. The quotient supplies a lower bound; it does not explain the full value 102. These are eccentricities from one specified state, not whole-graph diameters.

Different permutations of a Parikh vector need not give non-isomorphic generated group actions. The three permutations of `(2,2,1)` all yield the natural action of `S_30`; preserving both generator labels under a single conjugacy is a separate question.

## Counting scope and unverified claims

| Alphabet size | Ordered positive vectors, N≤200,000 | States counted | Maximum length |
| --- | --- | --- | --- |
| 3 | 2,377 | 146,010,252 | 447 |
| 4 | 1,106 | 68,419,344 | 59 |
| 5 | 612 | 44,113,680 | 22 |
| Total | 4,095 | 258,543,276 | 447 |

These are independently reproduced scope statistics. The supplied files do not contain the earlier C++ project or its per-vector logs. The claimed orbit traversal of all these states, and the C++/Python cross-validation on 391 vectors, remain unverified. The 391-vector scope count itself is confirmed. Revised Table 4 reports counts and does not infer zero counterexamples from them.

The state-count bound and the earlier length-17 bound are not nested. The balanced length-17 class `(6,6,5)` has 5,717,712 states and is outside the 200,000 threshold.

## Remaining problems

For three letters, the general unresolved regime has all multiplicities at least 2. For four or more letters, singleton cases such as `(1,2,2,2)` remain outside the families proved here.

Inner-Rotation Simulation binds a positive vector `p=(e_1,...,e_sigma)` and a suffix `u` in exactly the corresponding suffix Parikh class. Its pointwise reachability statement implies the full conjecture by induction; the converse is immediate from equal Parikh vectors.

Two-Step Ternary Lex-Descent is a separate sufficient condition for ternary reachability. A converse giving the two-step bound has not been proved, and the condition alone does not resolve larger alphabets. Finite verification through length 13 is not a proof for arbitrary length.
