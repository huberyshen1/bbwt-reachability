# Lean formalization

This development accompanies Theorems 3 and 4 of the [manuscript](../en/main.pdf). It uses the standard library bundled with Lean 4.19.0. The alphabet is `a < b < c`, and row and character positions are zero-based. The paper's positive parameters $e_a,e',r$ are represented by `A+1`, `E+1`, and `R+1` in the transfer proof.

## Run the proof checker

From this directory, run the following commands. Elan selects the pinned version in [lean-toolchain](lean-toolchain).

```sh
lean --version
lean -DwarningAsError=true BBWT.lean
```

The [verification log](verification.log) records the Lean version, exit status, and dependencies of the exported theorems. The source uses no `sorry`, `admit`, or custom axioms.

## Scope

| Manuscript | Lean theorem | Verified claim |
| --- | --- | --- |
| Theorem 3(c) | `maximal_singleton_transfer`, `transfer_decreases` | The two inverse-cycle decodings in the transfer and a strictly smaller rotation of the output for all positive parameters, including $r=1$. |
| Theorem 4(a) | `inverse_reflects_unique_c`, `rotate_shifts_unique_c` | Inverse reflection and the effect of rotation on the unique `c` for both relative orders of `a` and `c`. |
| Theorem 4(a) | `singleton_position_surjective`, `dihedral_position_relations` | Every position occurs. Reflection squares to the identity, left and right rotation are inverse, and reflection conjugates left rotation to right rotation. |
| Theorem 3(b3) | `b3_initial_trace`, `b3_c_trace`, `b3_nonclosing_exit_is_b`, `b3_positive_leader_is_b` | The initial cycle trace, the length of its `c` segment, both exit branches, and the leading rows of the other cycles. |
| Theorem 4(b) | `smallest_swap_merges_cycles`, `smallest_swap_splits_cycle` | The merge and split produced by swapping the outgoing edges of the first two sorted rows. |

`InverseRecipe` starts each stable LF inverse cycle at its least row and concatenates the cycles in decreasing order of their least rows. It requires the cycles to cover exactly the valid rows. The theorem `inverseRecipe_unique` proves that this relation determines at most one output for each input.

The forward statements `maximal_singleton_transfer_functions`, `maximal_singleton_descent_functions`, and `forward_reflects_unique_c` take the inverse-recipe characterization and its right-inverse law as explicit hypotheses. The equivalence with the manuscript's forward BBWT definition, full transitivity, the dihedral quotient order and wreath-product embedding, and general alphabet-merge equivariance remain to be formalized.
