# Scope and deviations

## Encoding choices

The main landscape development combines the external modes incident to a node
into a single finite index type. This is convenient for contraction and leaf
removal. `TTN/Landscape/External.lean` separately equips an architecture with
individual external legs and proves the realizability/rank characterization for
that literal formulation; it does not transport the entire landscape
development to individual-mode coordinates.

`Critical Tstar θ` is defined by `HasFDerivAt (𝕜 := ℝ) (a.loss Tstar) 0 θ`.
The theorem `critical_iff_nodewiseCritical` in
`TTN/Landscape/CriticalityBasic.lean` proves equivalence with the nodewise
residual-pairing condition used in the algebraic proofs. The line-derivative
characterization `critical_iff_hasDerivAt_line` remains available. Local and
global minimum predicates are also connected to Mathlib's standard topological
definitions.

The paper first presents TTNs as directed multilinear maps composed toward a
chosen root, and later presents the equivalent undirected contraction form.
After bases are chosen, `representedFromRoot` records the coordinate expansion
of the directed presentation. The theorem
`representedFromRoot_eq_represented` identifies it with the global bond-sum
contraction; the chosen root disappears from that expansion.

## Proof organization

The realizability converse and full-Tucker-rank theorem use leaf-removal
induction. The formal main proof needs only the leaf instance of the paper's
general environment-rank lemma and proves only that instance.

For the main minimum-norm theorem, the nonzero, rank-deficient case is first
compressed to the target cut ranks. The formal proof then selects a connected
component of deficient edges and perturbs all tensors in that component in the
dormant directions rather than following the paper's iterative stripping
narrative. The separate stripping construction is not included in this release.

The compression theorem requires a nonzero target because Lean encodes bond
dimensions as positive naturals, so the final proof handles the zero target
separately.

## Results outside the release scope

The escape-path corollary is not included in this release. Its proof requires
a path within the initial parameter's fiber to a minimum-norm representative;
the real algebraic geometry and geometric invariant theory used to establish
this property are outside the scope of the formalization.

The separate minimal two-factor factorization results are also omitted, since
neither main theorem depends on them.

The computational-hardness and Boolean-expressivity arguments are not part of
the Lean development. Neither is the parity saddle case study.
