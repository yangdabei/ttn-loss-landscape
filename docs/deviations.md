# Scope and deviations

## Encoding choices

The main landscape development combines the external modes incident to a node
into a single finite index type. This is convenient for contraction and leaf
removal. `TTN/Landscape/External.lean` separately equips an architecture with
individual external legs and proves the realizability/rank characterization for
that literal formulation; it does not transport the entire landscape
development to individual-mode coordinates.

Criticality is first expressed variationally. The theorem
`critical_iff_hasDerivAt_line` identifies it with vanishing Mathlib derivatives
along every affine parameter line. Local and global minimum predicates are also
connected to Mathlib's standard topological definitions.

## Proof organization

The realizability converse and full-Tucker-rank theorem use leaf-removal
induction. The formal main proof needs only the leaf instance of the paper's
general environment-rank lemma and proves only that instance.

For the main minimum-norm theorem, the nonzero, rank-deficient case is first
compressed to the target cut ranks. The formal proof then selects a connected
component of deficient edges and perturbs all tensors in that component in the
dormant directions rather than following the paper's iterative stripping
narrative. The stripping construction is nevertheless formalized in
`TTN/Landscape/Strip.lean`.

The compression theorem requires a nonzero target because Lean encodes bond
dimensions as positive naturals, so the final proof handles the zero target
separately.

## Explicit external hypotheses and incomplete scope

`exists_escape_path` assumes `hfiber`: every point has a path inside its fiber
to a minimum-norm representative. The present library does not formalize the
semialgebraic geometry and geometric-invariant-theory results used in the paper
to justify that property.

The per-bond conservation theorem is stated for the squared loss and an `Arch`,
which includes a tree hypothesis. It does not formalize the paper's full route
from balancedness to preservation of global minimum norm, nor the version for
an arbitrary differentiable loss of the represented tensor.

The computational-hardness and Boolean-expressivity arguments are not part of
the Lean development.
