import TTN.Contraction

/-!
# Trusted Comparator challenge for Theorem 4.3

This module is the trusted statement side of the Comparator certificate for
`TTN.Arch.minNorm_isLocalMin_isGlobalMin`.

Trust boundary: this challenge imports only `TTN.Contraction` (and its
transitive imports, notably `TTN.Arch` and Mathlib) for the architecture,
contraction, loss, realizability, and minimum-norm definitions. It deliberately
does not import any `TTN.Landscape` module or the production theorem under
test. The global-minimum predicate and parameter-space topology instances are
repeated below. Comparator must confirm that their elaborated definitions, as
well as the theorem type, agree with the production environment.

The single `sorry` below is the intentional challenge hole.  It is not part of
the production `TTN` library and is excluded from the repository's production
no-sorry gate.
-/

namespace TTN

namespace Arch

variable (a : Arch)

/-- The product topology on a node tensor, repeated from the production
statement-side instance in `TTN.Landscape.Criticality`. -/
noncomputable instance instTopologicalSpaceNodeTensor (v : a.V) :
    TopologicalSpace (a.NodeTensor v) := by
  unfold NodeTensor
  infer_instance

/-- The product topology on the full parameter space, repeated from the
production statement-side instance in `TTN.Landscape.Criticality`. -/
noncomputable instance instTopologicalSpaceParam : TopologicalSpace a.Param := by
  unfold Param
  infer_instance

/-- Global minimum of the squared loss, repeated from the production
statement-side definition in `TTN.Landscape.FullRank`. -/
def IsGlobalMin (Tstar : a.Ext → ℝ) (θ : a.Param) : Prop :=
  ∀ θ' : a.Param, a.loss Tstar θ ≤ a.loss Tstar θ'

/-- Theorem 4.3, with exactly the public type checked on the solution side. -/
theorem minNorm_isLocalMin_isGlobalMin {a : Arch} {Tstar : a.Ext → ℝ}
    (hreal : a.Realizable Tstar)
    {θ : a.Param} (hmn : a.MinNorm θ) (hloc : IsLocalMin (a.loss Tstar) θ) :
    a.IsGlobalMin Tstar θ ∧ a.loss Tstar θ = 0 := by
  sorry

end Arch

end TTN
