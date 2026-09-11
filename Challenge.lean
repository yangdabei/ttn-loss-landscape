import TTN.Contraction

/-!
# Trusted comparison statements

This module is the trusted statement side of the Comparator certificate. It was
written after the production proofs, so it is not an independent pre-solution
challenge. Its two theorem placeholders are intentional; the production
library never imports this module.

The challenge imports only the TTN architecture and contraction layer. It
repeats the loss-landscape definitions needed for Theorem 5.2 and Theorem 4.3.
Comparator checks those definitions and both target statements against the
production environment.
-/

open scoped Matrix MatrixOrder

namespace TTN

namespace Arch

variable (a : Arch)

/-! ## Shared loss-landscape statement definitions -/

noncomputable instance instTopologicalSpaceNodeTensor (v : a.V) :
    TopologicalSpace (a.NodeTensor v) := by
  unfold NodeTensor
  infer_instance

noncomputable instance instTopologicalSpaceParam : TopologicalSpace a.Param := by
  unfold Param
  infer_instance

noncomputable instance instNormedAddCommGroupNodeTensor (v : a.V) :
    NormedAddCommGroup (a.NodeTensor v) := by
  unfold NodeTensor
  infer_instance

noncomputable instance instNormedSpaceNodeTensor (v : a.V) :
    NormedSpace ℝ (a.NodeTensor v) :=
  inferInstanceAs (NormedSpace ℝ (a.BondIdx v → Fin (a.n v) → ℝ))

noncomputable instance instNormedAddCommGroupParam : NormedAddCommGroup a.Param := by
  unfold Param
  infer_instance

noncomputable instance instNormedSpaceParam : NormedSpace ℝ a.Param :=
  inferInstanceAs (NormedSpace ℝ ((v : a.V) → a.NodeTensor v))

noncomputable instance instIsTopologicalAddGroupParam : IsTopologicalAddGroup a.Param :=
  inferInstanceAs (IsTopologicalAddGroup ((v : a.V) → a.BondIdx v → Fin (a.n v) → ℝ))

noncomputable instance instContinuousSMulParam : ContinuousSMul ℝ a.Param :=
  inferInstanceAs (ContinuousSMul ℝ ((v : a.V) → a.BondIdx v → Fin (a.n v) → ℝ))

/-- **Critical point (Theorem 5.2).** The squared loss has zero Fréchet derivative. -/
def Critical (Tstar : a.Ext → ℝ) (θ : a.Param) : Prop :=
  HasFDerivAt (𝕜 := ℝ) (a.loss Tstar) 0 θ

noncomputable def matE (v : a.V) (e : a.Inc v) (W : a.NodeTensor v) :
    Matrix (Fin (a.r e.1)) (((e' : {e' : a.Inc v // e' ≠ e}) → Fin (a.r e'.1.1)) × Fin (a.n v)) ℝ :=
  fun k rest => W ((Equiv.piSplitAt e (fun e' => Fin (a.r e'.1))).symm (k, rest.1)) rest.2

def FullTuckerRank (θ : a.Param) : Prop :=
  ∀ (v : a.V) (e : a.Inc v), (a.matE v e (θ v)).rank = a.r e.1

def IsGlobalMin (Tstar : a.Ext → ℝ) (θ : a.Param) : Prop :=
  ∀ θ' : a.Param, a.loss Tstar θ ≤ a.loss Tstar θ'

theorem critical_fullRank_isGlobalMin {Tstar : a.Ext → ℝ} (hreal : a.Realizable Tstar)
    {θ : a.Param} (hcrit : a.Critical Tstar θ) (hftr : a.FullTuckerRank θ) :
    a.IsGlobalMin Tstar θ := by
  sorry

theorem minNorm_isLocalMin_isGlobalMin {a : Arch} {Tstar : a.Ext → ℝ}
    (hreal : a.Realizable Tstar)
    {θ : a.Param} (hmn : a.MinNorm θ) (hloc : IsLocalMin (a.loss Tstar) θ) :
    a.IsGlobalMin Tstar θ ∧ a.loss Tstar θ = 0 := by
  sorry

end Arch

end TTN
