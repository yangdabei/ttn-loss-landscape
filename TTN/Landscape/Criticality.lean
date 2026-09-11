import TTN.Landscape.FullRank

/-!
# Optimization predicates and local minima

Standard criticality and its nodewise characterization are defined and proved in
`TTN/Landscape/CriticalityBasic.lean`, before the full-rank landscape theorems.
This module connects the minimum predicates to Mathlib and proves that every
local minimum of the loss is critical.
-/

namespace TTN
namespace Arch

variable (a : Arch)

/-- The bespoke `IsGlobalMin` is Mathlib's `IsMinOn` over the whole parameter space. -/
theorem isGlobalMin_iff_isMinOn (Tstar : a.Ext → ℝ) (θ : a.Param) :
    a.IsGlobalMin Tstar θ ↔ IsMinOn (a.loss Tstar) Set.univ θ := by
  rw [isMinOn_iff]
  exact ⟨fun h θ' _ => h θ', fun h θ' => h θ' (Set.mem_univ θ')⟩

/-- **Definition 4.1**, aligned with Mathlib: `MinNorm` is `IsMinOn` of the squared parameter
norm over the fiber of the represented tensor. -/
theorem minNorm_iff_isMinOn (θ : a.Param) :
    a.MinNorm θ ↔ IsMinOn a.paramNormSq {θ' | a.represented θ' = a.represented θ} θ := by
  rw [isMinOn_iff]
  exact ⟨fun h θ' hθ' => h θ' hθ', fun h θ' hθ' => h θ' hθ'⟩


/-! ### Local minima: the parameter topology and `critical_of_isLocalMin`

The main theorem speaks of local minima of the loss; this anchors that hypothesis to
Mathlib's `IsLocalMin` in the product topology on `Param`, via the line bridge above. -/

variable {a}

/-- The parameter line `t ↦ θ + t·η` is continuous. -/
theorem continuous_paramLine (θ η : a.Param) :
    Continuous (fun t : ℝ => (fun v bi xv => θ v bi xv + t * η v bi xv : a.Param)) := by
  apply continuous_pi
  intro v
  show Continuous fun t : ℝ => (fun bi xv => θ v bi xv + t * η v bi xv : a.NodeTensor v)
  apply continuous_pi
  intro bi
  apply continuous_pi
  intro xv
  exact continuous_const.add (continuous_id.mul continuous_const)

/-- **A local minimum of the loss is a critical point** (zero Fréchet derivative). -/
theorem critical_of_isLocalMin {Tstar : a.Ext → ℝ} {θ : a.Param}
    (hloc : IsLocalMin (a.loss Tstar) θ) : a.Critical Tstar θ := by
  rw [a.critical_iff_hasDerivAt_line]
  intro η
  have hlift : IsLocalMin (a.loss Tstar)
      (fun v bi xv => θ v bi xv + (0 : ℝ) * η v bi xv) := by
    have hline0 : (fun v bi xv => θ v bi xv + (0 : ℝ) * η v bi xv : a.Param) = θ := by
      funext v bi xv; ring
    rw [hline0]
    exact hloc
  have hloc' : IsLocalMin (fun t : ℝ => a.loss Tstar
      (fun v bi xv => θ v bi xv + t * η v bi xv)) 0 :=
    IsLocalMin.comp_continuous (f := a.loss Tstar)
      (g := fun t : ℝ => (fun v bi xv => θ v bi xv + t * η v bi xv : a.Param)) (b := 0)
      hlift (continuous_paramLine θ η).continuousAt
  have hD := a.hasDerivAt_loss_line Tstar θ η
  have hzero := hloc'.hasDerivAt_eq_zero hD
  exact hzero ▸ hD


end Arch

end TTN
