import TTN.Contraction

/-!
# Standard criticality and its nodewise characterization

For the critical points in Theorem 5.2, `Critical` means that the loss has zero
Fréchet derivative. `NodewiseCritical` is the residual-pairing condition used by
the algebraic proofs. `critical_iff_nodewiseCritical` proves their equivalence.

This module depends only on the contraction layer, so the equivalence is available
before the full-rank landscape results. All derivatives use the finite product
norm on the parameter arrays, with the existing product topology.
-/

namespace TTN
namespace Arch

variable (a : Arch)

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

/-- The nodewise first-order variation of the squared loss vanishes at every node.
This is the algebraic characterization of criticality used in the proof of Theorem 5.2. -/
def NodewiseCritical (Tstar : a.Ext → ℝ) (θ : a.Param) : Prop :=
  ∀ (v : a.V) (δ : a.NodeTensor v),
    ∑ x : a.Ext, a.residual Tstar θ x * a.represented (Function.update θ v δ) x = 0

/-- The squared TTN loss is differentiable in all parameter entries. -/
theorem differentiable_loss (Tstar : a.Ext → ℝ) : Differentiable ℝ (a.loss Tstar) := by
  unfold loss represented
  change Differentiable ℝ (fun θ : (v : a.V) → a.BondIdx v → Fin (a.n v) → ℝ =>
    (1 / 2 : ℝ) * ∑ x : a.Ext,
      ((∑ b : a.Bond, ∏ v : a.V, θ v (Bond.restrict b v) (x v)) - Tstar x) ^ 2)
  fun_prop

/-- A parameter line has derivative equal to its direction. -/
theorem hasDerivAt_paramLine (θ η : a.Param) :
    HasDerivAt (fun t : ℝ => θ + t • η) η 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const η).const_add θ
  rw [one_smul] at h
  exact h

/-- Zeroing out one node tensor kills the represented tensor: `T` is linear in each `W_v`, so
the zero slice contributes a zero factor to every bond summand. -/
theorem represented_update_zero (θ : a.Param) (w : a.V) (x : a.Ext) :
    a.represented (Function.update θ w (fun _ _ => 0)) x = 0 :=
  Finset.sum_eq_zero fun _ _ =>
    Finset.prod_eq_zero (Finset.mem_univ w) (by rw [Function.update_self])

/-- **Derivative of the represented tensor along a parameter line** (multilinearity): at
`t = 0`, `t ↦ T(θ + t·η)(x)` has derivative `∑_v T(θ with W_v ← η_v)(x)`. -/
theorem hasDerivAt_represented_line (θ η : a.Param) (x : a.Ext) :
    HasDerivAt (fun t : ℝ => a.represented (fun v bi xv => θ v bi xv + t * η v bi xv) x)
      (∑ v, a.represented (Function.update θ v (η v)) x) 0 := by
  classical
  -- Each bond summand is a product over `v` of affine functions of `t`.
  have hterm : ∀ b : a.Bond, HasDerivAt
      (fun t : ℝ => ∏ v, (θ v (Bond.restrict b v) (x v) + t * η v (Bond.restrict b v) (x v)))
      (∑ v, (∏ w ∈ Finset.univ.erase v, θ w (Bond.restrict b w) (x w))
        * η v (Bond.restrict b v) (x v)) 0 := by
    intro b
    have h := HasDerivAt.fun_finsetProd (𝕜 := ℝ) (x := (0 : ℝ)) (u := Finset.univ)
      (f := fun v t => θ v (Bond.restrict b v) (x v) + t * η v (Bond.restrict b v) (x v))
      (f' := fun v => η v (Bond.restrict b v) (x v))
      (fun v _ => (hasDerivAt_mul_const _).const_add _)
    simpa using h
  have hsum := HasDerivAt.fun_sum (fun b (_ : b ∈ Finset.univ) => hterm b)
  -- Identify the derivative with the sum of single-slot substitutions.
  have hval : (∑ b : a.Bond, ∑ v, (∏ w ∈ Finset.univ.erase v, θ w (Bond.restrict b w) (x w))
        * η v (Bond.restrict b v) (x v))
      = ∑ v, a.represented (Function.update θ v (η v)) x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    show (∑ b : a.Bond, (∏ w ∈ Finset.univ.erase v, θ w (Bond.restrict b w) (x w))
          * η v (Bond.restrict b v) (x v))
        = ∑ b : a.Bond, ∏ w, Function.update θ v (η v) w (Bond.restrict b w) (x w)
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.prod_erase_mul Finset.univ
      (fun w => Function.update θ v (η v) w (Bond.restrict b w) (x w)) (Finset.mem_univ v),
      Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun w hw => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
  exact hval ▸ hsum

/-- **Derivative of the loss along a parameter line**: at `t = 0`, `t ↦ L(θ + t·η)` has
derivative `∑_v ⟨R, T(θ with W_v ← η_v)⟩` — the total first-order variation, whose summands
are exactly the pairings that `NodewiseCritical` requires to vanish. -/
theorem hasDerivAt_loss_line (Tstar : a.Ext → ℝ) (θ η : a.Param) :
    HasDerivAt (fun t : ℝ => a.loss Tstar (fun v bi xv => θ v bi xv + t * η v bi xv))
      (∑ v, ∑ x, a.residual Tstar θ x * a.represented (Function.update θ v (η v)) x) 0 := by
  classical
  have hx : ∀ x : a.Ext, HasDerivAt
      (fun t : ℝ =>
        (a.represented (fun v bi xv => θ v bi xv + t * η v bi xv) x - Tstar x) ^ 2)
      (2 * a.residual Tstar θ x * (∑ v, a.represented (Function.update θ v (η v)) x)) 0 := by
    intro x
    have h2 := ((a.hasDerivAt_represented_line θ η x).sub_const (Tstar x)).fun_pow 2
    simpa [residual] using h2
  have hsum :=
    (HasDerivAt.fun_sum (fun x (_ : x ∈ Finset.univ) => hx x)).const_mul ((1 : ℝ) / 2)
  have hval : ((1 : ℝ) / 2)
        * (∑ x, 2 * a.residual Tstar θ x
            * (∑ v, a.represented (Function.update θ v (η v)) x))
      = ∑ v, ∑ x, a.residual Tstar θ x * a.represented (Function.update θ v (η v)) x := by
    rw [Finset.mul_sum]
    rw [show (∑ x, ((1 : ℝ) / 2) * (2 * a.residual Tstar θ x
          * (∑ v, a.represented (Function.update θ v (η v)) x)))
        = ∑ x, ∑ v, a.residual Tstar θ x * a.represented (Function.update θ v (η v)) x from
      Finset.sum_congr rfl fun x _ => by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => by ring]
    exact Finset.sum_comm
  exact hval ▸ hsum

/-- The nodewise variational condition holds iff the loss has vanishing derivative — in Mathlib's
`HasDerivAt` sense — along every line `t ↦ θ + t·η` through `θ`. The loss is a polynomial
function of the parameter entries, so the right-hand side is the standard `∇L(θ) = 0`. -/
theorem nodewiseCritical_iff_hasDerivAt_line (Tstar : a.Ext → ℝ) (θ : a.Param) :
    a.NodewiseCritical Tstar θ ↔
      ∀ η : a.Param, HasDerivAt
        (fun t : ℝ => a.loss Tstar (fun v bi xv => θ v bi xv + t * η v bi xv)) 0 0 := by
  constructor
  · intro hcrit η
    have h := a.hasDerivAt_loss_line Tstar θ η
    rwa [Finset.sum_eq_zero (fun v _ => hcrit v (η v))] at h
  · intro hline v δ
    classical
    set η : a.Param := Function.update (fun (w : a.V) => (fun _ _ => 0 : a.NodeTensor w)) v δ
      with hη
    have huniq : (∑ w, ∑ x, a.residual Tstar θ x
        * a.represented (Function.update θ w (η w)) x) = 0 :=
      (a.hasDerivAt_loss_line Tstar θ η).unique (hline η)
    rw [Finset.sum_eq_single v] at huniq
    · rwa [hη, Function.update_self] at huniq
    · intro w _ hwv
      refine Finset.sum_eq_zero fun x _ => ?_
      have hηw : η w = (fun _ _ => 0 : a.NodeTensor w) := by
        rw [hη]; exact Function.update_of_ne hwv _ _
      rw [hηw, a.represented_update_zero θ w x, mul_zero]
    · exact fun hv => absurd (Finset.mem_univ v) hv

/-- Standard criticality is equivalent to zero derivative along every parameter line.
The reverse implication uses the differentiability of the loss, not merely the existence
of directional derivatives. -/
theorem critical_iff_hasDerivAt_line (Tstar : a.Ext → ℝ) (θ : a.Param) :
    a.Critical Tstar θ ↔
      ∀ η : a.Param, HasDerivAt
        (fun t : ℝ => a.loss Tstar (fun v bi xv => θ v bi xv + t * η v bi xv)) 0 0 := by
  constructor
  · intro hcrit η
    change HasFDerivAt (𝕜 := ℝ) (a.loss Tstar) 0 θ at hcrit
    have h := hcrit.comp_hasDerivAt_of_eq 0 (a.hasDerivAt_paramLine θ η) (by simp)
    exact h
  · intro hline
    have hf := (a.differentiable_loss Tstar θ).hasFDerivAt
    have hzero : fderiv ℝ (a.loss Tstar) θ = 0 := by
      ext η
      have h := hf.comp_hasDerivAt_of_eq 0 (a.hasDerivAt_paramLine θ η) (by simp)
      exact h.unique (hline η)
    rw [hzero] at hf
    exact hf

/-- **Criticality characterization (Theorem 5.2).** Zero Fréchet derivative of the loss
is equivalent to the nodewise residual-pairing condition used in the algebraic proofs. -/
theorem critical_iff_nodewiseCritical (Tstar : a.Ext → ℝ) (θ : a.Param) :
    a.Critical Tstar θ ↔ a.NodewiseCritical Tstar θ :=
  (a.critical_iff_hasDerivAt_line Tstar θ).trans
    (a.nodewiseCritical_iff_hasDerivAt_line Tstar θ).symm

end Arch
end TTN
