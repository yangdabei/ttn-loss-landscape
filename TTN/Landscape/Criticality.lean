import TTN.Landscape.FullRank

/-!
# Bridges from the bespoke optimization predicates to Mathlib's analysis vocabulary

`TTN/Landscape/FullRank.lean` states criticality variationally (`Critical`): every first-order variation
`⟨R, T(θ with W_v ← δ)⟩` vanishes. That is the form the algebraic proofs consume, but on its own
it asks the reader to trust that it *is* first-order optimality. This module discharges that
trust:

* `critical_iff_hasDerivAt_line` — `Critical Tstar θ` holds **iff** the loss has vanishing
  derivative, in Mathlib's `HasDerivAt` sense, along *every* parameter line `t ↦ θ + t·η`
  through `θ`. Since the loss is a polynomial function of the finitely many real parameters,
  this is exactly the standard "`∇L(θ) = 0`" notion of critical point.
* `isGlobalMin_iff_isMinOn`, `minNorm_iff_isMinOn`: the bespoke `IsGlobalMin` and
  `MinNorm` (Definition 4.1) are Mathlib's `IsMinOn` over the parameter space / the fiber.

The derivative computation is elementary multilinearity: `T` is degree one in each node tensor,
so along a line each bond summand is a product of affine functions of `t`
(`HasDerivAt.fun_finsetProd`), and the derivative at `t = 0` collects one `η_v`-slot per node.
-/

namespace TTN

namespace Arch

variable (a : Arch)

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
are exactly the pairings that `Critical` requires to vanish. -/
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

/-- **`Critical` is genuine first-order optimality.** `θ` is a critical point in the
variational sense of `Critical` iff the loss has vanishing derivative — in Mathlib's
`HasDerivAt` sense — along every line `t ↦ θ + t·η` through `θ`. The loss is a polynomial
function of the parameter entries, so the right-hand side is the standard `∇L(θ) = 0`. -/
theorem critical_iff_hasDerivAt_line (Tstar : a.Ext → ℝ) (θ : a.Param) :
    a.Critical Tstar θ ↔
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

variable (a : Arch)

noncomputable instance instTopologicalSpaceNodeTensor (v : a.V) :
    TopologicalSpace (a.NodeTensor v) := by
  unfold NodeTensor; infer_instance

noncomputable instance instTopologicalSpaceParam : TopologicalSpace a.Param := by
  unfold Param; infer_instance

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

/-- **A local minimum of the loss is a critical point** (variational sense). -/
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
