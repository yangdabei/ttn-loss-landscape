import TTN.Matricization

/-!
# Realizability, forward direction

The paper's realizability proposition characterizes realizable targets by an edge-rank
bound: `T*` is realizable iff `rank(T*^{(e)}) ≤ r_e` for every internal edge `e`.

This module establishes the **forward direction** (realizable ⇒ rank bound), which
is the direction used by the full-rank theorem, and the small generalization
`matricizeOf` of the edge matricization to an *arbitrary* target tensor (not only a
represented one). The **converse** (rank bound ⇒ realizable, via leaf-removal induction)
and the full iff `realizable_iff_rank_le` are in `TTN/Landscape/RealizabilityConverse.lean`.
-/

open scoped Matrix

namespace TTN

namespace Arch

variable (a : Arch)

/-- Edge matricization of an **arbitrary** tensor `T : Ext → ℝ` across the cut at
`s(u, w)`. Generalizes `matricize`, which is the special case of a
represented tensor: `matricize h θ = matricizeOf h (represented θ)`. -/
noncomputable def matricizeOf {u w : a.V} (h : a.G.Adj u w) (T : a.Ext → ℝ) :
    Matrix (a.Row h) (a.Col h) ℝ :=
  fun row col => T ((a.extSplit h).symm (row, col))

@[simp] theorem matricize_eq_matricizeOf {u w : a.V} (h : a.G.Adj u w) (θ : a.Param) :
    a.matricize h θ = a.matricizeOf h (a.represented θ) := rfl

/-- **Forward direction of the realizability characterization.** A realizable target satisfies the edge-rank
bound `rank(T*^{(e)}) ≤ r_e` at every internal edge. -/
theorem realizable_imp_rank_le {Tstar : a.Ext → ℝ} (hr : a.Realizable Tstar)
    {u w : a.V} (h : a.G.Adj u w) : (a.matricizeOf h Tstar).rank ≤ a.r s(u, w) := by
  obtain ⟨θ, rfl⟩ := hr
  rw [← a.matricize_eq_matricizeOf h θ]
  exact a.matricize_rank_le h θ

/-- **The matricization rank is independent of the cut orientation**: matricizing across
`s(u, w)` from the `w`-side gives the transpose of the `u`-side matricization, up to
row/column reindexing (the two sides are complementary, `side_symm_iff_not_side`). -/
theorem rank_matricizeOf_symm {u w : a.V} (h : a.G.Adj u w) (T : a.Ext → ℝ) :
    (a.matricizeOf h.symm T).rank = (a.matricizeOf h T).rank := by
  have hss : ∀ z, a.Side h.symm z ↔ ¬ a.Side h z := a.side_symm_iff_not_side h
  let eR : {z // a.Side h.symm z} ≃ {z // ¬ a.Side h z} := Equiv.subtypeEquivRight hss
  let eC : {z // ¬ a.Side h.symm z} ≃ {z // a.Side h z} :=
    Equiv.subtypeEquivRight (fun z => (not_congr (hss z)).trans not_not)
  let e1 : a.Row h.symm ≃ a.Col h :=
    { toFun := fun R' z => R' (eR.symm z), invFun := fun C z => C (eR z)
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  let e2 : a.Col h.symm ≃ a.Row h :=
    { toFun := fun C' z => C' (eC.symm z), invFun := fun R z => R (eC z)
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hentry : a.matricizeOf h.symm T = (a.matricizeOf h T)ᵀ.submatrix e1 e2 := by
    ext R' C'
    show T ((a.extSplit h.symm).symm (R', C')) = T ((a.extSplit h).symm (e2 C', e1 R'))
    congr 1
    funext z
    by_cases hz : a.Side h z
    · have hz' : ¬ a.Side h.symm z := by rw [hss]; exact not_not.mpr hz
      rw [a.extSplit_symm_col h.symm R' C' ⟨z, hz'⟩,
        a.extSplit_symm_row h (e2 C') (e1 R') ⟨z, hz⟩]
      rfl
    · rw [a.extSplit_symm_row h.symm R' C' ⟨z, (hss z).mpr hz⟩,
        a.extSplit_symm_col h (e2 C') (e1 R') ⟨z, hz⟩]
      rfl
  rw [hentry, Matrix.rank_submatrix, Matrix.rank_transpose]

end Arch

end TTN
