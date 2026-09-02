import TTN.Landscape.FullRank

/-!
# Dormant subspaces and target alignment

* `dormant`: `D_e = ker(matₑ W_u) ∩ ker(matₑ W_v)` (bond on rows in our
  `matE`, so the paper's `matₑ(W)·d` is `(matE …)ᵀ *ᵥ d`).
* `minNorm_ker_Hfun_eq_dormant` / `minNorm_ker_Ffun_eq_dormant` /
  `minNorm_rank_add_finrank_dormant`: minimum norm symmetrizes dormancy and gives the
  additive rank count.
* `minNorm_critical_ker_crossGram_le_dormant`: target alignment for any factorization
  `T*⁽ᵉ⁾ = F* H*ᵀ` (equivalent to the paper's "`M_e` injective on `A_e = D_eᗮ`").
* `minNorm_critical_rank_le_target`: model cut rank is at most target cut rank,
  without a realizability hypothesis or a chosen target factorization.
* `minNorm_critical_isUnit_crossGram`: full model cut rank makes the cross-Gram a unit.

The argument funnels through `ker_matricizeOf_mul_Hfun_eq_dormant`
(`ker (T*⁽ᵉ⁾·H_e) = D_e` at a min-norm critical point), proved gauge-free from
`critical_bond_identity` (`Fᵀ R⁽ᵉ⁾ H = 0`, obtained from `Critical` via mode-`e`
multiplications `modeMul`, the entry point of criticality into this layer).
-/

open scoped Matrix

namespace TTN

namespace Arch

variable {a : Arch}

/-! ### The cut edge as an incidence at each endpoint

Both carry the *syntactic* `Sym2` literal `s(u, w)`, so the two `matE` unfoldings share the
bond-index type `Fin (a.r s(u, w))` with no casts. -/

/-- The cut edge `s(u, w)` packaged as a bond incident to its left endpoint `u`.
Reducible so `(adjIncLeft h).1` unfolds to the syntactic `s(u, w)` during unification. -/
@[reducible] def adjIncLeft {u w : a.V} (h : a.G.Adj u w) : a.Inc u :=
  ⟨s(u, w), by rw [SimpleGraph.mem_edgeSet]; exact h, Sym2.mem_mk_left u w⟩

/-- The cut edge `s(u, w)` packaged as a bond incident to its right endpoint `w`. -/
@[reducible] def adjIncRight {u w : a.V} (h : a.G.Adj u w) : a.Inc w :=
  ⟨s(u, w), by rw [SimpleGraph.mem_edgeSet]; exact h, Sym2.mem_mk_right u w⟩

/-- The left endpoint `u` lies on the `Side` of the cut at `s(u, w)`. -/
theorem side_left {u w : a.V} (h : a.G.Adj u w) : a.Side h u :=
  SimpleGraph.Reachable.refl u

/-- The right endpoint `w` lies off the `Side` of the cut at `s(u, w)`. -/
theorem not_side_right {u w : a.V} (h : a.G.Adj u w) : ¬ a.Side h w :=
  (a.side_symm_iff_not_side h w).mp (SimpleGraph.Reachable.refl w)

/-! ### Dormant subspace -/

/-- **Dormant subspace.** For the internal edge `e = s(u, w)` (oriented by
`h : G.Adj u w`), the dormant subspace `D_e ⊆ ℝ^{r_e}` is the set of bond directions
annihilated by BOTH endpoint tensors on their `e`-mode:
`D_e = ker(matₑ W_u) ∩ ker(matₑ W_v)`. Our `matE` carries the bond on ROWS, so the paper's
`matₑ(W)·d` is `(matE …)ᵀ *ᵥ d` here. -/
noncomputable def dormant {u w : a.V} (h : a.G.Adj u w) (θ : a.Param) :
    Submodule ℝ (Fin (a.r s(u, w)) → ℝ) :=
  LinearMap.ker (a.matE u (adjIncLeft h) (θ u))ᵀ.mulVecLin ⊓
  LinearMap.ker (a.matE w (adjIncRight h) (θ w))ᵀ.mulVecLin

/-! ### Mode multiplication (the bond-space action on one node tensor)

Used for `critical_bond_identity`, for zeroing a slice with `M = projAway d`, and for
isometry embeddings and gauge transformations. -/

/-- Multiply the `e`-mode of a node tensor by the square matrix `M`: the new `e`-slice at
bond value `j` is `∑ k, M j k · (old slice at k)`. Satisfies `matE (modeMul M W) = M * matE W`. -/
noncomputable def modeMul (v : a.V) (e : a.Inc v)
    (M : Matrix (Fin (a.r e.1)) (Fin (a.r e.1)) ℝ) (W : a.NodeTensor v) : a.NodeTensor v :=
  fun bi x => ∑ k, M (bi e) k * W (Function.update bi e k) x

/-- `matE` intertwines mode multiplication with matrix multiplication. -/
theorem matE_modeMul (v : a.V) (e : a.Inc v)
    (M : Matrix (Fin (a.r e.1)) (Fin (a.r e.1)) ℝ) (W : a.NodeTensor v) :
    a.matE v e (a.modeMul v e M W) = M * a.matE v e W := by
  ext k rest
  simp only [matE, modeMul, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  rw [piSplitAt_symm_apply_self, piSplitAt_symm_update_self]

/-! ### Bond-slot bookkeeping for `bondInvFun` restrictions -/

/-- The cut-edge slot of the `u`-restriction of a split bond assignment is the cut value. -/
theorem restrict_bondInvFun_adjIncLeft {u w : a.V} (h : a.G.Adj u w)
    (k : Fin (a.r s(u, w))) (bs : a.BondSide h) (bc : a.BondCol h) :
    Bond.restrict (a.bondInvFun h (k, bs, bc)) u (adjIncLeft h) = k := by
  have hval : ∀ {x y : a.G.edgeSet} (hxy : x = y) (k' : Fin (a.r x.1)),
      ((hxy ▸ k' : Fin (a.r y.1))).val = k'.val := fun hxy k' => by cases hxy; rfl
  have hcut : (⟨(adjIncLeft h).1, (adjIncLeft h).2.1⟩ : a.G.edgeSet) = a.cutEdge h :=
    Subtype.ext rfl
  show a.bondInvFun h (k, bs, bc) ⟨(adjIncLeft h).1, (adjIncLeft h).2.1⟩ = k
  simp only [bondInvFun]
  apply Fin.ext
  exact hval hcut.symm k

/-- The cut-edge slot of the `w`-restriction of a split bond assignment is the cut value. -/
theorem restrict_bondInvFun_adjIncRight {u w : a.V} (h : a.G.Adj u w)
    (k : Fin (a.r s(u, w))) (bs : a.BondSide h) (bc : a.BondCol h) :
    Bond.restrict (a.bondInvFun h (k, bs, bc)) w (adjIncRight h) = k := by
  have hval : ∀ {x y : a.G.edgeSet} (hxy : x = y) (k' : Fin (a.r x.1)),
      ((hxy ▸ k' : Fin (a.r y.1))).val = k'.val := fun hxy k' => by cases hxy; rfl
  have hcut : (⟨(adjIncRight h).1, (adjIncRight h).2.1⟩ : a.G.edgeSet) = a.cutEdge h :=
    Subtype.ext rfl
  show a.bondInvFun h (k, bs, bc) ⟨(adjIncRight h).1, (adjIncRight h).2.1⟩ = k
  simp only [bondInvFun]
  apply Fin.ext
  exact hval hcut.symm k

/-- Changing the cut slot of the `u`-restriction is changing the cut value. -/
theorem update_restrict_bondInvFun_left {u w : a.V} (h : a.G.Adj u w)
    (k m : Fin (a.r s(u, w))) (bs : a.BondSide h) (bc : a.BondCol h) :
    Function.update (Bond.restrict (a.bondInvFun h (k, bs, bc)) u) (adjIncLeft h) m
      = Bond.restrict (a.bondInvFun h (m, bs, bc)) u := by
  funext e'
  by_cases he' : e' = adjIncLeft h
  · subst he'
    rw [Function.update_self, a.restrict_bondInvFun_adjIncLeft h m bs bc]
  · rw [Function.update_of_ne he']
    have hne : (⟨e'.1, e'.2.1⟩ : a.G.edgeSet) ≠ a.cutEdge h := fun hc => by
      have hv := congrArg Subtype.val hc
      exact he' (Subtype.ext hv)
    show a.bondInvFun h (k, bs, bc) ⟨e'.1, e'.2.1⟩ = a.bondInvFun h (m, bs, bc) ⟨e'.1, e'.2.1⟩
    simp only [bondInvFun, dif_neg hne]

/-- Changing the cut slot of the `w`-restriction is changing the cut value. -/
theorem update_restrict_bondInvFun_right {u w : a.V} (h : a.G.Adj u w)
    (k m : Fin (a.r s(u, w))) (bs : a.BondSide h) (bc : a.BondCol h) :
    Function.update (Bond.restrict (a.bondInvFun h (k, bs, bc)) w) (adjIncRight h) m
      = Bond.restrict (a.bondInvFun h (m, bs, bc)) w := by
  funext e'
  by_cases he' : e' = adjIncRight h
  · subst he'
    rw [Function.update_self, a.restrict_bondInvFun_adjIncRight h m bs bc]
  · rw [Function.update_of_ne he']
    have hne : (⟨e'.1, e'.2.1⟩ : a.G.edgeSet) ≠ a.cutEdge h := fun hc => by
      have hv := congrArg Subtype.val hc
      exact he' (Subtype.ext hv)
    show a.bondInvFun h (k, bs, bc) ⟨e'.1, e'.2.1⟩ = a.bondInvFun h (m, bs, bc) ⟨e'.1, e'.2.1⟩
    simp only [bondInvFun, dif_neg hne]

/-- Away from both endpoints, the restricted bond assignment is independent of the cut value. -/
theorem restrict_bondInvFun_k_indep {u w : a.V} (h : a.G.Adj u w) {v : a.V}
    (hvu : v ≠ u) (hvw : v ≠ w) (k m : Fin (a.r s(u, w)))
    (bs : a.BondSide h) (bc : a.BondCol h) :
    Bond.restrict (a.bondInvFun h (k, bs, bc)) v
      = Bond.restrict (a.bondInvFun h (m, bs, bc)) v := by
  funext e'
  have hne : (⟨e'.1, e'.2.1⟩ : a.G.edgeSet) ≠ a.cutEdge h := by
    intro hc
    have hvin : v ∈ e'.1 := e'.2.2
    rw [show e'.1 = s(u, w) from congrArg Subtype.val hc, Sym2.mem_iff] at hvin
    exact hvin.elim hvu hvw
  show a.bondInvFun h (k, bs, bc) ⟨e'.1, e'.2.1⟩ = a.bondInvFun h (m, bs, bc) ⟨e'.1, e'.2.1⟩
  simp only [bondInvFun, dif_neg hne]

/-- Mode-multiplying `W_u` on the cut edge post-composes `Ffun` with `Mᵀ`
(the bond index of `Ffun` is a column index, whence the transpose). -/
theorem Ffun_update_modeMul {u w : a.V} (h : a.G.Adj u w) (θ : a.Param)
    (M : Matrix (Fin (a.r s(u, w))) (Fin (a.r s(u, w))) ℝ) :
    a.Ffun h (Function.update θ u (a.modeMul u (adjIncLeft h) M (θ u)))
      = a.Ffun h θ * Mᵀ := by
  classical
  funext row k
  rw [Matrix.mul_apply]
  simp only [Ffun, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun bs _ => ?_)
  have split : ∀ (θ' : a.Param) (m : Fin (a.r s(u, w))),
      (∏ v : {x // a.Side h x},
        θ' v.1 (Bond.restrict (a.bondInvFun h (m, bs, a.colDefault h)) v.1) (row v))
      = θ' u (Bond.restrict (a.bondInvFun h (m, bs, a.colDefault h)) u) (row ⟨u, a.side_left h⟩)
        * ∏ v ∈ ({(⟨u, a.side_left h⟩ : {x // a.Side h x})}ᶜ : Finset {x // a.Side h x}),
            θ' v.1 (Bond.restrict (a.bondInvFun h (m, bs, a.colDefault h)) v.1) (row v) :=
    fun θ' m => Fintype.prod_eq_mul_prod_compl (⟨u, a.side_left h⟩ : {x // a.Side h x}) _
  rw [split (Function.update θ u (a.modeMul u (adjIncLeft h) M (θ u))) k,
    Function.update_self]
  have hrest : ∀ (m : Fin (a.r s(u, w))),
      (∏ v ∈ ({(⟨u, a.side_left h⟩ : {x // a.Side h x})}ᶜ : Finset {x // a.Side h x}),
        Function.update θ u (a.modeMul u (adjIncLeft h) M (θ u)) v.1
          (Bond.restrict (a.bondInvFun h (k, bs, a.colDefault h)) v.1) (row v))
      = ∏ v ∈ ({(⟨u, a.side_left h⟩ : {x // a.Side h x})}ᶜ : Finset {x // a.Side h x}),
          θ v.1 (Bond.restrict (a.bondInvFun h (m, bs, a.colDefault h)) v.1) (row v) := by
    intro m
    refine Finset.prod_congr rfl (fun v hv => ?_)
    have hvu : v.1 ≠ u := fun hc =>
      (Finset.mem_compl.mp hv) (Finset.mem_singleton.mpr (Subtype.ext hc))
    have hvw : v.1 ≠ w := fun hc => a.not_side_right h ((congrArg (a.Side h) hc).mp v.2)
    rw [Function.update_of_ne hvu,
      a.restrict_bondInvFun_k_indep h hvu hvw k m bs (a.colDefault h)]
  show (∑ m, M (Bond.restrict (a.bondInvFun h (k, bs, a.colDefault h)) u (adjIncLeft h)) m
        * θ u (Function.update
            (Bond.restrict (a.bondInvFun h (k, bs, a.colDefault h)) u) (adjIncLeft h) m)
            (row ⟨u, a.side_left h⟩))
      * (∏ v ∈ ({(⟨u, a.side_left h⟩ : {x // a.Side h x})}ᶜ : Finset {x // a.Side h x}),
          Function.update θ u (a.modeMul u (adjIncLeft h) M (θ u)) v.1
            (Bond.restrict (a.bondInvFun h (k, bs, a.colDefault h)) v.1) (row v))
      = _
  rw [a.restrict_bondInvFun_adjIncLeft h k bs (a.colDefault h), Finset.sum_mul]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [a.update_restrict_bondInvFun_left h k m bs (a.colDefault h), hrest m, split θ m]
  ring

/-- Mode-multiplying `W_w` on the cut edge post-composes `Hfun` with `Mᵀ`. -/
theorem Hfun_update_modeMul {u w : a.V} (h : a.G.Adj u w) (θ : a.Param)
    (M : Matrix (Fin (a.r s(u, w))) (Fin (a.r s(u, w))) ℝ) :
    a.Hfun h (Function.update θ w (a.modeMul w (adjIncRight h) M (θ w)))
      = a.Hfun h θ * Mᵀ := by
  classical
  funext col k
  rw [Matrix.mul_apply]
  simp only [Hfun, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun bc _ => ?_)
  have split : ∀ (θ' : a.Param) (m : Fin (a.r s(u, w))),
      (∏ v : {x // ¬ a.Side h x},
        θ' v.1 (Bond.restrict (a.bondInvFun h (m, a.sideDefault h, bc)) v.1) (col v))
      = θ' w (Bond.restrict (a.bondInvFun h (m, a.sideDefault h, bc)) w)
          (col ⟨w, a.not_side_right h⟩)
        * ∏ v ∈ ({(⟨w, a.not_side_right h⟩ : {x // ¬ a.Side h x})}ᶜ :
            Finset {x // ¬ a.Side h x}),
            θ' v.1 (Bond.restrict (a.bondInvFun h (m, a.sideDefault h, bc)) v.1) (col v) :=
    fun θ' m => Fintype.prod_eq_mul_prod_compl (⟨w, a.not_side_right h⟩ : {x // ¬ a.Side h x}) _
  rw [split (Function.update θ w (a.modeMul w (adjIncRight h) M (θ w))) k,
    Function.update_self]
  have hrest : ∀ (m : Fin (a.r s(u, w))),
      (∏ v ∈ ({(⟨w, a.not_side_right h⟩ : {x // ¬ a.Side h x})}ᶜ :
          Finset {x // ¬ a.Side h x}),
        Function.update θ w (a.modeMul w (adjIncRight h) M (θ w)) v.1
          (Bond.restrict (a.bondInvFun h (k, a.sideDefault h, bc)) v.1) (col v))
      = ∏ v ∈ ({(⟨w, a.not_side_right h⟩ : {x // ¬ a.Side h x})}ᶜ :
          Finset {x // ¬ a.Side h x}),
          θ v.1 (Bond.restrict (a.bondInvFun h (m, a.sideDefault h, bc)) v.1) (col v) := by
    intro m
    refine Finset.prod_congr rfl (fun v hv => ?_)
    have hvw : v.1 ≠ w := fun hc =>
      (Finset.mem_compl.mp hv) (Finset.mem_singleton.mpr (Subtype.ext hc))
    have hvu : v.1 ≠ u := fun hc => v.2 (by rw [hc]; exact a.side_left h)
    rw [Function.update_of_ne hvw,
      a.restrict_bondInvFun_k_indep h hvu hvw k m (a.sideDefault h) bc]
  show (∑ m, M (Bond.restrict (a.bondInvFun h (k, a.sideDefault h, bc)) w (adjIncRight h)) m
        * θ w (Function.update
            (Bond.restrict (a.bondInvFun h (k, a.sideDefault h, bc)) w) (adjIncRight h) m)
            (col ⟨w, a.not_side_right h⟩))
      * (∏ v ∈ ({(⟨w, a.not_side_right h⟩ : {x // ¬ a.Side h x})}ᶜ :
          Finset {x // ¬ a.Side h x}),
          Function.update θ w (a.modeMul w (adjIncRight h) M (θ w)) v.1
            (Bond.restrict (a.bondInvFun h (k, a.sideDefault h, bc)) v.1) (col v))
      = _
  rw [a.restrict_bondInvFun_adjIncRight h k (a.sideDefault h) bc, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [a.update_restrict_bondInvFun_right h k m (a.sideDefault h) bc, hrest m, split θ m]
  ring

/-- `Ffun` depends only on the `Side` node tensors (mirror of `Hfun_update_side`). -/
theorem Ffun_update_col {x y : a.V} (h : a.G.Adj x y) (θ : a.Param)
    {z : a.V} (hz : ¬ a.Side h z) (δ : a.NodeTensor z) :
    a.Ffun h (Function.update θ z δ) = a.Ffun h θ := by
  funext row k
  simp only [Ffun]
  refine Finset.sum_congr rfl (fun bs _ => Finset.prod_congr rfl (fun v _ => ?_))
  have hvz : v.1 ≠ z := fun hc => hz (hc ▸ v.2)
  rw [Function.update_of_ne hvz]

/-- The represented tensor is determined by any single edge matricization (the reshape
`extSplit` is an equivalence). -/
theorem represented_eq_of_matricize_eq {u w : a.V} (h : a.G.Adj u w) {θ θ' : a.Param}
    (heq : a.matricize h θ = a.matricize h θ') : a.represented θ = a.represented θ' := by
  funext x
  have h1 : a.represented θ x = a.matricize h θ (a.extSplit h x).1 (a.extSplit h x).2 := by
    show _ = a.represented θ ((a.extSplit h).symm ((a.extSplit h x).1, (a.extSplit h x).2))
    rw [Prod.mk.eta, Equiv.symm_apply_apply]
  have h2 : a.represented θ' x = a.matricize h θ' (a.extSplit h x).1 (a.extSplit h x).2 := by
    show _ = a.represented θ' ((a.extSplit h).symm ((a.extSplit h x).1, (a.extSplit h x).2))
    rw [Prod.mk.eta, Equiv.symm_apply_apply]
  rw [h1, h2, heq]

/-- The squared node norm is the Frobenius square of any mode unfolding (`matE` is a reshape). -/
theorem nodeNormSq_eq_matE (v : a.V) (e : a.Inc v) (θ : a.Param) :
    a.nodeNormSq θ v = ∑ k, ∑ c, (a.matE v e (θ v) k c) ^ 2 := by
  have hL : a.nodeNormSq θ v
      = ∑ p : Fin (a.r e.1) × ((e' : {e' : a.Inc v // e' ≠ e}) → Fin (a.r e'.1.1)),
          ∑ x : Fin (a.n v),
            (θ v ((Equiv.piSplitAt e (fun e' => Fin (a.r e'.1))).symm p) x) ^ 2 := by
    show (∑ bi : a.BondIdx v, ∑ x : Fin (a.n v), (θ v bi x) ^ 2) = _
    exact (Equiv.sum_comp (Equiv.piSplitAt e (fun e' => Fin (a.r e'.1))).symm
      (fun bi => ∑ x : Fin (a.n v), (θ v bi x) ^ 2)).symm
  rw [hL, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Fintype.sum_prod_type]
  rfl

/-! ### The factoring inclusions (`D_e ⊆ ker F_e`, `D_e ⊆ ker H_e` directions) -/

/-- The `u`-side cut factor annihilates any bond direction killed by `W_u`'s `e`-mode
(`F_e` factors through `matₑ W_u`; the cut bond enters the `Side` contraction only via `W_u`). -/
theorem Ffun_mulVec_eq_zero {u w : a.V} (h : a.G.Adj u w) (θ : a.Param)
    {d : Fin (a.r s(u, w)) → ℝ} (hd : (a.matE u (adjIncLeft h) (θ u))ᵀ *ᵥ d = 0) :
    a.Ffun h θ *ᵥ d = 0 := by
  classical
  have hr0 : 0 < a.r s(u, w) := a.hr s(u, w) (by rw [SimpleGraph.mem_edgeSet]; exact h)
  funext row
  show (∑ k, a.Ffun h θ row k * d k) = 0
  simp only [Ffun, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun bs _ => ?_)
  set k₀ : Fin (a.r s(u, w)) := ⟨0, hr0⟩ with hk₀
  have split : ∀ (m : Fin (a.r s(u, w))),
      (∏ v : {x // a.Side h x},
        θ v.1 (Bond.restrict (a.bondInvFun h (m, bs, a.colDefault h)) v.1) (row v))
      = θ u (Bond.restrict (a.bondInvFun h (m, bs, a.colDefault h)) u) (row ⟨u, a.side_left h⟩)
        * ∏ v ∈ ({(⟨u, a.side_left h⟩ : {x // a.Side h x})}ᶜ : Finset {x // a.Side h x}),
            θ v.1 (Bond.restrict (a.bondInvFun h (m, bs, a.colDefault h)) v.1) (row v) :=
    fun m => Fintype.prod_eq_mul_prod_compl (⟨u, a.side_left h⟩ : {x // a.Side h x}) _
  have hrest : ∀ (m : Fin (a.r s(u, w))),
      (∏ v ∈ ({(⟨u, a.side_left h⟩ : {x // a.Side h x})}ᶜ : Finset {x // a.Side h x}),
        θ v.1 (Bond.restrict (a.bondInvFun h (m, bs, a.colDefault h)) v.1) (row v))
      = ∏ v ∈ ({(⟨u, a.side_left h⟩ : {x // a.Side h x})}ᶜ : Finset {x // a.Side h x}),
          θ v.1 (Bond.restrict (a.bondInvFun h (k₀, bs, a.colDefault h)) v.1) (row v) := by
    intro m
    refine Finset.prod_congr rfl (fun v hv => ?_)
    have hvu : v.1 ≠ u := fun hc =>
      (Finset.mem_compl.mp hv) (Finset.mem_singleton.mpr (Subtype.ext hc))
    have hvw : v.1 ≠ w := fun hc => a.not_side_right h ((congrArg (a.Side h) hc).mp v.2)
    rw [a.restrict_bondInvFun_k_indep h hvu hvw m k₀ bs (a.colDefault h)]
  have hsplitAt : ∀ (m : Fin (a.r s(u, w))),
      Bond.restrict (a.bondInvFun h (m, bs, a.colDefault h)) u
        = (Equiv.piSplitAt (adjIncLeft h) (fun e' => Fin (a.r e'.1))).symm
            (m, fun e' => Bond.restrict (a.bondInvFun h (k₀, bs, a.colDefault h)) u e'.1) := by
    intro m
    funext e'
    by_cases he' : e' = adjIncLeft h
    · subst he'
      rw [piSplitAt_symm_apply_self, a.restrict_bondInvFun_adjIncLeft h m bs (a.colDefault h)]
    · rw [Equiv.piSplitAt_symm_apply, dif_neg he',
        ← a.update_restrict_bondInvFun_left h k₀ m bs (a.colDefault h),
        Function.update_of_ne he']
  have hker : (∑ m, θ u (Bond.restrict (a.bondInvFun h (m, bs, a.colDefault h)) u)
        (row ⟨u, a.side_left h⟩) * d m) = 0 := by
    have h0 := congrFun hd
      ((fun e' => Bond.restrict (a.bondInvFun h (k₀, bs, a.colDefault h)) u e'.1,
        row ⟨u, a.side_left h⟩))
    rw [Pi.zero_apply] at h0
    calc (∑ m, θ u (Bond.restrict (a.bondInvFun h (m, bs, a.colDefault h)) u)
          (row ⟨u, a.side_left h⟩) * d m)
        = ∑ m, a.matE u (adjIncLeft h) (θ u) m
            (fun e' => Bond.restrict (a.bondInvFun h (k₀, bs, a.colDefault h)) u e'.1,
             row ⟨u, a.side_left h⟩) * d m := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [hsplitAt m]
          rfl
      _ = 0 := h0
  calc (∑ m, (∏ v : {x // a.Side h x},
        θ v.1 (Bond.restrict (a.bondInvFun h (m, bs, a.colDefault h)) v.1) (row v)) * d m)
      = ∑ m, (θ u (Bond.restrict (a.bondInvFun h (m, bs, a.colDefault h)) u)
            (row ⟨u, a.side_left h⟩) * d m)
          * ∏ v ∈ ({(⟨u, a.side_left h⟩ : {x // a.Side h x})}ᶜ : Finset {x // a.Side h x}),
              θ v.1 (Bond.restrict (a.bondInvFun h (k₀, bs, a.colDefault h)) v.1) (row v) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [split m, hrest m]
        ring
    _ = (∑ m, θ u (Bond.restrict (a.bondInvFun h (m, bs, a.colDefault h)) u)
            (row ⟨u, a.side_left h⟩) * d m)
          * ∏ v ∈ ({(⟨u, a.side_left h⟩ : {x // a.Side h x})}ᶜ : Finset {x // a.Side h x}),
              θ v.1 (Bond.restrict (a.bondInvFun h (k₀, bs, a.colDefault h)) v.1) (row v) :=
        (Finset.sum_mul _ _ _).symm
    _ = 0 := by rw [hker, zero_mul]

/-- The `w`-side cut factor annihilates any bond direction killed by `W_w`'s `e`-mode. -/
theorem Hfun_mulVec_eq_zero {u w : a.V} (h : a.G.Adj u w) (θ : a.Param)
    {d : Fin (a.r s(u, w)) → ℝ} (hd : (a.matE w (adjIncRight h) (θ w))ᵀ *ᵥ d = 0) :
    a.Hfun h θ *ᵥ d = 0 := by
  classical
  have hr0 : 0 < a.r s(u, w) := a.hr s(u, w) (by rw [SimpleGraph.mem_edgeSet]; exact h)
  funext col
  show (∑ k, a.Hfun h θ col k * d k) = 0
  simp only [Hfun, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun bc _ => ?_)
  set k₀ : Fin (a.r s(u, w)) := ⟨0, hr0⟩ with hk₀
  have split : ∀ (m : Fin (a.r s(u, w))),
      (∏ v : {x // ¬ a.Side h x},
        θ v.1 (Bond.restrict (a.bondInvFun h (m, a.sideDefault h, bc)) v.1) (col v))
      = θ w (Bond.restrict (a.bondInvFun h (m, a.sideDefault h, bc)) w)
          (col ⟨w, a.not_side_right h⟩)
        * ∏ v ∈ ({(⟨w, a.not_side_right h⟩ : {x // ¬ a.Side h x})}ᶜ :
            Finset {x // ¬ a.Side h x}),
            θ v.1 (Bond.restrict (a.bondInvFun h (m, a.sideDefault h, bc)) v.1) (col v) :=
    fun m => Fintype.prod_eq_mul_prod_compl (⟨w, a.not_side_right h⟩ : {x // ¬ a.Side h x}) _
  have hrest : ∀ (m : Fin (a.r s(u, w))),
      (∏ v ∈ ({(⟨w, a.not_side_right h⟩ : {x // ¬ a.Side h x})}ᶜ :
          Finset {x // ¬ a.Side h x}),
        θ v.1 (Bond.restrict (a.bondInvFun h (m, a.sideDefault h, bc)) v.1) (col v))
      = ∏ v ∈ ({(⟨w, a.not_side_right h⟩ : {x // ¬ a.Side h x})}ᶜ :
          Finset {x // ¬ a.Side h x}),
          θ v.1 (Bond.restrict (a.bondInvFun h (k₀, a.sideDefault h, bc)) v.1) (col v) := by
    intro m
    refine Finset.prod_congr rfl (fun v hv => ?_)
    have hvw : v.1 ≠ w := fun hc =>
      (Finset.mem_compl.mp hv) (Finset.mem_singleton.mpr (Subtype.ext hc))
    have hvu : v.1 ≠ u := fun hc => v.2 (by rw [hc]; exact a.side_left h)
    rw [a.restrict_bondInvFun_k_indep h hvu hvw m k₀ (a.sideDefault h) bc]
  have hsplitAt : ∀ (m : Fin (a.r s(u, w))),
      Bond.restrict (a.bondInvFun h (m, a.sideDefault h, bc)) w
        = (Equiv.piSplitAt (adjIncRight h) (fun e' => Fin (a.r e'.1))).symm
            (m, fun e' => Bond.restrict (a.bondInvFun h (k₀, a.sideDefault h, bc)) w e'.1) := by
    intro m
    funext e'
    by_cases he' : e' = adjIncRight h
    · subst he'
      rw [piSplitAt_symm_apply_self,
        a.restrict_bondInvFun_adjIncRight h m (a.sideDefault h) bc]
    · rw [Equiv.piSplitAt_symm_apply, dif_neg he',
        ← a.update_restrict_bondInvFun_right h k₀ m (a.sideDefault h) bc,
        Function.update_of_ne he']
  have hker : (∑ m, θ w (Bond.restrict (a.bondInvFun h (m, a.sideDefault h, bc)) w)
        (col ⟨w, a.not_side_right h⟩) * d m) = 0 := by
    have h0 := congrFun hd
      ((fun e' => Bond.restrict (a.bondInvFun h (k₀, a.sideDefault h, bc)) w e'.1,
        col ⟨w, a.not_side_right h⟩))
    rw [Pi.zero_apply] at h0
    calc (∑ m, θ w (Bond.restrict (a.bondInvFun h (m, a.sideDefault h, bc)) w)
          (col ⟨w, a.not_side_right h⟩) * d m)
        = ∑ m, a.matE w (adjIncRight h) (θ w) m
            (fun e' => Bond.restrict (a.bondInvFun h (k₀, a.sideDefault h, bc)) w e'.1,
             col ⟨w, a.not_side_right h⟩) * d m := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [hsplitAt m]
          rfl
      _ = 0 := h0
  calc (∑ m, (∏ v : {x // ¬ a.Side h x},
        θ v.1 (Bond.restrict (a.bondInvFun h (m, a.sideDefault h, bc)) v.1) (col v)) * d m)
      = ∑ m, (θ w (Bond.restrict (a.bondInvFun h (m, a.sideDefault h, bc)) w)
            (col ⟨w, a.not_side_right h⟩) * d m)
          * ∏ v ∈ ({(⟨w, a.not_side_right h⟩ : {x // ¬ a.Side h x})}ᶜ :
              Finset {x // ¬ a.Side h x}),
              θ v.1 (Bond.restrict (a.bondInvFun h (k₀, a.sideDefault h, bc)) v.1) (col v) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [split m, hrest m]
        ring
    _ = (∑ m, θ w (Bond.restrict (a.bondInvFun h (m, a.sideDefault h, bc)) w)
            (col ⟨w, a.not_side_right h⟩) * d m)
          * ∏ v ∈ ({(⟨w, a.not_side_right h⟩ : {x // ¬ a.Side h x})}ᶜ :
              Finset {x // ¬ a.Side h x}),
              θ v.1 (Bond.restrict (a.bondInvFun h (k₀, a.sideDefault h, bc)) v.1) (col v) :=
        (Finset.sum_mul _ _ _).symm
    _ = 0 := by rw [hker, zero_mul]

/-! ### The zero-the-slice argument -/

/-- Orthogonal projection away from a single direction `d`, as an explicit matrix
(`1 − ddᵀ/‖d‖²`; the identity when `d = 0` since `(0)⁻¹ = 0` in `ℝ`). -/
noncomputable def projAway {r : ℕ} (d : Fin r → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  1 - (d ⬝ᵥ d)⁻¹ • Matrix.vecMulVec d d

/-- A nonzero real vector has positive self-dot-product. -/
theorem dotProduct_self_pos {r : ℕ} {d : Fin r → ℝ} (hd : d ≠ 0) : 0 < d ⬝ᵥ d :=
  lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (d i))
    (fun hc => hd (dotProduct_self_eq_zero.mp hc.symm))

/-- `projAway d` is symmetric. -/
theorem projAway_transpose {r : ℕ} (d : Fin r → ℝ) : (projAway d)ᵀ = projAway d := by
  ext i j
  simp only [Matrix.transpose_apply, projAway, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; rfl
  · rw [if_neg hij, if_neg (Ne.symm hij)]
    ring

/-- `projAway d` acts as the identity on `Hᵀ` when `H` kills `d`. -/
theorem projAway_mul_transpose_eq {r : ℕ} {C : Type*} [Fintype C] (d : Fin r → ℝ)
    (H : Matrix C (Fin r) ℝ) (hd : H *ᵥ d = 0) : projAway d * Hᵀ = Hᵀ := by
  rw [projAway, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  suffices hz : Matrix.vecMulVec d d * Hᵀ = 0 by rw [hz, smul_zero, sub_zero]
  ext k c
  rw [Matrix.mul_apply, Matrix.zero_apply]
  calc ∑ j, Matrix.vecMulVec d d k j * Hᵀ j c
      = d k * ∑ j, H c j * d j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by
          rw [Matrix.vecMulVec_apply, Matrix.transpose_apply]; ring
    _ = d k * (H *ᵥ d) c := rfl
    _ = 0 := by rw [hd, Pi.zero_apply, mul_zero]

/-- `projAway d` acts as the identity on `F` (from the right) when `F` kills `d`. -/
theorem mul_projAway_eq {r : ℕ} {R : Type*} [Fintype R] (d : Fin r → ℝ)
    (F : Matrix R (Fin r) ℝ) (hd : F *ᵥ d = 0) : F * projAway d = F := by
  rw [projAway, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  suffices hz : F * Matrix.vecMulVec d d = 0 by rw [hz, smul_zero, sub_zero]
  ext i c
  rw [Matrix.mul_apply, Matrix.zero_apply]
  calc ∑ j, F i j * Matrix.vecMulVec d d j c
      = (∑ j, F i j * d j) * d c := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by
          rw [Matrix.vecMulVec_apply]; ring
    _ = (F *ᵥ d) i * d c := rfl
    _ = 0 := by rw [hd, Pi.zero_apply, zero_mul]

/-- **Frobenius cost of the rank-one withdrawal**: for `d ≠ 0`,
`‖projAway d · A‖²_F = ‖A‖²_F − (d⬝ᵥd)⁻¹ · ‖Aᵀ *ᵥ d‖²`. -/
theorem sum_sq_projAway_mul {r : ℕ} {C : Type*} [Fintype C] {d : Fin r → ℝ} (hd : d ≠ 0)
    (A : Matrix (Fin r) C ℝ) :
    (∑ k, ∑ c, ((projAway d * A) k c) ^ 2)
      = (∑ k, ∑ c, (A k c) ^ 2) - (d ⬝ᵥ d)⁻¹ * ∑ c, ((Aᵀ *ᵥ d) c) ^ 2 := by
  classical
  set t : ℝ := (d ⬝ᵥ d)⁻¹ with ht
  have hddne : d ⬝ᵥ d ≠ 0 := (dotProduct_self_pos hd).ne'
  have htdd : t * (d ⬝ᵥ d) = 1 := inv_mul_cancel₀ hddne
  have hvv : ∀ k c, (Matrix.vecMulVec d d * A) k c = d k * (Aᵀ *ᵥ d) c := by
    intro k c
    rw [Matrix.mul_apply]
    calc ∑ j, Matrix.vecMulVec d d k j * A j c
        = d k * ∑ j, A j c * d j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [Matrix.vecMulVec_apply]; ring
      _ = d k * (Aᵀ *ᵥ d) c := rfl
  have hentry : ∀ k c, (projAway d * A) k c = A k c - t * (d k * (Aᵀ *ᵥ d) c) := by
    intro k c
    rw [show projAway d * A = A - t • (Matrix.vecMulVec d d * A) from by
        rw [projAway, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul],
      Matrix.sub_apply, Matrix.smul_apply, hvv, smul_eq_mul]
  rw [show (∑ k, ∑ c, ((projAway d * A) k c) ^ 2) = ∑ c, ∑ k, ((projAway d * A) k c) ^ 2
      from Finset.sum_comm,
    show (∑ k, ∑ c, (A k c) ^ 2) = ∑ c, ∑ k, (A k c) ^ 2 from Finset.sum_comm]
  have hcol : ∀ c, (∑ k, ((projAway d * A) k c) ^ 2)
      = (∑ k, (A k c) ^ 2) - t * ((Aᵀ *ᵥ d) c) ^ 2 := by
    intro c
    set g : ℝ := (Aᵀ *ᵥ d) c with hg
    have hgsum : (∑ k, d k * A k c) = g := by
      rw [hg]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    calc (∑ k, ((projAway d * A) k c) ^ 2)
        = ∑ k, ((A k c) ^ 2
            - (2 * (t * g) * (d k * A k c) - (t * g) ^ 2 * (d k * d k))) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hentry k c, ← hg]
          ring
      _ = (∑ k, (A k c) ^ 2)
          - (2 * (t * g) * (∑ k, d k * A k c) - (t * g) ^ 2 * ∑ k, d k * d k) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = (∑ k, (A k c) ^ 2) - (2 * (t * g) * g - (t * g) ^ 2 * (d ⬝ᵥ d)) := by
          rw [hgsum]
          rfl
      _ = (∑ k, (A k c) ^ 2) - t * g ^ 2 := by
          have h1 : (t * g) ^ 2 * (d ⬝ᵥ d) = (t * (d ⬝ᵥ d)) * (t * g ^ 2) := by ring
          rw [h1, htdd, one_mul]
          ring_nf
  rw [Finset.sum_congr rfl (fun c _ => hcol c), Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- **Minimum norm kills slices the far side annihilates** (`ker H_e ⊆ ker matₑ W_u`).
If `d ∈ ker H_e`, projecting `W_u`'s `e`-mode away from `d` preserves the represented tensor
(`F (projAway d)ᵀ Hᵀ = F Hᵀ` since `H d = 0`) while strictly reducing `‖W_u‖²` unless the
`d`-slice already vanishes; min-norm forces the latter. -/
theorem minNorm_matE_u_ker {u w : a.V} (h : a.G.Adj u w) {θ : a.Param} (hmn : a.MinNorm θ)
    {d : Fin (a.r s(u, w)) → ℝ} (hd : a.Hfun h θ *ᵥ d = 0) :
    (a.matE u (adjIncLeft h) (θ u))ᵀ *ᵥ d = 0 := by
  classical
  by_cases hd0 : d = 0
  · subst hd0; rw [Matrix.mulVec_zero]
  set θ' := Function.update θ u (a.modeMul u (adjIncLeft h) (projAway d) (θ u)) with hθ'
  -- (1) the withdrawal preserves the represented tensor
  have hrep : a.represented θ' = a.represented θ := by
    refine a.represented_eq_of_matricize_eq h ?_
    rw [a.matricize_FH h θ', a.matricize_FH h θ, hθ',
      a.Ffun_update_modeMul h θ (projAway d),
      a.Hfun_update_side h θ (a.side_left h), projAway_transpose, Matrix.mul_assoc,
      projAway_mul_transpose_eq d (a.Hfun h θ) hd]
  -- (2) min-norm localizes at `u`
  have hnorm : a.nodeNormSq θ u ≤ a.nodeNormSq θ' u := by
    have hp := hmn θ' hrep
    have hsplitP : ∀ ρ : a.Param, a.paramNormSq ρ
        = a.nodeNormSq ρ u + ∑ v ∈ Finset.univ.erase u, a.nodeNormSq ρ v := by
      intro ρ
      show (∑ v, a.nodeNormSq ρ v) = _
      exact (Finset.add_sum_erase _ _ (Finset.mem_univ u)).symm
    have hoff : (∑ v ∈ Finset.univ.erase u, a.nodeNormSq θ' v)
        = ∑ v ∈ Finset.univ.erase u, a.nodeNormSq θ v := by
      refine Finset.sum_congr rfl (fun v hv => ?_)
      have hvu : v ≠ u := Finset.ne_of_mem_erase hv
      show (∑ bi, ∑ x, (θ' v bi x) ^ 2) = ∑ bi, ∑ x, (θ v bi x) ^ 2
      rw [hθ', Function.update_of_ne hvu]
    rw [hsplitP θ, hsplitP θ', hoff] at hp
    linarith
  -- (3) the withdrawn node norm in matricized form
  have hmatE' : a.matE u (adjIncLeft h) (θ' u)
      = projAway d * a.matE u (adjIncLeft h) (θ u) := by
    rw [hθ', Function.update_self, a.matE_modeMul u (adjIncLeft h) (projAway d) (θ u)]
  have hnorm' : a.nodeNormSq θ' u = a.nodeNormSq θ u
      - (d ⬝ᵥ d)⁻¹ * ∑ c, (((a.matE u (adjIncLeft h) (θ u))ᵀ *ᵥ d) c) ^ 2 := by
    rw [a.nodeNormSq_eq_matE u (adjIncLeft h) θ', hmatE',
      sum_sq_projAway_mul hd0 (a.matE u (adjIncLeft h) (θ u)),
      ← a.nodeNormSq_eq_matE u (adjIncLeft h) θ]
  -- (4) conclude: the withdrawn mass is zero
  have hddpos : (0 : ℝ) < d ⬝ᵥ d := dotProduct_self_pos hd0
  have hsum0 : (∑ c, (((a.matE u (adjIncLeft h) (θ u))ᵀ *ᵥ d) c) ^ 2) = 0 := by
    have hnn : (0 : ℝ) ≤ ∑ c, (((a.matE u (adjIncLeft h) (θ u))ᵀ *ᵥ d) c) ^ 2 :=
      Finset.sum_nonneg fun c _ => sq_nonneg _
    have hle : (d ⬝ᵥ d)⁻¹ * ∑ c, (((a.matE u (adjIncLeft h) (θ u))ᵀ *ᵥ d) c) ^ 2 ≤ 0 := by
      rw [hnorm'] at hnorm; linarith
    nlinarith [inv_pos.mpr hddpos]
  funext c
  have hc := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => sq_nonneg _)).mp hsum0 c
    (Finset.mem_univ c)
  exact sq_eq_zero_iff.mp hc

/-- Symmetric zero-the-slice at the `w` endpoint (`ker F_e ⊆ ker matₑ W_w`). -/
theorem minNorm_matE_w_ker {u w : a.V} (h : a.G.Adj u w) {θ : a.Param} (hmn : a.MinNorm θ)
    {d : Fin (a.r s(u, w)) → ℝ} (hd : a.Ffun h θ *ᵥ d = 0) :
    (a.matE w (adjIncRight h) (θ w))ᵀ *ᵥ d = 0 := by
  classical
  by_cases hd0 : d = 0
  · subst hd0; rw [Matrix.mulVec_zero]
  set θ' := Function.update θ w (a.modeMul w (adjIncRight h) (projAway d) (θ w)) with hθ'
  -- (1) the withdrawal preserves the represented tensor
  have hrep : a.represented θ' = a.represented θ := by
    refine a.represented_eq_of_matricize_eq h ?_
    rw [a.matricize_FH h θ', a.matricize_FH h θ, hθ',
      a.Hfun_update_modeMul h θ (projAway d),
      a.Ffun_update_col h θ (a.not_side_right h), Matrix.transpose_mul,
      Matrix.transpose_transpose, ← Matrix.mul_assoc,
      mul_projAway_eq d (a.Ffun h θ) hd]
  -- (2) min-norm localizes at `w`
  have hnorm : a.nodeNormSq θ w ≤ a.nodeNormSq θ' w := by
    have hp := hmn θ' hrep
    have hsplitP : ∀ ρ : a.Param, a.paramNormSq ρ
        = a.nodeNormSq ρ w + ∑ v ∈ Finset.univ.erase w, a.nodeNormSq ρ v := by
      intro ρ
      show (∑ v, a.nodeNormSq ρ v) = _
      exact (Finset.add_sum_erase _ _ (Finset.mem_univ w)).symm
    have hoff : (∑ v ∈ Finset.univ.erase w, a.nodeNormSq θ' v)
        = ∑ v ∈ Finset.univ.erase w, a.nodeNormSq θ v := by
      refine Finset.sum_congr rfl (fun v hv => ?_)
      have hvw : v ≠ w := Finset.ne_of_mem_erase hv
      show (∑ bi, ∑ x, (θ' v bi x) ^ 2) = ∑ bi, ∑ x, (θ v bi x) ^ 2
      rw [hθ', Function.update_of_ne hvw]
    rw [hsplitP θ, hsplitP θ', hoff] at hp
    linarith
  -- (3) the withdrawn node norm in matricized form
  have hmatE' : a.matE w (adjIncRight h) (θ' w)
      = projAway d * a.matE w (adjIncRight h) (θ w) := by
    rw [hθ', Function.update_self, a.matE_modeMul w (adjIncRight h) (projAway d) (θ w)]
  have hnorm' : a.nodeNormSq θ' w = a.nodeNormSq θ w
      - (d ⬝ᵥ d)⁻¹ * ∑ c, (((a.matE w (adjIncRight h) (θ w))ᵀ *ᵥ d) c) ^ 2 := by
    rw [a.nodeNormSq_eq_matE w (adjIncRight h) θ', hmatE',
      sum_sq_projAway_mul hd0 (a.matE w (adjIncRight h) (θ w)),
      ← a.nodeNormSq_eq_matE w (adjIncRight h) θ]
  -- (4) conclude
  have hddpos : (0 : ℝ) < d ⬝ᵥ d := dotProduct_self_pos hd0
  have hsum0 : (∑ c, (((a.matE w (adjIncRight h) (θ w))ᵀ *ᵥ d) c) ^ 2) = 0 := by
    have hnn : (0 : ℝ) ≤ ∑ c, (((a.matE w (adjIncRight h) (θ w))ᵀ *ᵥ d) c) ^ 2 :=
      Finset.sum_nonneg fun c _ => sq_nonneg _
    have hle : (d ⬝ᵥ d)⁻¹ * ∑ c, (((a.matE w (adjIncRight h) (θ w))ᵀ *ᵥ d) c) ^ 2 ≤ 0 := by
      rw [hnorm'] at hnorm; linarith
    nlinarith [inv_pos.mpr hddpos]
  funext c
  have hc := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => sq_nonneg _)).mp hsum0 c
    (Finset.mem_univ c)
  exact sq_eq_zero_iff.mp hc

/-! ### General matrix helpers -/

/-- Gram-kernel identity over `ℝ`: `ker(AᵀA) = ker A` (`AᵀAx = 0 ⇒ ‖Ax‖² = xᵀAᵀAx = 0`). -/
theorem ker_transpose_mul_self {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) :
    LinearMap.ker (Aᵀ * A).mulVecLin = LinearMap.ker A.mulVecLin := by
  ext x
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hx
    have h0 : (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = 0 := by
      have hdot : x ⬝ᵥ ((Aᵀ * A) *ᵥ x) = 0 := by rw [hx]; simp
      rwa [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at hdot
    exact dotProduct_self_eq_zero.mp h0
  · intro hx
    rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

/-- Rank–nullity for a matrix: `rank M + dim ker M = #columns`. -/
theorem rank_add_finrank_ker {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℝ) :
    M.rank + Module.finrank ℝ (LinearMap.ker M.mulVecLin) = Fintype.card n := by
  have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hdom : Module.finrank ℝ (n → ℝ) = Fintype.card n := by simp
  unfold Matrix.rank
  omega

/-- A square real matrix with trivial kernel is a unit. -/
theorem isUnit_of_ker_mulVecLin_eq_bot {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} (hker : LinearMap.ker M.mulVecLin = ⊥) : IsUnit M := by
  have hrank : M.rank = Fintype.card n := by
    have h := rank_add_finrank_ker M
    rw [hker] at h
    simpa using h
  rw [← Matrix.linearIndependent_cols_iff_isUnit,
    linearIndependent_iff_card_eq_finrank_span]
  rw [Matrix.rank_eq_finrank_span_cols] at hrank
  exact hrank.symm

/-! ### Minimum-norm kernel identities -/

/-- **Minimum-norm kernel identity at `H_e`**:
`ker H_e = D_e`. Chain: `ker H ⊆ ker matₑW_u ⊆ ker F ⊆ ker matₑW_w ⊆ ker H`, the middle
inclusions by factoring, the outer two by the min-norm zero-the-slice argument. -/
theorem minNorm_ker_Hfun_eq_dormant {u w : a.V} (h : a.G.Adj u w) {θ : a.Param}
    (hmn : a.MinNorm θ) :
    LinearMap.ker (a.Hfun h θ).mulVecLin = a.dormant h θ := by
  apply le_antisymm
  · intro d hdk
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hdk
    have h1 := a.minNorm_matE_u_ker h hmn hdk
    have h2 := a.Ffun_mulVec_eq_zero h θ h1
    have h3 := a.minNorm_matE_w_ker h hmn h2
    exact Submodule.mem_inf.mpr
      ⟨by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact h1,
       by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact h3⟩
  · intro d hdD
    obtain ⟨-, h2⟩ := Submodule.mem_inf.mp hdD
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2 ⊢
    exact a.Hfun_mulVec_eq_zero h θ h2

/-- **Minimum-norm kernel identity at `F_e`**: `ker F_e = D_e`. -/
theorem minNorm_ker_Ffun_eq_dormant {u w : a.V} (h : a.G.Adj u w) {θ : a.Param}
    (hmn : a.MinNorm θ) :
    LinearMap.ker (a.Ffun h θ).mulVecLin = a.dormant h θ := by
  apply le_antisymm
  · intro d hdk
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hdk
    have h1 := a.minNorm_matE_w_ker h hmn hdk
    have h2 := a.Hfun_mulVec_eq_zero h θ h1
    have h3 := a.minNorm_matE_u_ker h hmn h2
    exact Submodule.mem_inf.mpr
      ⟨by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact h3,
       by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact h1⟩
  · intro d hdD
    obtain ⟨h1, -⟩ := Submodule.mem_inf.mp hdD
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h1 ⊢
    exact a.Ffun_mulVec_eq_zero h θ h1

/-- **Minimum-norm dimension count**: `rank T⁽ᵉ⁾ + dim D_e = r_e` (stated additively;
the paper writes `dim D_e = r_e − rank T⁽ᵉ⁾`). Via `T⁽ᵉ⁾ = F Hᵀ` with `ker F = ker H = D_e`:
`range Hᵀ` meets `ker F` trivially (row space ∩ kernel = 0 over `ℝ`), so
`rank(F Hᵀ) = rank H = r_e − dim D_e`. -/
theorem minNorm_rank_add_finrank_dormant {u w : a.V} (h : a.G.Adj u w) {θ : a.Param}
    (hmn : a.MinNorm θ) :
    (a.matricize h θ).rank + Module.finrank ℝ (a.dormant h θ) = a.r s(u, w) := by
  have hkerH := a.minNorm_ker_Hfun_eq_dormant h hmn
  have hkerF := a.minNorm_ker_Ffun_eq_dormant h hmn
  -- `ker (F Hᵀ) = ker Hᵀ`: row space of `H` meets `ker F = ker H` trivially.
  have hkk : LinearMap.ker (a.Ffun h θ * (a.Hfun h θ)ᵀ).mulVecLin
      = LinearMap.ker ((a.Hfun h θ)ᵀ).mulVecLin := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec] at hx
      have hyD : (a.Hfun h θ)ᵀ *ᵥ x ∈ a.dormant h θ := by
        rw [← hkerF]
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        exact hx
      have hyH : a.Hfun h θ *ᵥ ((a.Hfun h θ)ᵀ *ᵥ x) = 0 := by
        rw [← hkerH] at hyD
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hyD
        exact hyD
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      have hyy : ((a.Hfun h θ)ᵀ *ᵥ x) ⬝ᵥ ((a.Hfun h θ)ᵀ *ᵥ x) = 0 := by
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hyH, zero_dotProduct]
      exact dotProduct_self_eq_zero.mp hyy
    · intro x hx
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
      rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  have h1 := rank_add_finrank_ker (a.Ffun h θ * (a.Hfun h θ)ᵀ)
  have h2 := rank_add_finrank_ker ((a.Hfun h θ)ᵀ)
  rw [hkk] at h1
  have hrank_eq : (a.Ffun h θ * (a.Hfun h θ)ᵀ).rank = ((a.Hfun h θ)ᵀ).rank := by omega
  have h3 := rank_add_finrank_ker (a.Hfun h θ)
  rw [hkerH, Fintype.card_fin] at h3
  rw [a.matricize_FH h θ, hrank_eq, Matrix.rank_transpose]
  exact h3

/-! ### Criticality in the bond frame -/

/-- **Bond-frame stationarity**: at a critical point, `F_eᵀ · R⁽ᵉ⁾ · H_e = 0` for the
matricized residual `R⁽ᵉ⁾ = T⁽ᵉ⁾ − T*⁽ᵉ⁾`. Proof: instantiate `Critical` at `w` with the
mode-`e` perturbation `δ = modeMul N (θ w)` for arbitrary `N`; by `Hfun_update_modeMul` /
`Ffun_update_col` the variation matricizes to `F N Hᵀ`, and the pairing is
`tr(R⁽ᵉ⁾ᵀ F N Hᵀ) = ⟨FᵀR⁽ᵉ⁾H, N⟩ = 0` for all `N`. This is the ONLY entry point of
criticality into the target-alignment layer. -/
theorem critical_bond_identity {Tstar : a.Ext → ℝ} {θ : a.Param} (hcrit : a.Critical Tstar θ)
    {u w : a.V} (h : a.G.Adj u w) :
    (a.Ffun h θ)ᵀ * (a.matricize h θ - a.matricizeOf h Tstar) * a.Hfun h θ = 0 := by
  classical
  set R := a.matricize h θ - a.matricizeOf h Tstar with hR
  set P := (a.Ffun h θ)ᵀ * R * a.Hfun h θ with hP
  -- generic 4-fold sum reordering
  have hswap4 : ∀ (f : a.Row h → a.Col h → Fin (a.r s(u, w)) → Fin (a.r s(u, w)) → ℝ),
      (∑ row, ∑ col, ∑ p, ∑ q, f row col p q)
        = ∑ p, ∑ q, ∑ row, ∑ col, f row col p q := by
    intro f
    calc (∑ row, ∑ col, ∑ p, ∑ q, f row col p q)
        = ∑ row, ∑ p, ∑ col, ∑ q, f row col p q :=
          Finset.sum_congr rfl fun row _ => Finset.sum_comm
      _ = ∑ p, ∑ row, ∑ col, ∑ q, f row col p q := Finset.sum_comm
      _ = ∑ p, ∑ row, ∑ q, ∑ col, f row col p q :=
          Finset.sum_congr rfl fun p _ =>
            Finset.sum_congr rfl fun row _ => Finset.sum_comm
      _ = ∑ p, ∑ q, ∑ row, ∑ col, f row col p q :=
          Finset.sum_congr rfl fun p _ => Finset.sum_comm
  -- for every direction N, the Frobenius pairing ⟨P, N⟩ vanishes
  have hkey : ∀ N : Matrix (Fin (a.r s(u, w))) (Fin (a.r s(u, w))) ℝ,
      (∑ p, ∑ q, P p q * N p q) = 0 := by
    intro N
    have hc := hcrit w (a.modeMul w (adjIncRight h) N (θ w))
    rw [← (a.extSplit h).symm.sum_comp
        (fun x => a.residual Tstar θ x
          * a.represented (Function.update θ w (a.modeMul w (adjIncRight h) N (θ w))) x),
      Fintype.sum_prod_type] at hc
    have hmat : a.matricize h (Function.update θ w (a.modeMul w (adjIncRight h) N (θ w)))
        = a.Ffun h θ * N * (a.Hfun h θ)ᵀ := by
      rw [a.matricize_FH h, a.Hfun_update_modeMul h θ N,
        a.Ffun_update_col h θ (a.not_side_right h), Matrix.transpose_mul,
        Matrix.transpose_transpose, ← Matrix.mul_assoc]
    have hexpand : ∀ (row : a.Row h) (col : a.Col h),
        a.residual Tstar θ ((a.extSplit h).symm (row, col))
          * a.represented (Function.update θ w (a.modeMul w (adjIncRight h) N (θ w)))
              ((a.extSplit h).symm (row, col))
        = ∑ p, ∑ q, (a.Ffun h θ row p * R row col * a.Hfun h θ col q) * N p q := by
      intro row col
      have h1 : a.residual Tstar θ ((a.extSplit h).symm (row, col)) = R row col := rfl
      have h2 : a.represented (Function.update θ w (a.modeMul w (adjIncRight h) N (θ w)))
          ((a.extSplit h).symm (row, col))
          = (a.Ffun h θ * N * (a.Hfun h θ)ᵀ) row col := by
        rw [← hmat]; rfl
      rw [h1, h2]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
    rw [Finset.sum_congr rfl
        (fun row _ => Finset.sum_congr rfl (fun col _ => hexpand row col)),
      hswap4] at hc
    have hPpq : ∀ p q,
        (∑ row, ∑ col, (a.Ffun h θ row p * R row col * a.Hfun h θ col q) * N p q)
          = P p q * N p q := by
      intro p q
      rw [hP]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      try rw [Finset.sum_comm]
      try exact Finset.sum_congr rfl fun col _ => Finset.sum_congr rfl fun row _ => by ring
    rw [Finset.sum_congr rfl
        (fun p _ => Finset.sum_congr rfl (fun q _ => hPpq p q))] at hc
    exact hc
  -- plug `N := P` and read off `P = 0` entrywise
  have hPP := hkey P
  ext p q
  rw [Matrix.zero_apply]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun p' _ => Finset.sum_nonneg fun q' _ => mul_self_nonneg (P p' q'))).mp hPP p
    (Finset.mem_univ p)
  have hzz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun q' _ => mul_self_nonneg (P p q'))).mp hz q (Finset.mem_univ q)
  exact mul_self_eq_zero.mp hzz

/-! ### THE helper: the target-times-`H` kernel is the dormant subspace -/

/-- **The single funnel identity**: at a min-norm critical point,
`ker (T*⁽ᵉ⁾ · H_e) = D_e`. The forward inclusion uses `ker H = D`; the reverse inclusion
is the gauge-free Gram chain:
`T*⁽ᵉ⁾H x = 0` + `critical_bond_identity` give `FᵀF (HᵀH x) = 0`, so
`HᵀH x ∈ ker(FᵀF) = ker F = ker H`; then `y := HᵀH x` has `H y = 0`, so
`‖y‖² = (Hx)ᵀ(Hy) = 0`, so `HᵀH x = 0`, so `‖Hx‖² = xᵀ(HᵀHx) = 0`, so `x ∈ ker H = D_e`.
The alignment, rank-comparison, and invertibility results are all corollaries of this identity. -/
theorem ker_matricizeOf_mul_Hfun_eq_dormant {Tstar : a.Ext → ℝ} {θ : a.Param}
    (hmn : a.MinNorm θ) (hcrit : a.Critical Tstar θ) {u w : a.V} (h : a.G.Adj u w) :
    LinearMap.ker (a.matricizeOf h Tstar * a.Hfun h θ).mulVecLin = a.dormant h θ := by
  have hkerH := a.minNorm_ker_Hfun_eq_dormant h hmn
  have hkerF := a.minNorm_ker_Ffun_eq_dormant h hmn
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec] at hx
    -- rearrange the critical identity to `FᵀT⁽ᵉ⁾H = FᵀT*⁽ᵉ⁾H`
    have hci' : (a.Ffun h θ)ᵀ * a.matricize h θ * a.Hfun h θ
        = (a.Ffun h θ)ᵀ * a.matricizeOf h Tstar * a.Hfun h θ := by
      have h1 := a.critical_bond_identity hcrit h
      rw [Matrix.mul_sub, Matrix.sub_mul, sub_eq_zero] at h1
      exact h1
    have happ := congrArg (fun M => M *ᵥ x) hci'
    simp only [a.matricize_FH h θ, ← Matrix.mulVec_mulVec] at happ
    rw [hx, Matrix.mulVec_zero] at happ
    -- happ : Fᵀ *ᵥ (F *ᵥ (Hᵀ *ᵥ (H *ᵥ x))) = 0
    set y := (a.Hfun h θ)ᵀ *ᵥ (a.Hfun h θ *ᵥ x) with hy
    have hyD : y ∈ LinearMap.ker (a.Ffun h θ).mulVecLin := by
      rw [← ker_transpose_mul_self]
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
      exact happ
    rw [hkerF, ← hkerH] at hyD
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hyD
    have hy0 : y = 0 := by
      have hyy : y ⬝ᵥ y = 0 := by
        nth_rewrite 1 [hy]
        rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hyD,
          dotProduct_zero]
      exact dotProduct_self_eq_zero.mp hyy
    have hHx : a.Hfun h θ *ᵥ x = 0 := by
      have hxx : (a.Hfun h θ *ᵥ x) ⬝ᵥ (a.Hfun h θ *ᵥ x) = 0 := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ← hy, hy0,
          zero_dotProduct]
      exact dotProduct_self_eq_zero.mp hxx
    rw [← hkerH, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hHx
  · intro d hdD
    rw [← hkerH] at hdD
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hdD ⊢
    rw [← Matrix.mulVec_mulVec, hdD, Matrix.mulVec_zero]

/-! ### Target alignment, rank comparison, and cross-Gram invertibility -/

/-- **Active directions are target-aligned**, complement-free form: at a
min-norm critical point, for ANY factorization `T*⁽ᵉ⁾ = F* H*ᵀ` through the bond space, the
cross-Gram `M_e = H*ᵀ H_e` satisfies `ker M_e ⊆ D_e`. (Equivalent to the paper's "`M_e` is
injective on `A_e = D_eᗮ`", since `D_e = ker H_e ⊆ ker M_e` always.) Corollary of
`ker_matricizeOf_mul_Hfun_eq_dormant`: `M_e x = 0 ⇒ T*⁽ᵉ⁾H x = F*(H*ᵀH x) = 0 ⇒ x ∈ D_e`. -/
theorem minNorm_critical_ker_crossGram_le_dormant {Tstar : a.Ext → ℝ} {θ : a.Param}
    (hmn : a.MinNorm θ) (hcrit : a.Critical Tstar θ) {u w : a.V} (h : a.G.Adj u w)
    {Fstar : Matrix (a.Row h) (Fin (a.r s(u, w))) ℝ}
    {Hstar : Matrix (a.Col h) (Fin (a.r s(u, w))) ℝ}
    (hFH : a.matricizeOf h Tstar = Fstar * Hstarᵀ) :
    LinearMap.ker (Hstarᵀ * a.Hfun h θ).mulVecLin ≤ a.dormant h θ := by
  intro x hx
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
  rw [← a.ker_matricizeOf_mul_Hfun_eq_dormant hmn hcrit h,
    LinearMap.mem_ker, Matrix.mulVecLin_apply, hFH, Matrix.mul_assoc,
    ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

/-- **Model rank is bounded by target rank**: at a minimum-norm critical point,
`rank T⁽ᵉ⁾ ≤ rank T*⁽ᵉ⁾` on every internal edge — no realizability or bond-bound side
hypothesis; in particular, the paper's standing realizability assumption is not needed here.
Proof: `rank T⁽ᵉ⁾ = r_e − dim D_e = rank(T*⁽ᵉ⁾H_e)
≤ rank T*⁽ᵉ⁾` by the dimension count, `ker_matricizeOf_mul_Hfun_eq_dormant` + rank-nullity, and
`rank_mul_le_left`. -/
theorem minNorm_critical_rank_le_target {Tstar : a.Ext → ℝ} {θ : a.Param}
    (hmn : a.MinNorm θ) (hcrit : a.Critical Tstar θ) {u w : a.V} (h : a.G.Adj u w) :
    (a.matricize h θ).rank ≤ (a.matricizeOf h Tstar).rank := by
  have hcount := a.minNorm_rank_add_finrank_dormant h hmn
  have hrn := rank_add_finrank_ker (a.matricizeOf h Tstar * a.Hfun h θ)
  rw [a.ker_matricizeOf_mul_Hfun_eq_dormant hmn hcrit h, Fintype.card_fin] at hrn
  have hle : (a.matricizeOf h Tstar * a.Hfun h θ).rank ≤ (a.matricizeOf h Tstar).rank :=
    Matrix.rank_mul_le_left _ _
  omega

/-- **Full model rank implies an invertible cross-Gram**: at a minimum-norm critical point
with `rank T⁽ᵉ⁾ = r_e`, the cross-Gram of ANY factorization of `T*⁽ᵉ⁾` is invertible.
(`dim D_e = 0` by the dimension count, so `ker M_e = ⊥` by target alignment; a square matrix over a field with
trivial kernel is a unit.) -/
theorem minNorm_critical_isUnit_crossGram {Tstar : a.Ext → ℝ} {θ : a.Param}
    (hmn : a.MinNorm θ) (hcrit : a.Critical Tstar θ) {u w : a.V} (h : a.G.Adj u w)
    {Fstar : Matrix (a.Row h) (Fin (a.r s(u, w))) ℝ}
    {Hstar : Matrix (a.Col h) (Fin (a.r s(u, w))) ℝ}
    (hFH : a.matricizeOf h Tstar = Fstar * Hstarᵀ)
    (hfull : (a.matricize h θ).rank = a.r s(u, w)) :
    IsUnit (Hstarᵀ * a.Hfun h θ) := by
  have hcount := a.minNorm_rank_add_finrank_dormant h hmn
  have hD0 : Module.finrank ℝ (a.dormant h θ) = 0 := by omega
  have hDbot : a.dormant h θ = ⊥ := Submodule.finrank_eq_zero.mp hD0
  have hker := a.minNorm_critical_ker_crossGram_le_dormant hmn hcrit h hFH
  rw [hDbot, le_bot_iff] at hker
  exact isUnit_of_ker_mulVecLin_eq_bot hker


/-! ### Endpoint kernel identities and the full-Tucker-rank bridge -/

/-- At a min-norm point the **left endpoint unfolding's kernel** is exactly the dormant
subspace (all four kernels coincide). -/
theorem minNorm_ker_matE_left_eq_dormant {u w : a.V} (h : a.G.Adj u w) {θ : a.Param}
    (hmn : a.MinNorm θ) :
    LinearMap.ker ((a.matE u (adjIncLeft h) (θ u))ᵀ).mulVecLin = a.dormant h θ := by
  apply le_antisymm
  · intro d hd
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hd
    have h2 := a.Ffun_mulVec_eq_zero h θ hd
    have h3 := a.minNorm_matE_w_ker h hmn h2
    exact Submodule.mem_inf.mpr
      ⟨by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hd,
       by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact h3⟩
  · exact inf_le_left

/-- At a min-norm point the **right endpoint unfolding's kernel** is exactly the dormant
subspace. -/
theorem minNorm_ker_matE_right_eq_dormant {u w : a.V} (h : a.G.Adj u w) {θ : a.Param}
    (hmn : a.MinNorm θ) :
    LinearMap.ker ((a.matE w (adjIncRight h) (θ w))ᵀ).mulVecLin = a.dormant h θ := by
  apply le_antisymm
  · intro d hd
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hd
    have h2 := a.Hfun_mulVec_eq_zero h θ hd
    have h3 := a.minNorm_matE_u_ker h hmn h2
    exact Submodule.mem_inf.mpr
      ⟨by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact h3,
       by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hd⟩
  · exact inf_le_right

/-- **Full model rank at every edge ⇒ full Tucker rank, at a min-norm point** (the bridge
that hands Theorem 4.3's full-rank branch to Theorem 5.2). Every incidence is the left slot
of an oriented edge; the endpoint kernel identities plus the dimension count pin the unfolding rank. -/
theorem fullTuckerRank_of_minNorm_of_rank_eq {θ : a.Param} (hmn : a.MinNorm θ)
    (hfull : ∀ (u w : a.V) (h : a.G.Adj u w), (a.matricize h θ).rank = a.r s(u, w)) :
    a.FullTuckerRank θ := by
  intro v e
  have hspec : s(v, Sym2.Mem.other' e.2.2) = e.1 := Sym2.other_spec' e.2.2
  have hadj : a.G.Adj v (Sym2.Mem.other' e.2.2) := by
    rw [← SimpleGraph.mem_edgeSet, hspec]; exact e.2.1
  have he : e = adjIncLeft hadj := Subtype.ext hspec.symm
  rw [he]
  -- dormant is trivial at this edge
  have hcount := a.minNorm_rank_add_finrank_dormant hadj hmn
  rw [hfull v _ hadj] at hcount
  have hD0 : Module.finrank ℝ (a.dormant hadj θ) = 0 := by omega
  have hDbot : a.dormant hadj θ = ⊥ := Submodule.finrank_eq_zero.mp hD0
  -- hence the left unfolding's transpose has trivial kernel, pinning the rank
  have hker := a.minNorm_ker_matE_left_eq_dormant hadj hmn
  rw [hDbot] at hker
  have hrn := rank_add_finrank_ker ((a.matE v (adjIncLeft hadj) (θ v))ᵀ)
  rw [hker, Fintype.card_fin] at hrn
  simp only [finrank_bot] at hrn
  rw [← Matrix.rank_transpose]
  omega
end Arch

end TTN
