import TTN.Landscape.Component
import TTN.Landscape.Compress
import TTN.Landscape.EnvPair

/-!
# Rank transport and side confinement

This module proves the generic
rank lemmas for the `P·R⁽ᵉ*⁾·Qᵀ` argument, matricization linearity, and the confinement of
the deficient component to one side of any full-rank (hence non-component) edge.
-/

open scoped Matrix

namespace TTN

namespace Arch

variable {a : Arch}

/-- Left multiplication by a matrix with trivial kernel preserves rank. -/
theorem rank_mul_eq_right_of_ker_eq_bot {l m C : Type*} [Fintype l] [Fintype m] [Fintype C]
    {A : Matrix l m ℝ} (hA : LinearMap.ker A.mulVecLin = ⊥)
    (B : Matrix m C ℝ) : (A * B).rank = B.rank := by
  have hinj : Function.Injective A.mulVecLin := LinearMap.ker_eq_bot.mp hA
  show Module.finrank ℝ (LinearMap.range (A * B).mulVecLin) = _
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
  exact ((Submodule.equivMapOfInjective _ hinj _).finrank_eq).symm

/-- Right multiplication by a matrix whose transpose has trivial kernel preserves rank. -/
theorem rank_mul_eq_left_of_ker_transpose_eq_bot {l m C : Type*} [Fintype l] [Fintype m]
    [Fintype C] {B : Matrix C l ℝ}
    (hB : LinearMap.ker (Bᵀ).mulVecLin = ⊥) (A : Matrix m C ℝ) :
    (A * B).rank = A.rank := by
  rw [← Matrix.rank_transpose (A * B), Matrix.transpose_mul,
    rank_mul_eq_right_of_ker_eq_bot hB, Matrix.rank_transpose]

/-- The matricization of the residual is the difference of the model and target
matricizations. -/
theorem matricizeOf_residual {u w : a.V} (h : a.G.Adj u w) (Tstar : a.Ext → ℝ)
    (θ : a.Param) :
    a.matricizeOf h (a.residual Tstar θ) = a.matricize h θ - a.matricizeOf h Tstar := by
  ext row col
  show a.residual Tstar θ ((a.extSplit h).symm (row, col)) = _
  show a.represented θ ((a.extSplit h).symm (row, col))
      - Tstar ((a.extSplit h).symm (row, col)) = _
  rfl

/-- A nonzero matrix has a nonzero entry. -/
theorem exists_entry_ne_zero_of_ne_zero {m C : Type*} {M : Matrix m C ℝ} (hM : M ≠ 0) :
    ∃ i j, M i j ≠ 0 := by
  by_contra hall
  push Not at hall
  exact hM (by ext i j; rw [hall i j, Matrix.zero_apply])

/-- **Walks avoiding the cut edge stay on one side** (transfer into the deleted graph). -/
theorem side_iff_of_walk_avoiding {u w : a.V} (h : a.G.Adj u w) {p q : a.V}
    (W : a.G.Walk p q) (hW : s(u, w) ∉ W.edges) : a.Side h p ↔ a.Side h q := by
  classical
  have hsub : ∀ e ∈ W.edges, e ∈ (a.G.deleteEdges {s(u, w)}).edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_deleteEdges]
    refine ⟨W.edges_subset_edgeSet he, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hc
    exact hW (hc ▸ he)
  have hreach : (a.G.deleteEdges {s(u, w)}).Reachable p q := ⟨W.transfer _ hsub⟩
  unfold Side
  exact ⟨fun hp => hp.trans hreach, fun hq => hq.trans hreach.symm⟩

/-- **The deficient component is confined to one side of any non-component edge**: two
`Gdef`-reachable vertices lie on the same side of the cut at a full-model-rank edge. -/
theorem side_iff_of_gdef_reachable {θ : a.Param} {u w : a.V} (h : a.G.Adj u w)
    (hfull : ¬ (a.matricize h θ).rank < a.r s(u, w)) {p q : a.V}
    (hr : (a.Gdef θ).Reachable p q) : a.Side h p ↔ a.Side h q := by
  classical
  obtain ⟨W'⟩ := hr
  have hle : ∀ e ∈ W'.edges, e ∈ a.G.edgeSet := by
    intro e he
    have h1 : e ∈ (a.Gdef θ).edgeSet := W'.edges_subset_edgeSet he
    have hle' : a.Gdef θ ≤ a.G := fun x y hxy => hxy.choose
    exact SimpleGraph.edgeSet_subset_edgeSet.mpr hle' h1
  refine a.side_iff_of_walk_avoiding h (W'.transfer a.G hle) ?_
  rw [SimpleGraph.Walk.edges_transfer]
  intro hmem
  have hGdef : (a.Gdef θ).Adj u w := by
    have h2 : s(u, w) ∈ (a.Gdef θ).edgeSet := W'.edges_subset_edgeSet hmem
    rwa [SimpleGraph.mem_edgeSet] at h2
  obtain ⟨h', hrank⟩ := hGdef
  exact hfull hrank

/-- **Nested-cut factorization**: if the subtree behind the cut at `f = s(p,q)` (the
`q`-side) lies inside the column side of the `e* = s(xs,ys)`-cut, then an `f`-cut
factorization `W⁽ᶠ⁾ = F·Hᵀ` expresses the `e*`-matricization of `W` with the subtree block
of every column factored through `H`. -/
theorem matricizeOf_nested_factor {xs ys p q : a.V} (hstar : a.G.Adj xs ys)
    (hf : a.G.Adj p q) (hsub : ∀ z : a.V, ¬ a.Side hf z → ¬ a.Side hstar z)
    (W : a.Ext → ℝ) {F : Matrix (a.Row hf) (Fin (a.r s(p, q))) ℝ}
    {H : Matrix (a.Col hf) (Fin (a.r s(p, q))) ℝ}
    (hFH : a.matricizeOf hf W = F * Hᵀ) (rx : a.Row hstar) (cx : a.Col hstar) :
    a.matricizeOf hstar W rx cx
      = ∑ m : Fin (a.r s(p, q)),
          F (fun z : {z : a.V // a.Side hf z} =>
              if hz : a.Side hstar z.1 then rx ⟨z.1, hz⟩ else cx ⟨z.1, hz⟩) m
            * H (fun z : {z : a.V // ¬ a.Side hf z} => cx ⟨z.1, hsub z.1 z.2⟩) m := by
  classical
  set x : a.Ext := (a.extSplit hstar).symm (rx, cx) with hxdef
  have hx : a.matricizeOf hstar W rx cx = W x := rfl
  have hW : W x = a.matricizeOf hf W ((a.extSplit hf) x).1 ((a.extSplit hf) x).2 := by
    show W x = W ((a.extSplit hf).symm ((a.extSplit hf) x))
    rw [Equiv.symm_apply_apply]
  have hxz : ∀ z : a.V, x z = if hz : a.Side hstar z then rx ⟨z, hz⟩ else cx ⟨z, hz⟩ := by
    intro z
    show ((a.extSplit hstar).symm (rx, cx)) z = _
    by_cases hz : a.Side hstar z
    · rw [dif_pos hz]
      show (if h : a.Side hstar z then rx ⟨z, h⟩ else cx ⟨z, h⟩) = rx ⟨z, hz⟩
      exact dif_pos hz
    · rw [dif_neg hz]
      show (if h : a.Side hstar z then rx ⟨z, h⟩ else cx ⟨z, h⟩) = cx ⟨z, hz⟩
      exact dif_neg hz
  have hargF : ((a.extSplit hf) x).1 = (fun z : {z : a.V // a.Side hf z} =>
      if hz : a.Side hstar z.1 then rx ⟨z.1, hz⟩ else cx ⟨z.1, hz⟩) := by
    funext z
    show x z.1 = _
    exact hxz z.1
  have hargH : ((a.extSplit hf) x).2 = (fun z : {z : a.V // ¬ a.Side hf z} =>
      cx ⟨z.1, hsub z.1 z.2⟩) := by
    funext z
    show x z.1 = _
    rw [hxz z.1]
    exact dif_neg (hsub z.1 z.2)
  rw [hx, hW, hFH, Matrix.mul_apply, hargF, hargH]
  exact Finset.sum_congr rfl (fun m _ => by rw [Matrix.transpose_apply])


/-- **The component sits on the near side of each of its boundary edges**: for a
full-model-rank edge `s(p, q)` with `p` in the deficient component (the `Gdef`-reachability
class of `p₀`), every vertex of the component is on `p`'s side of the cut. -/
theorem component_side_of_boundary {θ : a.Param} {p₀ : a.V}
    {p q : a.V} (hpq : a.G.Adj p q)
    (hfull : ¬ (a.matricize hpq θ).rank < a.r s(p, q))
    (hp : (a.Gdef θ).Reachable p₀ p) {s : a.V}
    (hs : (a.Gdef θ).Reachable p₀ s) : a.Side hpq s :=
  (a.side_iff_of_gdef_reachable hpq hfull (hp.symm.trans hs)).mp (a.side_left hpq)


/-- A unit matrix (in the monoid sense) has trivial kernel. -/
theorem ker_mulVecLin_eq_bot_of_isUnit {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℝ} (hA : IsUnit A) : LinearMap.ker A.mulVecLin = ⊥ := by
  obtain ⟨u, hu⟩ := hA
  rw [LinearMap.ker_eq_bot]
  intro x y hxy
  have hxy' : A *ᵥ x = A *ᵥ y := hxy
  have h1 : ((↑u⁻¹ : Matrix m m ℝ) * A) *ᵥ x = ((↑u⁻¹ : Matrix m m ℝ) * A) *ᵥ y := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy']
  have h2 : ((↑u⁻¹ : Matrix m m ℝ) * A) = 1 := by
    rw [← hu]
    exact u.inv_mul
  rwa [h2, Matrix.one_mulVec, Matrix.one_mulVec] at h1

/-- **The peel step, matrix form**: compressing a matrix that factors through `D` by a `C`
with `C·D` invertible preserves its rank. (The environment absorption of one boundary
subtree: `D` is the target's subtree expansion, `C` the model's subtree contraction, and
`C·D` the invertible boundary cross-Gram.) -/
theorem rank_comp_eq_of_factor {Y Z R' : Type*} [Fintype Y] [Fintype Z]
    [Fintype R'] [DecidableEq R'] {g : Matrix Y Z ℝ} {D : Matrix Y R' ℝ}
    {W₀ : Matrix R' Z ℝ} {C : Matrix R' Y ℝ}
    (hg : g = D * W₀) (hCD : IsUnit (C * D)) : (C * g).rank = g.rank := by
  have h1 : (C * g).rank = W₀.rank := by
    rw [hg, ← Matrix.mul_assoc]
    exact rank_mul_eq_right_of_ker_eq_bot (ker_mulVecLin_eq_bot_of_isUnit hCD) W₀
  have h2 : g.rank ≤ W₀.rank := by
    rw [hg]
    exact Matrix.rank_mul_le_right D W₀
  have h3 : (C * g).rank ≤ g.rank := Matrix.rank_mul_le_right C g
  omega


/-! ### The grouped contraction and the boundary Kronecker algebra

Boundary edges are oriented by a chosen family `oP/oQ/oAdj/oEdge/oS` (the `S` endpoint
first); `oSide` says that the whole component is on the near side, and `oPart` says that
every far vertex lies behind exactly one boundary edge. -/

noncomputable instance (S : Finset a.V) :
    Fintype {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} := by
  classical
  infer_instance

noncomputable instance (S : Finset a.V) :
    Fintype {E : a.G.edgeSet // a.EdgeInside S E} := by
  classical
  infer_instance

noncomputable instance (S : Finset a.V) :
    Fintype {E : a.G.edgeSet // ¬ a.EdgeTouches S E} := by
  classical
  infer_instance

noncomputable instance {u w : a.V} (h : a.G.Adj u w) :
    Fintype {e : a.G.edgeSet // e ≠ a.cutEdge h ∧ ¬ a.EdgeSide h e} := by
  classical
  infer_instance

open Classical in
/-- **The S-core contraction**: the `S`-node tensors contracted over the inside bonds, with
the boundary bonds `β` and the `S`-external coordinates `ξ` left open. -/
noncomputable def SCore (θ : a.Param) (S : Finset a.V) (ξ : a.SExtC S)
    (β : a.BdryBond S) : ℝ :=
  ∑ bK : a.KBond S, ∏ v : {v : a.V // v ∈ S},
    θ v.1 (fun e => if h : a.EdgeInside S ⟨e.1, e.2.1⟩
        then bK ⟨⟨e.1, e.2.1⟩, h⟩
        else β ⟨⟨e.1, e.2.1⟩, ⟨v.1, e.2.2, v.2⟩, h⟩) (ξ v)

open Classical in
/-- **Grouped contraction, pre-orientation form**: the represented tensor is the S-core
paired with the joint environment, summed over the boundary bonds. Pure bond/vertex Fubini
(no orientation data needed). -/
theorem represented_eq_sum_SCore_mul_envFactor (θ : a.Param) (S : Finset a.V) (x : a.Ext) :
    a.represented θ x
      = ∑ β : a.BdryBond S, a.SCore θ S (fun v => x v.1) β
          * a.envFactor θ S β (fun y => x y.1) := by
  classical
  show (∑ b : a.Bond, ∏ v : a.V, θ v (Bond.restrict b v) (x v)) = _
  -- value of the S-node tensor, bond argument rewritten by class
  have hSval : ∀ (bK : a.KBond S) (bB : a.BdryBond S) (bF : a.FarBond S)
      (v : {v : a.V // v ∈ S}),
      θ v.1 (Bond.restrict ((a.bondSplit S).symm (bK, bB, bF)) v.1) (x v.1)
      = θ v.1 (fun e => if h : a.EdgeInside S ⟨e.1, e.2.1⟩
            then bK ⟨⟨e.1, e.2.1⟩, h⟩
            else bB ⟨⟨e.1, e.2.1⟩, ⟨v.1, e.2.2, v.2⟩, h⟩) (x v.1) := by
    intro bK bB bF v
    refine congrArg (fun g => θ v.1 g (x v.1)) ?_
    funext e
    show (a.bondSplit S).symm (bK, bB, bF) ⟨e.1, e.2.1⟩ = _
    rw [a.bondSplit_symm_apply]
    by_cases hin : a.EdgeInside S ⟨e.1, e.2.1⟩
    · rw [dif_pos hin, dif_pos hin]
    · rw [dif_neg hin, dif_neg hin,
        dif_pos (show a.EdgeTouches S ⟨e.1, e.2.1⟩ from ⟨v.1, e.2.2, v.2⟩)]
  -- value of a far-node tensor, bond argument rewritten by class
  have hFval : ∀ (bK : a.KBond S) (bB : a.BdryBond S) (bF : a.FarBond S)
      (y : {y : a.V // y ∉ S}),
      θ y.1 (Bond.restrict ((a.bondSplit S).symm (bK, bB, bF)) y.1) (x y.1)
      = θ y.1 (fun e => if h : a.EdgeTouches S ⟨e.1, e.2.1⟩
            then bB ⟨⟨e.1, e.2.1⟩, h, fun hins => y.2 (hins y.1 e.2.2)⟩
            else bF ⟨⟨e.1, e.2.1⟩, h⟩) (x y.1) := by
    intro bK bB bF y
    refine congrArg (fun g => θ y.1 g (x y.1)) ?_
    funext e
    show (a.bondSplit S).symm (bK, bB, bF) ⟨e.1, e.2.1⟩ = _
    rw [a.bondSplit_symm_apply, dif_neg (fun hins => y.2 (hins y.1 e.2.2))]
  -- the per-triple summand splits over S / far
  have hmaster : ∀ (bK : a.KBond S) (bB : a.BdryBond S) (bF : a.FarBond S),
      (∏ v : a.V, θ v (Bond.restrict ((a.bondSplit S).symm (bK, bB, bF)) v) (x v))
      = (∏ v : {v : a.V // v ∈ S}, θ v.1 (fun e => if h : a.EdgeInside S ⟨e.1, e.2.1⟩
              then bK ⟨⟨e.1, e.2.1⟩, h⟩
              else bB ⟨⟨e.1, e.2.1⟩, ⟨v.1, e.2.2, v.2⟩, h⟩) (x v.1))
        * (∏ y : {y : a.V // y ∉ S}, θ y.1 (fun e => if h : a.EdgeTouches S ⟨e.1, e.2.1⟩
              then bB ⟨⟨e.1, e.2.1⟩, h, fun hins => y.2 (hins y.1 e.2.2)⟩
              else bF ⟨⟨e.1, e.2.1⟩, h⟩) (x y.1)) := by
    intro bK bB bF
    rw [prod_split_S S (fun v => θ v (Bond.restrict ((a.bondSplit S).symm (bK, bB, bF)) v) (x v)),
      Finset.prod_congr rfl (fun v _ => hSval bK bB bF v),
      Finset.prod_congr rfl (fun y _ => hFval bK bB bF y)]
  -- reindex the bond sum by the three-class split
  have hreindex : (∑ b : a.Bond, ∏ v, θ v (Bond.restrict b v) (x v))
      = ∑ bK : a.KBond S, ∑ bB : a.BdryBond S, ∑ bF : a.FarBond S,
          ∏ v, θ v (Bond.restrict ((a.bondSplit S).symm (bK, bB, bF)) v) (x v) := by
    calc (∑ b : a.Bond, ∏ v, θ v (Bond.restrict b v) (x v))
        = ∑ p : a.KBond S × a.BdryBond S × a.FarBond S,
            ∏ v, θ v (Bond.restrict ((a.bondSplit S).symm p) v) (x v) :=
          (Fintype.sum_equiv (a.bondSplit S).symm _ _ (fun p => rfl)).symm
      _ = ∑ bK : a.KBond S, ∑ q : a.BdryBond S × a.FarBond S,
            ∏ v, θ v (Bond.restrict ((a.bondSplit S).symm (bK, q)) v) (x v) :=
          Fintype.sum_prod_type _
      _ = ∑ bK, ∑ bB, ∑ bF,
            ∏ v, θ v (Bond.restrict ((a.bondSplit S).symm (bK, bB, bF)) v) (x v) :=
          Finset.sum_congr rfl (fun bK _ => Fintype.sum_prod_type _)
  rw [hreindex, Finset.sum_congr rfl (fun bK _ => Finset.sum_congr rfl (fun bB _ =>
    Finset.sum_congr rfl (fun bF _ => hmaster bK bB bF)))]
  rw [Finset.sum_congr rfl fun bK _ => Finset.sum_congr rfl fun bB _ => by
    rw [← Finset.mul_sum]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun bB _ => ?_)
  rw [← Finset.sum_mul]
  rfl

/-- Transport of a bond value along an edge equality preserves the `Fin` value. -/
theorem eqRec_edge_val {P : a.G.edgeSet → ℕ} {E E' : a.G.edgeSet}
    (hh : E = E') (z : Fin (P E)) : (hh ▸ z).val = z.val := by cases hh; rfl

/-- Fubini: a finite product of full sums is the sum over the dependent product of the
factorwise products. -/
theorem prod_univ_sum_pi {I : Type*} [Fintype I] [DecidableEq I] {κ : I → Type*}
    [∀ i, Fintype (κ i)] (f : (i : I) → κ i → ℝ) :
    ∏ i, ∑ k : κ i, f i k = ∑ g : (i : I) → κ i, ∏ i, f i (g i) := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- **Every far edge lies behind exactly one boundary edge.** Its endpoints are far
vertices; they share a subtree (bridge property), and that subtree is unique by `oPart`. -/
theorem edgeSubtree_existsUnique (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)) (oEdge : ∀ f, s(oP f, oQ f) = f.1.1)
    (oPart : ∀ y : a.V, y ∉ S → ∃! f, ¬ a.Side (oAdj f) y)
    (E : {E : a.G.edgeSet // ¬ a.EdgeTouches S E}) :
    ∃! f, ¬ a.EdgeSide (oAdj f) E.1 := by
  obtain ⟨E, hnt⟩ := E
  obtain ⟨e, he⟩ := E
  induction e using Sym2.ind with
  | _ p q =>
    have hadj : a.G.Adj p q := by rwa [SimpleGraph.mem_edgeSet] at he
    have hp : p ∉ S := fun hpS => hnt ⟨p, Sym2.mem_mk_left p q, hpS⟩
    obtain ⟨fp, hfp, hfpU⟩ := oPart p hp
    refine ⟨fp, ?_, ?_⟩
    · intro hall
      exact hfp (hall p (Sym2.mem_mk_left p q))
    · intro f' hf'
      apply hfpU f'
      have hneS : s(p, q) ≠ s(oP f', oQ f') := by
        intro hc
        apply hnt
        have hEeq : (⟨s(p, q), he⟩ : a.G.edgeSet) = f'.1 :=
          Subtype.ext (hc.trans (oEdge f'))
        rw [hEeq]; exact f'.2.1
      intro hSp
      apply hf'
      intro x hx
      have hSq : a.Side (oAdj f') q := (a.side_iff_of_adj (oAdj f') hadj hneS).mp hSp
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact hSp
      · exact hSq

/-- A column-edge of the `f`-cut (other side than `oP f`, not the cut edge) is a far edge:
both its endpoints lie off `Side (oAdj f)`, hence outside `S`. -/
theorem bondcol_far (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f))
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    (f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E})
    (e : {e : a.G.edgeSet // e ≠ a.cutEdge (oAdj f) ∧ ¬ a.EdgeSide (oAdj f) e}) :
    ¬ a.EdgeTouches S e.1 := by
  obtain ⟨⟨ed, hed⟩, hne, hns⟩ := e
  induction ed using Sym2.ind with
  | _ p q =>
    have hadj : a.G.Adj p q := by rwa [SimpleGraph.mem_edgeSet] at hed
    have hne' : s(p, q) ≠ s(oP f, oQ f) := fun hc => hne (Subtype.ext hc)
    have hnotboth : ¬ (a.Side (oAdj f) p ∧ a.Side (oAdj f) q) := by
      rintro ⟨hSp, hSq⟩
      exact hns (fun x hx => by rcases Sym2.mem_iff.mp hx with rfl | rfl; exacts [hSp, hSq])
    have hiff := a.side_iff_of_adj (oAdj f) hadj hne'
    have hpns : ¬ a.Side (oAdj f) p := fun hSp => hnotboth ⟨hSp, hiff.mp hSp⟩
    have hqns : ¬ a.Side (oAdj f) q := fun hSq => hnotboth ⟨hiff.mpr hSq, hSq⟩
    rintro ⟨v, hv, hvS⟩
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact oSide f v hpns hvS
    · exact oSide f v hqns hvS

/-- **The pinned boundary slot cast.** When an incident edge `E` of a subtree vertex is the
cut edge `s(oP f, oQ f)`, the `bondInvFun` value (the transported `Hfun` column index) equals
the boundary bond `β` at that edge. Pure `Fin`-value bookkeeping. -/
theorem cut_slot_cast (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)) (oEdge : ∀ f, s(oP f, oQ f) = f.1.1)
    (β : a.BdryBond S) (f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E})
    (E : a.G.edgeSet) (he : E = a.cutEdge (oAdj f))
    (ht : a.EdgeTouches S E) (hni : ¬ a.EdgeInside S E) :
    (he.symm ▸ ((finCongr (congrArg a.r (oEdge f))).symm (β f)) : Fin (a.r E.1))
      = β ⟨E, ht, hni⟩ := by
  subst he
  have hpt : (⟨a.cutEdge (oAdj f), ht, hni⟩ :
      {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}) = f :=
    Subtype.ext (Subtype.ext (oEdge f))
  apply Fin.ext
  show ((finCongr (congrArg a.r (oEdge f))).symm (β f)).val = (β ⟨_, ht, hni⟩).val
  rw [show ((finCongr (congrArg a.r (oEdge f))).symm (β f)).val = (β f).val from by simp]
  exact (congrArg (fun g => (β g).val) hpt).symm

/-- **The far vertices partition into the boundary subtrees.** Each `y ∉ S` lies behind
exactly one boundary edge (`oPart`); each subtree is contained in the far vertices (`oSide`). -/
theorem prod_far_split (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f))
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    (oPart : ∀ y : a.V, y ∉ S → ∃! f, ¬ a.Side (oAdj f) y)
    (F : {y : a.V // y ∉ S} → ℝ) :
    (∏ y : {y : a.V // y ∉ S}, F y)
      = ∏ f, ∏ z : {z : a.V // ¬ a.Side (oAdj f) z}, F ⟨z.1, oSide f z.1 z.2⟩ := by
  classical
  set vmap : {y : a.V // y ∉ S} → {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} :=
    fun y => (oPart y.1 y.2).choose with hvmap
  have hspec : ∀ y, ¬ a.Side (oAdj (vmap y)) y.1 := fun y => (oPart y.1 y.2).choose_spec.1
  have huniq : ∀ (y : {y : a.V // y ∉ S}) (g), ¬ a.Side (oAdj g) y.1 → g = vmap y :=
    fun y g hg => (oPart y.1 y.2).choose_spec.2 g hg
  let efib : ∀ f, {y : {y : a.V // y ∉ S} // vmap y = f} ≃ {z : a.V // ¬ a.Side (oAdj f) z} :=
    fun f =>
    { toFun := fun y => ⟨y.1.1, by have h := hspec y.1; rw [y.2] at h; exact h⟩
      invFun := fun z => ⟨⟨z.1, oSide f z.1 z.2⟩, (huniq ⟨z.1, oSide f z.1 z.2⟩ f z.2).symm⟩
      left_inv := fun y => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun z => by apply Subtype.ext; rfl }
  rw [← Equiv.prod_comp (Equiv.sigmaFiberEquiv vmap) F, ← Finset.univ_sigma_univ,
    Finset.prod_sigma]
  refine Finset.prod_congr rfl (fun f _ => ?_)
  refine Fintype.prod_equiv (efib f) _ _ (fun s => ?_)
  apply congrArg F
  apply Subtype.ext
  rfl

/-- A far edge is never the cut edge of any boundary cut (the cut edge touches `S`). -/
theorem far_ne_cutEdge (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)) (oEdge : ∀ f, s(oP f, oQ f) = f.1.1)
    (f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E})
    (E : {E : a.G.edgeSet // ¬ a.EdgeTouches S E}) : E.1 ≠ a.cutEdge (oAdj f) := by
  intro hc
  apply E.2
  have hEf : E.1 = f.1 := hc.trans (Subtype.ext (oEdge f))
  rw [hEf]; exact f.2.1

/-- **The far edges partition over the boundary subtrees.** For any commutative-monoid
weight `g`, the product over far edges is the product over per-subtree column edges. -/
theorem prod_edge_split {M : Type*} [CommMonoid M] (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)) (oEdge : ∀ f, s(oP f, oQ f) = f.1.1)
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    (oPart : ∀ y : a.V, y ∉ S → ∃! f, ¬ a.Side (oAdj f) y)
    (g : {E : a.G.edgeSet // ¬ a.EdgeTouches S E} → M) :
    (∏ E : {E : a.G.edgeSet // ¬ a.EdgeTouches S E}, g E)
      = ∏ f, ∏ e : {e : a.G.edgeSet // e ≠ a.cutEdge (oAdj f) ∧ ¬ a.EdgeSide (oAdj f) e},
          g ⟨e.1, a.bondcol_far S oP oQ oAdj oSide f e⟩ := by
  classical
  set emap : {E : a.G.edgeSet // ¬ a.EdgeTouches S E} →
      {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} :=
    fun E => (a.edgeSubtree_existsUnique S oP oQ oAdj oEdge oPart E).choose with hemap
  have hspec : ∀ E, ¬ a.EdgeSide (oAdj (emap E)) E.1 :=
    fun E => (a.edgeSubtree_existsUnique S oP oQ oAdj oEdge oPart E).choose_spec.1
  have huniq : ∀ E g', ¬ a.EdgeSide (oAdj g') E.1 → g' = emap E :=
    fun E g' hg => (a.edgeSubtree_existsUnique S oP oQ oAdj oEdge oPart E).choose_spec.2 g' hg
  let ecar : ∀ f, {E : {E : a.G.edgeSet // ¬ a.EdgeTouches S E} // emap E = f} ≃
      {e : a.G.edgeSet // e ≠ a.cutEdge (oAdj f) ∧ ¬ a.EdgeSide (oAdj f) e} :=
    fun f =>
    { toFun := fun E => ⟨E.1.1, a.far_ne_cutEdge S oP oQ oAdj oEdge f E.1,
        by have h := hspec E.1; rw [E.2] at h; exact h⟩
      invFun := fun e => ⟨⟨e.1, a.bondcol_far S oP oQ oAdj oSide f e⟩,
        (huniq ⟨e.1, a.bondcol_far S oP oQ oAdj oSide f e⟩ f e.2.2).symm⟩
      left_inv := fun E => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun e => by apply Subtype.ext; rfl }
  rw [← Equiv.prod_comp (Equiv.sigmaFiberEquiv emap) g, ← Finset.univ_sigma_univ,
    Finset.prod_sigma]
  refine Finset.prod_congr rfl (fun f _ => ?_)
  refine Fintype.prod_equiv (ecar f) _ _ (fun E => ?_)
  apply congrArg g
  apply Subtype.ext
  rfl

open Classical in
/-- **Reindex a sum over global far bonds as a sum over per-subtree column bonds.** The
restriction map (far bond ↦ its per-subtree restrictions) is a bijection (injective, and the
two finite types have equal cardinality by the far-edge partition). -/
theorem sum_farbond_reindex (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)) (oEdge : ∀ f, s(oP f, oQ f) = f.1.1)
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    (oPart : ∀ y : a.V, y ∉ S → ∃! f, ¬ a.Side (oAdj f) y)
    (H : ((f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}) →
      a.BondCol (oAdj f)) → ℝ) :
    (∑ bF : a.FarBond S, H (fun f e => bF ⟨e.1, a.bondcol_far S oP oQ oAdj oSide f e⟩))
      = ∑ bc, H bc := by
  classical
  set restr : a.FarBond S →
      ((f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}) → a.BondCol (oAdj f)) :=
    fun bF f e => bF ⟨e.1, a.bondcol_far S oP oQ oAdj oSide f e⟩ with hrestr
  set emap : {E : a.G.edgeSet // ¬ a.EdgeTouches S E} →
      {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} :=
    fun E => (a.edgeSubtree_existsUnique S oP oQ oAdj oEdge oPart E).choose with hemap
  have hspec : ∀ E, ¬ a.EdgeSide (oAdj (emap E)) E.1 :=
    fun E => (a.edgeSubtree_existsUnique S oP oQ oAdj oEdge oPart E).choose_spec.1
  have hinj : Function.Injective restr := by
    intro bF bF' hEq
    funext E
    exact congrFun (congrFun hEq (emap E))
      ⟨E.1, a.far_ne_cutEdge S oP oQ oAdj oEdge (emap E) E, hspec E⟩
  have hcard : Fintype.card (a.FarBond S)
      = Fintype.card ((f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}) →
          a.BondCol (oAdj f)) := by
    have e1 : Fintype.card (a.FarBond S)
        = ∏ E : {E : a.G.edgeSet // ¬ a.EdgeTouches S E}, a.r E.1.1 := by
      show Fintype.card ((E : {E : a.G.edgeSet // ¬ a.EdgeTouches S E}) → Fin (a.r E.1.1)) = _
      rw [Fintype.card_pi]; simp only [Fintype.card_fin]
    have e2 : Fintype.card ((f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}) →
          a.BondCol (oAdj f))
        = ∏ f, ∏ e : {e : a.G.edgeSet // e ≠ a.cutEdge (oAdj f) ∧ ¬ a.EdgeSide (oAdj f) e},
            a.r e.1.1 := by
      show Fintype.card ((f : _) → (e : {e : a.G.edgeSet //
          e ≠ a.cutEdge (oAdj f) ∧ ¬ a.EdgeSide (oAdj f) e}) → Fin (a.r e.1.1)) = _
      rw [Fintype.card_pi]
      refine Finset.prod_congr rfl (fun f _ => ?_)
      rw [Fintype.card_pi]; simp only [Fintype.card_fin]
    rw [e1, e2, a.prod_edge_split S oP oQ oAdj oEdge oSide oPart (fun E => a.r E.1.1)]
  have hbij : Function.Bijective restr :=
    (Fintype.bijective_iff_injective_and_card restr).mpr ⟨hinj, hcard⟩
  exact hbij.sum_comp H

/-- **The environment factors over the boundary subtrees.** -/
theorem envFactor_eq_prod_Hfun_aux (θ : a.Param) (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)) (oEdge : ∀ f, s(oP f, oQ f) = f.1.1)
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    (oPart : ∀ y : a.V, y ∉ S → ∃! f, ¬ a.Side (oAdj f) y)
    (β : a.BdryBond S) (xf : a.FarExtC S) :
    a.envFactor θ S β xf = ∏ f, a.Hfun (oAdj f) θ
      (fun z => xf ⟨z.1, oSide f z.1 z.2⟩)
      ((finCongr (congrArg a.r (oEdge f))).symm (β f)) := by
  classical
  -- per-vertex, per-edge bond matching: the environment slot dite equals the pinned
  -- `bondInvFun` reconstruction inside `Hfun`.
  have hterm : ∀ (bF : a.FarBond S)
      (f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E})
      (z : {z : a.V // ¬ a.Side (oAdj f) z}),
      θ z.1 (fun e => if h : a.EdgeTouches S ⟨e.1, e.2.1⟩
          then β ⟨⟨e.1, e.2.1⟩, h, fun hins => (oSide f z.1 z.2) (hins z.1 e.2.2)⟩
          else bF ⟨⟨e.1, e.2.1⟩, h⟩) (xf ⟨z.1, oSide f z.1 z.2⟩)
      = θ z.1 (Bond.restrict (a.bondInvFun (oAdj f)
          ((finCongr (congrArg a.r (oEdge f))).symm (β f), a.sideDefault (oAdj f),
            fun e => bF ⟨e.1, a.bondcol_far S oP oQ oAdj oSide f e⟩)) z.1)
          (xf ⟨z.1, oSide f z.1 z.2⟩) := by
    intro bF f z
    refine congrArg (fun bi => θ z.1 bi (xf ⟨z.1, oSide f z.1 z.2⟩)) ?_
    funext e
    set E : a.G.edgeSet := ⟨e.1, e.2.1⟩ with hE
    show (if h : a.EdgeTouches S E
        then β ⟨E, h, fun hins => (oSide f z.1 z.2) (hins z.1 e.2.2)⟩ else bF ⟨E, h⟩)
      = a.bondInvFun (oAdj f) (_, _, _) E
    simp only [bondInvFun]
    by_cases he : E = a.cutEdge (oAdj f)
    · have htouch : a.EdgeTouches S E := by
        rw [he, show a.cutEdge (oAdj f) = f.1 from Subtype.ext (oEdge f)]; exact f.2.1
      rw [dif_pos he, dif_pos htouch]
      exact (a.cut_slot_cast S oP oQ oAdj oEdge β f E he htouch
        (fun hins => (oSide f z.1 z.2) (hins z.1 e.2.2))).symm
    · rw [dif_neg he]
      by_cases hs : a.EdgeSide (oAdj f) E
      · exact absurd (hs z.1 e.2.2) z.2
      · rw [dif_neg hs, dif_neg (a.bondcol_far S oP oQ oAdj oSide f ⟨E, he, hs⟩)]
  -- factor each far-node product over the subtrees
  have hsummand : ∀ bF : a.FarBond S,
      (∏ y : {y : a.V // y ∉ S}, θ y.1 (fun e => if h : a.EdgeTouches S ⟨e.1, e.2.1⟩
          then β ⟨⟨e.1, e.2.1⟩, h, fun hins => y.2 (hins y.1 e.2.2)⟩
          else bF ⟨⟨e.1, e.2.1⟩, h⟩) (xf y))
      = ∏ f, ∏ z : {z : a.V // ¬ a.Side (oAdj f) z},
          θ z.1 (Bond.restrict (a.bondInvFun (oAdj f)
            ((finCongr (congrArg a.r (oEdge f))).symm (β f), a.sideDefault (oAdj f),
              fun e => bF ⟨e.1, a.bondcol_far S oP oQ oAdj oSide f e⟩)) z.1)
            (xf ⟨z.1, oSide f z.1 z.2⟩) := by
    intro bF
    rw [a.prod_far_split S oP oQ oAdj oSide oPart
      (fun y => θ y.1 (fun e => if h : a.EdgeTouches S ⟨e.1, e.2.1⟩
          then β ⟨⟨e.1, e.2.1⟩, h, fun hins => y.2 (hins y.1 e.2.2)⟩
          else bF ⟨⟨e.1, e.2.1⟩, h⟩) (xf y))]
    exact Finset.prod_congr rfl (fun f _ => Finset.prod_congr rfl (fun z _ => hterm bF f z))
  show (∑ bF : a.FarBond S, ∏ y : {y : a.V // y ∉ S},
      θ y.1 (fun e => if h : a.EdgeTouches S ⟨e.1, e.2.1⟩
          then β ⟨⟨e.1, e.2.1⟩, h, fun hins => y.2 (hins y.1 e.2.2)⟩
          else bF ⟨⟨e.1, e.2.1⟩, h⟩) (xf y)) = _
  rw [Finset.sum_congr rfl (fun bF _ => hsummand bF),
    a.sum_farbond_reindex S oP oQ oAdj oEdge oSide oPart
      (fun bc => ∏ f, ∏ z : {z : a.V // ¬ a.Side (oAdj f) z},
        θ z.1 (Bond.restrict (a.bondInvFun (oAdj f)
          ((finCongr (congrArg a.r (oEdge f))).symm (β f), a.sideDefault (oAdj f), bc f)) z.1)
          (xf ⟨z.1, oSide f z.1 z.2⟩)),
    ← prod_univ_sum_pi (fun f bc => ∏ z : {z : a.V // ¬ a.Side (oAdj f) z},
      θ z.1 (Bond.restrict (a.bondInvFun (oAdj f)
        ((finCongr (congrArg a.r (oEdge f))).symm (β f), a.sideDefault (oAdj f), bc)) z.1)
        (xf ⟨z.1, oSide f z.1 z.2⟩))]
  rfl

/-- **Grouped contraction (master Fubini)**: the represented tensor is the S-core paired
with the per-boundary-subtree column factors. -/
theorem represented_eq_sum_SCore (θ : a.Param) (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)) (oEdge : ∀ f, s(oP f, oQ f) = f.1.1)
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    (oPart : ∀ y : a.V, y ∉ S → ∃! f, ¬ a.Side (oAdj f) y)
    (x : a.Ext) :
    a.represented θ x = ∑ β : a.BdryBond S,
      a.SCore θ S (fun v => x v.1) β
        * ∏ f, a.Hfun (oAdj f) θ (fun z => x z.1)
            ((finCongr (congrArg a.r (oEdge f))).symm (β f)) := by
  rw [represented_eq_sum_SCore_mul_envFactor θ S x]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [envFactor_eq_prod_Hfun_aux θ S oP oQ oAdj oEdge oSide oPart β (fun y => x y.1)]

/-- **The environment factors over the boundary subtrees** (each subtree's pinned
contraction is a `Hfun` column factor of the current point). -/
theorem envFactor_eq_prod_Hfun (θ : a.Param) (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)) (oEdge : ∀ f, s(oP f, oQ f) = f.1.1)
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    (oPart : ∀ y : a.V, y ∉ S → ∃! f, ¬ a.Side (oAdj f) y)
    (β : a.BdryBond S) (xf : a.FarExtC S) :
    a.envFactor θ S β xf = ∏ f, a.Hfun (oAdj f) θ
      (fun z => xf ⟨z.1, oSide f z.1 z.2⟩)
      ((finCongr (congrArg a.r (oEdge f))).symm (β f)) :=
  envFactor_eq_prod_Hfun_aux θ S oP oQ oAdj oEdge oSide oPart β xf

/-- The finite Kronecker product of a family of square matrices, as a matrix on the
dependent product of the index types. -/
noncomputable def piKron {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (M : (i : ι) → Matrix (Fin (d i)) (Fin (d i)) ℝ) :
    Matrix ((i : ι) → Fin (d i)) ((i : ι) → Fin (d i)) ℝ :=
  fun β γ => ∏ i, M i (β i) (γ i)

theorem piKron_mul_piKron {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}
    (M N : (i : ι) → Matrix (Fin (d i)) (Fin (d i)) ℝ) :
    piKron M * piKron N = piKron (fun i => M i * N i) := by
  classical
  ext β γ
  rw [Matrix.mul_apply]
  simp only [piKron]
  rw [Finset.sum_congr rfl (fun δ _ => (Finset.prod_mul_distrib
    (f := fun i => M i (β i) (δ i)) (g := fun i => N i (δ i) (γ i))).symm)]
  rw [sum_pi_prod (fun i => d i) (fun i k => M i (β i) k * N i k (γ i))]
  exact Finset.prod_congr rfl (fun i _ => (Matrix.mul_apply).symm)

theorem piKron_one {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ} :
    piKron (fun i : ι => (1 : Matrix (Fin (d i)) (Fin (d i)) ℝ)) = 1 := by
  classical
  ext β γ
  simp only [piKron]
  rw [Matrix.one_apply]
  by_cases hβγ : β = γ
  · subst hβγ
    rw [if_pos rfl]
    exact Finset.prod_eq_one (fun i _ => Matrix.one_apply_eq _)
  · rw [if_neg hβγ]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hβγ
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)

theorem isUnit_piKron {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}
    {M : (i : ι) → Matrix (Fin (d i)) (Fin (d i)) ℝ} (hM : ∀ i, IsUnit (M i)) :
    IsUnit (piKron M) := by
  classical
  choose u hu using hM
  refine ⟨⟨piKron M, piKron (fun i => (↑(u i)⁻¹ : Matrix (Fin (d i)) (Fin (d i)) ℝ)), ?_, ?_⟩, rfl⟩
  · rw [piKron_mul_piKron, show (fun i => M i * (↑(u i)⁻¹ : Matrix (Fin (d i)) (Fin (d i)) ℝ))
        = (fun i => (1 : Matrix (Fin (d i)) (Fin (d i)) ℝ)) from
      funext fun i => by rw [← hu i]; exact (u i).mul_inv, piKron_one]
  · rw [piKron_mul_piKron, show (fun i => (↑(u i)⁻¹ : Matrix (Fin (d i)) (Fin (d i)) ℝ) * M i)
        = (fun i => (1 : Matrix (Fin (d i)) (Fin (d i)) ℝ)) from
      funext fun i => by rw [← hu i]; exact (u i).inv_mul, piKron_one]


/-! ### Orientation and partition providers and the rank chain

The final result is `exists_envPair_ne_zero`. -/

/-- **(G1) One-sidedness from component connectivity**: a non-`K` edge with an endpoint in
`S` has ALL of `S` on that endpoint's side. -/
theorem side_all_of_hconn (S : Finset a.V) (K : Finset a.G.edgeSet)
    (hKiff : ∀ E : a.G.edgeSet, E ∈ K ↔ a.EdgeInside S E)
    (hconn : ∀ P ⊆ S, P.Nonempty → P ≠ S →
      ∃ (y z : a.V) (hyz : a.G.Adj y z), y ∉ P ∧ z ∈ P ∧
        (⟨s(y, z), by rw [SimpleGraph.mem_edgeSet]; exact hyz⟩ : a.G.edgeSet) ∈ K)
    {p q : a.V} (hpq : a.G.Adj p q) (hpS : p ∈ S)
    (hnK : (⟨s(p, q), by rw [SimpleGraph.mem_edgeSet]; exact hpq⟩ : a.G.edgeSet) ∉ K)
    {s : a.V} (hs : s ∈ S) : a.Side hpq s := by
  classical
  set P : Finset a.V := S.filter (fun s => a.Side hpq s) with hPdef
  have hpP : p ∈ P := by
    rw [hPdef, Finset.mem_filter]; exact ⟨hpS, a.side_left hpq⟩
  by_cases hPS : P = S
  · have : s ∈ P := by rw [hPS]; exact hs
    rw [hPdef, Finset.mem_filter] at this; exact this.2
  · exfalso
    obtain ⟨y, z, hyz, hyP, hzP, hKmem⟩ := hconn P (Finset.filter_subset _ _) ⟨p, hpP⟩ hPS
    -- z on the side (from filter membership)
    have hSz : a.Side hpq z := (Finset.mem_filter.mp hzP).2
    -- y is inside S (K-edge is EdgeInside), but y ∉ P, so y is off the side
    have hyS : y ∈ S := by
      have hin : a.EdgeInside S ⟨s(y, z), by rw [SimpleGraph.mem_edgeSet]; exact hyz⟩ :=
        (hKiff _).mp hKmem
      exact hin y (Sym2.mem_mk_left y z)
    have hnSy : ¬ a.Side hpq y := fun hSy => hyP (Finset.mem_filter.mpr ⟨hyS, hSy⟩)
    -- an edge with endpoints on opposite sides must be the cut edge
    have hedgeeq : s(y, z) = s(p, q) := by
      by_contra hne
      exact hnSy ((a.side_iff_of_adj hpq hyz hne).mpr hSz)
    have heq : (⟨s(y, z), by rw [SimpleGraph.mem_edgeSet]; exact hyz⟩ : a.G.edgeSet)
        = ⟨s(p, q), by rw [SimpleGraph.mem_edgeSet]; exact hpq⟩ := Subtype.ext hedgeeq
    exact hnK (heq ▸ hKmem)

/-- **(G0) The boundary orientation family**: every boundary edge is oriented with its
`S`-endpoint first, and the whole component lies on the near side. -/
theorem exists_boundary_orientation (S : Finset a.V) (K : Finset a.G.edgeSet)
    (hKiff : ∀ E : a.G.edgeSet, E ∈ K ↔ a.EdgeInside S E)
    (hconn : ∀ P ⊆ S, P.Nonempty → P ≠ S →
      ∃ (y z : a.V) (hyz : a.G.Adj y z), y ∉ P ∧ z ∈ P ∧
        (⟨s(y, z), by rw [SimpleGraph.mem_edgeSet]; exact hyz⟩ : a.G.edgeSet) ∈ K) :
    ∃ (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
      (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)),
      (∀ f, s(oP f, oQ f) = f.1.1) ∧ (∀ f, oP f ∈ S) ∧ (∀ f, oQ f ∉ S) ∧
      (∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S) := by
  classical
  have key : ∀ f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E},
      ∃ p q, ∃ (_ : a.G.Adj p q), s(p, q) = f.1.1 ∧ p ∈ S ∧ q ∉ S := by
    intro f
    obtain ⟨⟨ed, hed⟩, htouch, hninside⟩ := f
    induction ed using Sym2.ind with
    | _ c d =>
      have hadj : a.G.Adj c d := by rwa [SimpleGraph.mem_edgeSet] at hed
      by_cases hc : c ∈ S
      · by_cases hd : d ∈ S
        · exact absurd (fun v hv => by
            rcases Sym2.mem_iff.mp hv with rfl | rfl; exacts [hc, hd]) hninside
        · exact ⟨c, d, hadj, rfl, hc, hd⟩
      · by_cases hd : d ∈ S
        · exact ⟨d, c, hadj.symm, Sym2.eq_swap, hd, hc⟩
        · exact absurd (by
            obtain ⟨v, hv, hvS⟩ := htouch
            rcases Sym2.mem_iff.mp hv with rfl | rfl; exacts [hc hvS, hd hvS]) not_false
  choose oP oQ oAdj oEdge oPS oQS using key
  refine ⟨oP, oQ, oAdj, oEdge, oPS, oQS, ?_⟩
  intro f z hns
  by_contra hzS
  refine hns (a.side_all_of_hconn S K hKiff hconn (oAdj f) (oPS f) ?_ hzS)
  intro hmem
  refine f.2.2 ((hKiff f.1).mp ?_)
  have heq : (⟨s(oP f, oQ f), by rw [SimpleGraph.mem_edgeSet]; exact oAdj f⟩ : a.G.edgeSet)
      = f.1 := Subtype.ext (oEdge f)
  exact heq ▸ hmem

/-- **(G2) The subtree partition**: every far vertex lies behind exactly one boundary
edge. -/
theorem existsUnique_not_side (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)) (oEdge : ∀ f, s(oP f, oQ f) = f.1.1)
    (oPS : ∀ f, oP f ∈ S) (oQS : ∀ f, oQ f ∉ S)
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    (hS : S.Nonempty) {y : a.V} (hy : y ∉ S) :
    ∃! f, ¬ a.Side (oAdj f) y := by
  classical
  -- A walk from a non-`S` vertex to an `S` vertex has a first boundary crossing.
  have aux : ∀ {u v : a.V} (p : a.G.Walk u v), u ∉ S → v ∈ S →
      ∃ b c, ∃ (_ : a.G.Adj b c) (pre : a.G.Walk u b),
        b ∉ S ∧ c ∈ S ∧ s(b, c) ∉ pre.edges ∧ ∀ x ∈ pre.support, x ∉ S := by
    intro u v p
    induction p with
    | nil => intro h1 h2; exact absurd h2 h1
    | @cons u' m v' hadj q ih =>
      intro huS hvS
      by_cases hmS : m ∈ S
      · refine ⟨u', m, hadj, SimpleGraph.Walk.nil, huS, hmS, by simp, ?_⟩
        intro x hx
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
        subst hx; exact huS
      · obtain ⟨b, c, hbc, pre, hbS, hcS, hpre_e, hpre_s⟩ := ih hmS hvS
        refine ⟨b, c, hbc, SimpleGraph.Walk.cons hadj pre, hbS, hcS, ?_, ?_⟩
        · rw [SimpleGraph.Walk.edges_cons]
          intro hmem
          rcases List.mem_cons.mp hmem with h1 | h2
          · have hc_in : c ∈ s(u', m) := h1 ▸ Sym2.mem_mk_right b c
            rcases Sym2.mem_iff.mp hc_in with rfl | rfl
            · exact huS hcS
            · exact hmS hcS
          · exact hpre_e h2
        · intro x hx
          rw [SimpleGraph.Walk.support_cons] at hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact huS
          · exact hpre_s x hx
  -- A walk from an off-side vertex to an on-side vertex must contain the cut edge.
  have crossing : ∀ {p q x' y' : a.V} (h : a.G.Adj p q) (W : a.G.Walk x' y'),
      ¬ a.Side h x' → a.Side h y' → s(p, q) ∈ W.edges := by
    intro p q x' y' h W
    induction W with
    | nil => intro hx hy'; exact absurd hy' hx
    | @cons x'' m y'' hadj W' ih =>
      intro hx hy'
      by_cases he : s(x'', m) = s(p, q)
      · rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons.mpr (Or.inl he.symm)
      · have hmoff : ¬ a.Side h m := fun hm => hx ((a.side_iff_of_adj h hadj he).mpr hm)
        rw [SimpleGraph.Walk.edges_cons]
        exact List.mem_cons.mpr (Or.inr (ih hmoff hy'))
  -- Uniqueness: two boundary edges behind `y` coincide.
  have uniq : ∀ (f₁ f₂ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}),
      ¬ a.Side (oAdj f₁) y → ¬ a.Side (oAdj f₂) y → f₁ = f₂ := by
    intro f₁ f₂ hf₁ hf₂
    by_contra hne
    have reach2 : (a.G.deleteEdges {s(oQ f₂, oP f₂)}).Reachable (oQ f₂) y :=
      (a.side_symm_iff_not_side (oAdj f₂) y).mpr hf₂
    obtain ⟨W₀⟩ := reach2.symm
    have hsub2 : ∀ e ∈ W₀.edges, e ∈ a.G.edgeSet := by
      intro e he
      have hh := W₀.edges_subset_edgeSet he
      rw [SimpleGraph.edgeSet_deleteEdges] at hh; exact hh.1
    have hf1q : ¬ a.Side (oAdj f₁) (oQ f₂) := by
      intro hcon
      have hmem' : s(oP f₁, oQ f₁) ∈ (W₀.transfer a.G hsub2).edges :=
        crossing (oAdj f₁) (W₀.transfer a.G hsub2) hf₁ hcon
      have hin : oP f₁ ∈ W₀.support := by
        have hh := (W₀.transfer a.G hsub2).fst_mem_support_of_mem_edges hmem'
        rwa [SimpleGraph.Walk.support_transfer] at hh
      have reachy : (a.G.deleteEdges {s(oQ f₂, oP f₂)}).Reachable y (oP f₁) :=
        (W₀.takeUntil (oP f₁) hin).reachable
      have hreachP : (a.G.deleteEdges {s(oQ f₂, oP f₂)}).Reachable (oQ f₂) (oP f₁) :=
        reach2.trans reachy
      have hoffP : ¬ a.Side (oAdj f₂) (oP f₁) :=
        (a.side_symm_iff_not_side (oAdj f₂) (oP f₁)).mp hreachP
      exact (oSide f₂ (oP f₁) hoffP) (oPS f₁)
    have hf1p2 : a.Side (oAdj f₁) (oP f₂) := by
      by_contra hc; exact (oSide f₁ (oP f₂) hc) (oPS f₂)
    have hedge : s(oP f₂, oQ f₂) = s(oP f₁, oQ f₁) := by
      by_contra hne'
      exact hf1q ((a.side_iff_of_adj (oAdj f₁) (oAdj f₂) hne').mp hf1p2)
    apply hne
    apply Subtype.ext; apply Subtype.ext
    rw [← oEdge f₁, ← oEdge f₂]; exact hedge.symm
  -- Existence
  obtain ⟨s₀, hs₀⟩ := hS
  obtain ⟨Wex⟩ := a.hT.connected.preconnected y s₀
  obtain ⟨b, c, hbc, pre, hbS, hcS, hpre_e, hpre_s⟩ := aux Wex hy hs₀
  have hbcmem : s(b, c) ∈ a.G.edgeSet := by rw [SimpleGraph.mem_edgeSet]; exact hbc
  set f₀ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} :=
    ⟨⟨s(b, c), hbcmem⟩, ⟨c, Sym2.mem_mk_right b c, hcS⟩,
      fun hin => hbS (hin b (Sym2.mem_mk_left b c))⟩ with hf₀def
  have hEdge₀ : s(oP f₀, oQ f₀) = s(b, c) := oEdge f₀
  have horient : oP f₀ = c ∧ oQ f₀ = b := by
    rcases Sym2.eq_iff.mp hEdge₀ with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact absurd (h1 ▸ oPS f₀) hbS
    · exact ⟨h1, h2⟩
  obtain ⟨hoP, hoQ⟩ := horient
  have hy_behind_f₀ : ¬ a.Side (oAdj f₀) y := by
    have hpre_avoid : s(oP f₀, oQ f₀) ∉ pre.edges := by rw [hEdge₀]; exact hpre_e
    have hiff := a.side_iff_of_walk_avoiding (oAdj f₀) pre hpre_avoid
    have hnb : ¬ a.Side (oAdj f₀) b :=
      (congrArg (a.Side (oAdj f₀)) hoQ) ▸ a.not_side_right (oAdj f₀)
    exact fun hyy => hnb (hiff.mp hyy)
  exact ⟨f₀, hy_behind_f₀, fun g hg => uniq g f₀ hg hy_behind_f₀⟩

/-- **(G3) Subtrees inherit the `e*`-side of their far endpoint**: everything behind a
boundary cut (all of `S` on the near side, `xs ∈ S`) is on the same `e*`-side as the far
endpoint `q`. -/
theorem side_hstar_iff_of_behind {xs ys : a.V} (hstar : a.G.Adj xs ys) {S : Finset a.V}
    (hxsS : xs ∈ S) {p q : a.V} (hpq : a.G.Adj p q)
    (hSside : ∀ s ∈ S, a.Side hpq s)
    {z : a.V} (hz : ¬ a.Side hpq z) : (a.Side hstar z ↔ a.Side hstar q) := by
  classical
  have hDz : (a.G.deleteEdges {s(p, q)}).Reachable q z := by
    have hz' : (a.G.deleteEdges {s(q, p)}).Reachable q z :=
      (a.side_symm_iff_not_side hpq z).mpr hz
    rwa [Sym2.eq_swap] at hz'
  obtain ⟨W₀⟩ := hDz
  have hsub : ∀ e ∈ W₀.edges, e ∈ a.G.edgeSet := by
    intro e he
    have hh := W₀.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_deleteEdges] at hh
    exact hh.1
  have havoid : s(xs, ys) ∉ (W₀.transfer a.G hsub).edges := by
    rw [SimpleGraph.Walk.edges_transfer]
    intro hmem
    have hxs_supp : xs ∈ W₀.support := W₀.fst_mem_support_of_mem_edges hmem
    have hreach : (a.G.deleteEdges {s(p, q)}).Reachable q xs :=
      (W₀.takeUntil xs hxs_supp).reachable
    have hxsoff : ¬ a.Side hpq xs := by
      have h2 : (a.G.deleteEdges {s(q, p)}).Reachable q xs := by rwa [Sym2.eq_swap]
      exact (a.side_symm_iff_not_side hpq xs).mp h2
    exact hxsoff (hSside xs hxsS)
  exact (a.side_iff_of_walk_avoiding hstar (W₀.transfer a.G hsub) havoid).symm

open Classical in
/-- The environment pairing of a tensor `represented W` against the `θ`-environment. -/
noncomputable def envPaired (W θ : a.Param) (S : Finset a.V) (ξ : a.SExtC S)
    (β : a.BdryBond S) : ℝ :=
  ∑ xf : a.FarExtC S,
    a.represented W ((Equiv.piEquivPiSubtypeProd (fun v : a.V => v ∈ S)
      (fun v => Fin (a.n v))).symm (ξ, xf)) * a.envFactor θ S β xf

/-- The S-core as a matrix over `(ξ, β)`. -/
noncomputable def SCoreMat (W : a.Param) (S : Finset a.V) :
    Matrix (a.SExtC S) (a.BdryBond S) ℝ := fun ξ β => a.SCore W S ξ β

/-- The environment pairing as a matrix over `(ξ, β)`. -/
noncomputable def envPairedMat (W θ : a.Param) (S : Finset a.V) :
    Matrix (a.SExtC S) (a.BdryBond S) ℝ := fun ξ β => a.envPaired W θ S ξ β

/-- The per-boundary-edge cross-Gram `(H_f^W)ᵀ · H_f^θ`, transported onto the edge's own
bond index. -/
noncomputable def bdryGram (W θ : a.Param) (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)) (oEdge : ∀ f, s(oP f, oQ f) = f.1.1)
    (f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}) :
    Matrix (Fin (a.r f.1.1)) (Fin (a.r f.1.1)) ℝ :=
  fun i j => ((a.Hfun (oAdj f) W)ᵀ * a.Hfun (oAdj f) θ)
    ((finCongr (congrArg a.r (oEdge f))).symm i) ((finCongr (congrArg a.r (oEdge f))).symm j)

/-- The Kronecker product of the boundary cross-Grams, typed at the boundary bond
coordinates. -/
noncomputable def bdryKron (W θ : a.Param) (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)) (oEdge : ∀ f, s(oP f, oQ f) = f.1.1) :
    Matrix (a.BdryBond S) (a.BdryBond S) ℝ :=
  piKron (a.bdryGram W θ S oP oQ oAdj oEdge)

open Classical in
/-- **Reindex a sum over far externals as a sum over per-subtree column coordinates.** The
restriction map (far external ↦ its per-subtree restrictions) is a bijection (injective, and
equal cardinality by the far-vertex partition). -/
theorem sum_farext_reindex (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f))
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    (oPart : ∀ y : a.V, y ∉ S → ∃! f, ¬ a.Side (oAdj f) y)
    (H : ((f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}) →
      a.Col (oAdj f)) → ℝ) :
    (∑ xf : a.FarExtC S, H (fun f z => xf ⟨z.1, oSide f z.1 z.2⟩)) = ∑ c, H c := by
  classical
  set restr : a.FarExtC S →
      ((f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}) → a.Col (oAdj f)) :=
    fun xf f z => xf ⟨z.1, oSide f z.1 z.2⟩ with hrestr
  set vmap : {y : a.V // y ∉ S} →
      {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} :=
    fun y => (oPart y.1 y.2).choose with hvmap
  have hspec : ∀ y, ¬ a.Side (oAdj (vmap y)) y.1 := fun y => (oPart y.1 y.2).choose_spec.1
  have hinj : Function.Injective restr := by
    intro xf xf' hEq
    funext y
    exact congrFun (congrFun hEq (vmap y)) ⟨y.1, hspec y⟩
  have hcard : Fintype.card (a.FarExtC S)
      = Fintype.card ((f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}) →
          a.Col (oAdj f)) := by
    have hR : (∏ y : {y : a.V // y ∉ S}, (a.n y.1 : ℝ))
        = ∏ f, ∏ z : {z : a.V // ¬ a.Side (oAdj f) z}, (a.n (⟨z.1, oSide f z.1 z.2⟩ :
            {y : a.V // y ∉ S}).1 : ℝ) :=
      a.prod_far_split S oP oQ oAdj oSide oPart (fun y => (a.n y.1 : ℝ))
    have hN : (∏ y : {y : a.V // y ∉ S}, a.n y.1)
        = ∏ f, ∏ z : {z : a.V // ¬ a.Side (oAdj f) z}, a.n z.1 := by exact_mod_cast hR
    have e1 : Fintype.card (a.FarExtC S) = ∏ y : {y : a.V // y ∉ S}, a.n y.1 := by
      show Fintype.card ((y : {y : a.V // y ∉ S}) → Fin (a.n y.1)) = _
      rw [Fintype.card_pi]; simp only [Fintype.card_fin]
    have e2 : Fintype.card ((f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}) →
          a.Col (oAdj f))
        = ∏ f, ∏ z : {z : a.V // ¬ a.Side (oAdj f) z}, a.n z.1 := by
      show Fintype.card ((f : _) → (z : {z : a.V // ¬ a.Side (oAdj f) z}) → Fin (a.n z.1)) = _
      rw [Fintype.card_pi]
      refine Finset.prod_congr rfl (fun f _ => ?_)
      rw [Fintype.card_pi]; simp only [Fintype.card_fin]
    rw [e1, e2, hN]
  have hbij : Function.Bijective restr :=
    (Fintype.bijective_iff_injective_and_card restr).mpr ⟨hinj, hcard⟩
  exact hbij.sum_comp H

/-- **(C1) The pairing matrix is the S-core matrix times the Kronecker product of the
cross-Grams.** -/
theorem envPairedMat_eq_SCoreMat_mul_piKron (W θ : a.Param) (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)) (oEdge : ∀ f, s(oP f, oQ f) = f.1.1)
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    (oPart : ∀ y : a.V, y ∉ S → ∃! f, ¬ a.Side (oAdj f) y) :
    a.envPairedMat W θ S
      = a.SCoreMat W S * a.bdryKron W θ S oP oQ oAdj oEdge := by
  classical
  ext ξ γ
  set e := Equiv.piEquivPiSubtypeProd (fun v : a.V => v ∈ S) (fun v => Fin (a.n v)) with he
  have hSv : ∀ (xf : a.FarExtC S) (v : {v : a.V // v ∈ S}), (e.symm (ξ, xf)) v.1 = ξ v := by
    intro xf v
    show (if h : v.1 ∈ S then (ξ, xf).1 ⟨v.1, h⟩ else (ξ, xf).2 ⟨v.1, h⟩) = ξ v
    exact (dif_pos v.2).trans rfl
  have hFy : ∀ (xf : a.FarExtC S) (y : {y : a.V // y ∉ S}), (e.symm (ξ, xf)) y.1 = xf y := by
    intro xf y
    show (if h : y.1 ∈ S then (ξ, xf).1 ⟨y.1, h⟩ else (ξ, xf).2 ⟨y.1, h⟩) = xf y
    exact (dif_neg y.2).trans rfl
  have hsummand : ∀ xf : a.FarExtC S,
      a.represented W (e.symm (ξ, xf)) * a.envFactor θ S γ xf
      = ∑ β' : a.BdryBond S, a.SCore W S ξ β'
          * ∏ f, (a.Hfun (oAdj f) W (fun z => xf ⟨z.1, oSide f z.1 z.2⟩)
                ((finCongr (congrArg a.r (oEdge f))).symm (β' f))
              * a.Hfun (oAdj f) θ (fun z => xf ⟨z.1, oSide f z.1 z.2⟩)
                ((finCongr (congrArg a.r (oEdge f))).symm (γ f))) := by
    intro xf
    rw [a.represented_eq_sum_SCore W S oP oQ oAdj oEdge oSide oPart (e.symm (ξ, xf)),
        a.envFactor_eq_prod_Hfun θ S oP oQ oAdj oEdge oSide oPart γ xf, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun β' _ => ?_)
    have hξ : (fun v : {v : a.V // v ∈ S} => (e.symm (ξ, xf)) v.1) = ξ := funext (hSv xf)
    have harg : ∀ f, (fun z : {z : a.V // ¬ a.Side (oAdj f) z} => (e.symm (ξ, xf)) z.1)
        = (fun z : {z : a.V // ¬ a.Side (oAdj f) z} => xf ⟨z.1, oSide f z.1 z.2⟩) :=
      fun f => funext (fun z : {z : a.V // ¬ a.Side (oAdj f) z} =>
        hFy xf ⟨z.1, oSide f z.1 z.2⟩)
    have hWprod : (∏ f, a.Hfun (oAdj f) W (fun z => (e.symm (ξ, xf)) z.1)
          ((finCongr (congrArg a.r (oEdge f))).symm (β' f)))
        = ∏ f, a.Hfun (oAdj f) W (fun z => xf ⟨z.1, oSide f z.1 z.2⟩)
          ((finCongr (congrArg a.r (oEdge f))).symm (β' f)) :=
      Finset.prod_congr rfl (fun f _ => by rw [harg f])
    rw [hξ, hWprod, mul_assoc, ← Finset.prod_mul_distrib]
  show (∑ xf : a.FarExtC S, a.represented W (e.symm (ξ, xf)) * a.envFactor θ S γ xf)
    = (a.SCoreMat W S * a.bdryKron W θ S oP oQ oAdj oEdge) ξ γ
  rw [Matrix.mul_apply, Finset.sum_congr rfl (fun xf _ => hsummand xf), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun β' _ => ?_)
  rw [← Finset.mul_sum]
  show a.SCore W S ξ β' * _ = a.SCore W S ξ β' * a.bdryKron W θ S oP oQ oAdj oEdge β' γ
  congr 1
  rw [a.sum_farext_reindex S oP oQ oAdj oSide oPart
      (fun c => ∏ f, (a.Hfun (oAdj f) W (c f) ((finCongr (congrArg a.r (oEdge f))).symm (β' f))
        * a.Hfun (oAdj f) θ (c f) ((finCongr (congrArg a.r (oEdge f))).symm (γ f)))),
    ← prod_univ_sum_pi (fun f c => a.Hfun (oAdj f) W c
        ((finCongr (congrArg a.r (oEdge f))).symm (β' f))
      * a.Hfun (oAdj f) θ c ((finCongr (congrArg a.r (oEdge f))).symm (γ f)))]
  show (∏ f, ∑ c : a.Col (oAdj f), _) = a.bdryKron W θ S oP oQ oAdj oEdge β' γ
  show _ = ∏ f, a.bdryGram W θ S oP oQ oAdj oEdge f (β' f) (γ f)
  refine Finset.prod_congr rfl (fun f _ => ?_)
  show (∑ c : a.Col (oAdj f), _)
    = ((a.Hfun (oAdj f) W)ᵀ * a.Hfun (oAdj f) θ)
        ((finCongr (congrArg a.r (oEdge f))).symm (β' f))
        ((finCongr (congrArg a.r (oEdge f))).symm (γ f))
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl (fun c _ => by rw [Matrix.transpose_apply])

/-- **(C2) The cross-Grams are invertible** at a min-norm critical point whose boundary
edges have full model rank. -/
theorem isUnit_bdryGram {Tstar : a.Ext → ℝ} {θ θs : a.Param} (hmn : a.MinNorm θ)
    (hcrit : a.Critical Tstar θ) (hts : a.represented θs = Tstar)
    (S : Finset a.V) (K : Finset a.G.edgeSet)
    (hKiff : ∀ E : a.G.edgeSet, E ∈ K ↔ a.EdgeInside S E)
    (hbdry : ∀ E : a.G.edgeSet, E ∉ K → ∀ (u w : a.V) (h : a.G.Adj u w), s(u, w) = E.1 →
      u ∈ S → (a.matricize h θ).rank = a.r s(u, w))
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)) (oEdge : ∀ f, s(oP f, oQ f) = f.1.1)
    (oPS : ∀ f, oP f ∈ S)
    (f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}) :
    IsUnit (a.bdryGram θs θ S oP oQ oAdj oEdge f) := by
  have hnK : f.1 ∉ K := fun hmem => f.2.2 ((hKiff f.1).mp hmem)
  have hfull : (a.matricize (oAdj f) θ).rank = a.r s(oP f, oQ f) :=
    hbdry f.1 hnK (oP f) (oQ f) (oAdj f) (oEdge f) (oPS f)
  have hFH : a.matricizeOf (oAdj f) Tstar
      = a.Ffun (oAdj f) θs * (a.Hfun (oAdj f) θs)ᵀ := by
    rw [← hts, ← a.matricize_eq_matricizeOf (oAdj f) θs]
    exact a.matricize_FH (oAdj f) θs
  have hunit : IsUnit ((a.Hfun (oAdj f) θs)ᵀ * a.Hfun (oAdj f) θ) :=
    a.minNorm_critical_isUnit_crossGram hmn hcrit (oAdj f) hFH hfull
  have hsub : a.bdryGram θs θ S oP oQ oAdj oEdge f
      = ((a.Hfun (oAdj f) θs)ᵀ * a.Hfun (oAdj f) θ).submatrix
          (finCongr (congrArg a.r (oEdge f))).symm
          (finCongr (congrArg a.r (oEdge f))).symm := rfl
  rw [hsub, Matrix.isUnit_iff_isUnit_det, Matrix.det_submatrix_equiv_self,
    ← Matrix.isUnit_iff_isUnit_det]
  exact hunit

/-- **Generic reshape along two product splittings.** Given `eR : R ≃ R₁ × R₂` and
`eC : C ≃ C₁ × C₂`, regroup a matrix `Matrix R C` into a matrix whose rows are indexed by
`R₁ × C₁` and columns by `R₂ × C₂`. This is the abstract `sideSplit` used in the rank
comparison below; the two splittings refine the `S`-external coordinates and boundary bonds
along the `e*` cut. -/
def reshapeSplit {R C R₁ R₂ C₁ C₂ : Type*}
    (eR : R ≃ R₁ × R₂) (eC : C ≃ C₁ × C₂) (M : Matrix R C ℝ) :
    Matrix (R₁ × C₁) (R₂ × C₂) ℝ :=
  fun p q => M (eR.symm (p.1, q.1)) (eC.symm (p.2, q.2))

/-- Rank sandwich: `rank (P · M · Qᵀ) ≤ rank M`. -/
theorem rank_mul_mul_transpose_le {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂]
    [Fintype n₁] [Fintype n₂] (P : Matrix m₁ n₁ ℝ) (M : Matrix n₁ n₂ ℝ) (Q : Matrix m₂ n₂ ℝ) :
    (P * M * Qᵀ).rank ≤ M.rank := by
  calc (P * M * Qᵀ).rank ≤ (P * M).rank := Matrix.rank_mul_le_left _ _
    _ ≤ M.rank := Matrix.rank_mul_le_right _ _

/-- **Identity-Kronecker**: the block matrix `1 ⊗ B` on `I × J`. -/
def idKron {I J : Type*} [DecidableEq I] (B : Matrix J J ℝ) : Matrix (I × J) (I × J) ℝ :=
  fun p q => (if p.1 = q.1 then (1 : ℝ) else 0) * B p.2 q.2

theorem idKron_mul_idKron {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (B C : Matrix J J ℝ) : (idKron B : Matrix (I × J) (I × J) ℝ) * idKron C = idKron (B * C) := by
  ext p q
  simp only [idKron, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single p.1]
  · rw [if_pos rfl]; ring
  · intro i _ hi
    rw [if_neg (fun h => hi h.symm)]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

theorem idKron_one {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J] :
    (idKron (1 : Matrix J J ℝ) : Matrix (I × J) (I × J) ℝ) = 1 := by
  ext p q
  simp only [idKron, Matrix.one_apply]
  by_cases h1 : p.1 = q.1
  · by_cases h2 : p.2 = q.2
    · rw [if_pos h1, if_pos h2, one_mul, if_pos (Prod.ext h1 h2)]
    · rw [if_pos h1, if_neg h2, mul_zero, if_neg (fun h => h2 (congrArg Prod.snd h))]
  · rw [if_neg h1, zero_mul, if_neg (fun h => h1 (congrArg Prod.fst h))]

theorem isUnit_idKron {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {B : Matrix J J ℝ} (hB : IsUnit B) : IsUnit (idKron B : Matrix (I × J) (I × J) ℝ) := by
  obtain ⟨u, hu⟩ := hB
  refine ⟨⟨idKron B, idKron (↑u⁻¹ : Matrix J J ℝ), ?_, ?_⟩, rfl⟩
  · rw [idKron_mul_idKron, ← hu, u.mul_inv, idKron_one]
  · rw [idKron_mul_idKron, ← hu, u.inv_mul, idKron_one]

/-- Transpose preserves invertibility. -/
theorem isUnit_transpose {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix m m ℝ}
    (hM : IsUnit M) : IsUnit Mᵀ := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose,
    ← Matrix.isUnit_iff_isUnit_det]
  exact hM

/-- **The boundary Kronecker product splits along a side predicate.** Reconstructing both
bond arguments from side-split coordinates, `piKron` factors as a product of the two
sub-family Kronecker products. -/
theorem piKron_symm_split {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    {d : ι → ℕ} (M : (i : ι) → Matrix (Fin (d i)) (Fin (d i)) ℝ)
    (βr γr : (i : {i // p i}) → Fin (d i.1)) (βc γc : (i : {i // ¬ p i}) → Fin (d i.1)) :
    piKron M ((Equiv.piEquivPiSubtypeProd p (fun i => Fin (d i))).symm (βr, βc))
        ((Equiv.piEquivPiSubtypeProd p (fun i => Fin (d i))).symm (γr, γc))
      = piKron (fun i : {i // p i} => M i.1) βr γr
        * piKron (fun i : {i // ¬ p i} => M i.1) βc γc := by
  classical
  simp only [piKron]
  rw [← Fintype.prod_subtype_mul_prod_subtype p
    (fun i => M i (((Equiv.piEquivPiSubtypeProd p (fun i => Fin (d i))).symm (βr, βc)) i)
      (((Equiv.piEquivPiSubtypeProd p (fun i => Fin (d i))).symm (γr, γc)) i))]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have h1 : ((Equiv.piEquivPiSubtypeProd p (fun i => Fin (d i))).symm (βr, βc)) i.1 = βr i := by
      show (if h : p i.1 then βr ⟨i.1, h⟩ else βc ⟨i.1, h⟩) = βr i
      rw [dif_pos i.2]
    have h2 : ((Equiv.piEquivPiSubtypeProd p (fun i => Fin (d i))).symm (γr, γc)) i.1 = γr i := by
      show (if h : p i.1 then γr ⟨i.1, h⟩ else γc ⟨i.1, h⟩) = γr i
      rw [dif_pos i.2]
    rw [h1, h2]
  · refine Finset.prod_congr rfl fun i _ => ?_
    have h1 : ((Equiv.piEquivPiSubtypeProd p (fun i => Fin (d i))).symm (βr, βc)) i.1 = βc i := by
      show (if h : p i.1 then βr ⟨i.1, h⟩ else βc ⟨i.1, h⟩) = βc i
      rw [dif_neg i.2]
    have h2 : ((Equiv.piEquivPiSubtypeProd p (fun i => Fin (d i))).symm (γr, γc)) i.1 = γc i := by
      show (if h : p i.1 then γr ⟨i.1, h⟩ else γc ⟨i.1, h⟩) = γc i
      rw [dif_neg i.2]
    rw [h1, h2]

/-- **Reshape of a boundary-Kronecker product.** Right-multiplying by `piKron N` and then
reshaping at the side cut is the same as reshaping and then sandwiching by the two
`idKron`s of the sub-family Kronecker products. -/
theorem reshapeSplit_mul_piKron {R R₁ R₂ ι : Type*} [Fintype R] [Fintype ι] [DecidableEq ι]
    [Fintype R₁] [Fintype R₂] [DecidableEq R₁] [DecidableEq R₂]
    (p : ι → Prop) [DecidablePred p] {d : ι → ℕ}
    (eR : R ≃ R₁ × R₂) (A : Matrix R ((i : ι) → Fin (d i)) ℝ)
    (N : (i : ι) → Matrix (Fin (d i)) (Fin (d i)) ℝ) :
    reshapeSplit eR (Equiv.piEquivPiSubtypeProd p (fun i => Fin (d i))) (A * piKron N)
      = idKron (I := R₁) (piKron (fun i : {i // p i} => N i.1))ᵀ
        * reshapeSplit eR (Equiv.piEquivPiSubtypeProd p (fun i => Fin (d i))) A
        * idKron (I := R₂) (piKron (fun i : {i // ¬ p i} => N i.1)) := by
  classical
  set eB := Equiv.piEquivPiSubtypeProd p (fun i => Fin (d i)) with heB
  set KR := piKron (fun i : {i // p i} => N i.1) with hKR
  set KC := piKron (fun i : {i // ¬ p i} => N i.1) with hKC
  ext pr pc
  -- Canonical middle form (`γc` outer, `γr` inner).
  have hLHS : reshapeSplit eR eB (A * piKron N) pr pc
      = ∑ γc : (i : {i // ¬ p i}) → Fin (d i.1), ∑ γr : (i : {i // p i}) → Fin (d i.1),
          reshapeSplit eR eB A (pr.1, γr) (pc.1, γc) * KR γr pr.2 * KC γc pc.2 := by
    show (A * piKron N) (eR.symm (pr.1, pc.1)) (eB.symm (pr.2, pc.2)) = _
    rw [Matrix.mul_apply, ← Equiv.sum_comp eB.symm
      (fun γ => A (eR.symm (pr.1, pc.1)) γ * piKron N γ (eB.symm (pr.2, pc.2)))]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun γc _ => Finset.sum_congr rfl fun γr _ => ?_
    rw [piKron_symm_split p N γr pr.2 γc pc.2]
    show A (eR.symm (pr.1, pc.1)) (eB.symm (γr, γc)) * (KR γr pr.2 * KC γc pc.2)
      = A (eR.symm (pr.1, pc.1)) (eB.symm (γr, γc)) * KR γr pr.2 * KC γc pc.2
    ring
  have hRHS : (idKron (I := R₁) KRᵀ * reshapeSplit eR eB A * idKron (I := R₂) KC) pr pc
      = ∑ γc : (i : {i // ¬ p i}) → Fin (d i.1), ∑ γr : (i : {i // p i}) → Fin (d i.1),
          reshapeSplit eR eB A (pr.1, γr) (pc.1, γc) * KR γr pr.2 * KC γc pc.2 := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single pc.1]
    · refine Finset.sum_congr rfl fun γc _ => ?_
      have hR : (idKron (I := R₂) KC) (pc.1, γc) pc = KC γc pc.2 := by
        simp only [idKron, if_true, one_mul]
      rw [hR, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single pr.1]
      · rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun γr _ => ?_
        have hL : (idKron (I := R₁) KRᵀ) pr (pr.1, γr) = KR γr pr.2 := by
          simp only [idKron, Matrix.transpose_apply, if_true, one_mul]
        rw [hL]; ring
      · intro ξr _ hne
        apply Finset.sum_eq_zero
        intro γr _
        have hL0 : (idKron (I := R₁) KRᵀ) pr (ξr, γr) = 0 := by
          simp only [idKron, Matrix.transpose_apply]
          rw [if_neg (fun h => hne h.symm), zero_mul]
        rw [hL0, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro ξc _ hne
      apply Finset.sum_eq_zero
      intro γc _
      have hR0 : (idKron (I := R₂) KC) (ξc, γc) pc = 0 := by
        simp only [idKron]; rw [if_neg hne, zero_mul]
      rw [hR0, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hLHS, hRHS]

/-! ### Shared geometric and indicator helpers for the two `e*`-cut factorizations -/

/-- A boundary edge is never the cut edge `e* = s(xs, ys)`: both endpoints of `e*` lie in `S`,
but the far endpoint `oQ f` of a boundary edge does not. -/
theorem bdry_ne_star (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f))
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    {xs ys : a.V} (hxsS : xs ∈ S) (hysS : ys ∈ S)
    (f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}) :
    s(oP f, oQ f) ≠ s(xs, ys) := by
  intro hc
  have hqS : oQ f ∉ S := oSide f (oQ f) (a.not_side_right (oAdj f))
  have hmem : oQ f ∈ s(xs, ys) := hc ▸ Sym2.mem_mk_right (oP f) (oQ f)
  rcases Sym2.mem_iff.mp hmem with rfl | rfl
  · exact hqS hxsS
  · exact hqS hysS

/-- Along the `e*`-cut, a boundary edge keeps both endpoints on the same side. -/
theorem bdry_oQ_side_iff (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f))
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    {xs ys : a.V} (hstar : a.G.Adj xs ys) (hxsS : xs ∈ S) (hysS : ys ∈ S)
    (f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}) :
    a.Side hstar (oP f) ↔ a.Side hstar (oQ f) :=
  a.side_iff_of_adj hstar (oAdj f) (bdry_ne_star S oP oQ oAdj oSide hxsS hysS f)

/-- G3, iff form: a vertex behind a boundary edge `f` shares the `e*`-side of `oQ f`. -/
theorem behind_side_iff (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f))
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    {xs ys : a.V} (hstar : a.G.Adj xs ys) (hxsS : xs ∈ S)
    (f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E})
    {z : a.V} (hz : ¬ a.Side (oAdj f) z) :
    (a.Side hstar z ↔ a.Side hstar (oQ f)) :=
  a.side_hstar_iff_of_behind hstar hxsS (oAdj f)
    (fun s hs => not_not.mp (fun hns => oSide f s hns hs)) hz

/-- A vertex behind a row-side boundary edge is on the row side of the `e*`-cut. -/
theorem behind_rowplace (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f))
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    {xs ys : a.V} (hstar : a.G.Adj xs ys) (hxsS : xs ∈ S) (hysS : ys ∈ S)
    (f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E})
    (hf : a.Side hstar (oP f)) {z : a.V} (hz : ¬ a.Side (oAdj f) z) : a.Side hstar z :=
  (behind_side_iff S oP oQ oAdj oSide hstar hxsS f hz).mpr
    ((bdry_oQ_side_iff S oP oQ oAdj oSide hstar hxsS hysS f).mp hf)

/-- A vertex behind a column-side boundary edge is on the column side of the `e*`-cut. -/
theorem behind_colplace (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f))
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    {xs ys : a.V} (hstar : a.G.Adj xs ys) (hxsS : xs ∈ S) (hysS : ys ∈ S)
    (f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E})
    (hf : ¬ a.Side hstar (oP f)) {z : a.V} (hz : ¬ a.Side (oAdj f) z) : ¬ a.Side hstar z :=
  fun h => hf ((bdry_oQ_side_iff S oP oQ oAdj oSide hstar hxsS hysS f).mpr
    ((behind_side_iff S oP oQ oAdj oSide hstar hxsS f hz).mp h))

/-- A finite product of equality-indicators is the indicator of the pointwise equality. -/
theorem prod_indicator_eq_ite {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, DecidableEq (κ i)] (f g : (i : ι) → κ i) :
    (∏ i, if f i = g i then (1 : ℝ) else 0) = if f = g then 1 else 0 := by
  by_cases h : f = g
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi])

/-- **Boundary `Hfun`-product recombination** across the `e*`-cut: the row-side product (in
`rx`) times the column-side product (in `cx`) reassembles the full boundary product of the
recombined point `(extSplit hstar).symm (rx, cx)`, at the recombined bond `eB.symm (βr, βc)`. -/
theorem prod_Hfun_recombine (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)) (oEdge : ∀ f, s(oP f, oQ f) = f.1.1)
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    {xs ys : a.V} (hstar : a.G.Adj xs ys) (hxsS : xs ∈ S) (hysS : ys ∈ S)
    (W : a.Param) (rx : a.Row hstar) (cx : a.Col hstar)
    (βr : (f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
          // a.Side hstar (oP f)}) → Fin (a.r f.1.1.1))
    (βc : (f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
          // ¬ a.Side hstar (oP f)}) → Fin (a.r f.1.1.1)) :
    (∏ f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
          // a.Side hstar (oP f)}, a.Hfun (oAdj f.1) W
        (fun z => rx ⟨z.1, a.behind_rowplace S oP oQ oAdj oSide hstar hxsS hysS f.1 f.2 z.2⟩)
        ((finCongr (congrArg a.r (oEdge f.1))).symm (βr f)))
      * (∏ f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
          // ¬ a.Side hstar (oP f)}, a.Hfun (oAdj f.1) W
        (fun z => cx ⟨z.1, a.behind_colplace S oP oQ oAdj oSide hstar hxsS hysS f.1 f.2 z.2⟩)
        ((finCongr (congrArg a.r (oEdge f.1))).symm (βc f)))
    = ∏ f, a.Hfun (oAdj f) W
        (fun z => if h : a.Side hstar z.1 then rx ⟨z.1, h⟩ else cx ⟨z.1, h⟩)
        ((finCongr (congrArg a.r (oEdge f))).symm
          ((Equiv.piEquivPiSubtypeProd
            (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
              a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1))).symm (βr, βc) f)) := by
  classical
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun f => a.Side hstar (oP f))
      (fun f => a.Hfun (oAdj f) W
        (fun z => if h : a.Side hstar z.1 then rx ⟨z.1, h⟩ else cx ⟨z.1, h⟩)
        ((finCongr (congrArg a.r (oEdge f))).symm
          ((Equiv.piEquivPiSubtypeProd
            (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
              a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1))).symm (βr, βc) f)))]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine Finset.prod_congr rfl (fun f _ => ?_)
    have hb : (Equiv.piEquivPiSubtypeProd
        (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
          a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1))).symm (βr, βc) f.1 = βr f := by
      show (if h : a.Side hstar (oP f.1) then (βr, βc).1 ⟨f.1, h⟩ else (βr, βc).2 ⟨f.1, h⟩) = βr f
      rw [dif_pos f.2]
    rw [hb]
    congr 1
    funext z
    rw [dif_pos (a.behind_rowplace S oP oQ oAdj oSide hstar hxsS hysS f.1 f.2 z.2)]
  · refine Finset.prod_congr rfl (fun f _ => ?_)
    have hb : (Equiv.piEquivPiSubtypeProd
        (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
          a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1))).symm (βr, βc) f.1 = βc f := by
      show (if h : a.Side hstar (oP f.1) then (βr, βc).1 ⟨f.1, h⟩ else (βr, βc).2 ⟨f.1, h⟩) = βc f
      rw [dif_neg f.2]
    rw [hb]
    congr 1
    funext z
    rw [dif_neg (a.behind_colplace S oP oQ oAdj oSide hstar hxsS hysS f.1 f.2 z.2)]

/-- Generic boundary-bond reindex through the `e*`-side split (no coordinate data, cheap). -/
theorem sum_bdry_reindex (S : Finset a.V)
    (oP : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    {xs ys : a.V} (hstar : a.G.Adj xs ys) (G : a.BdryBond S → ℝ) :
    (∑ βr : (f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
          // a.Side hstar (oP f)}) → Fin (a.r f.1.1.1),
        ∑ βc : (f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
            // ¬ a.Side hstar (oP f)}) → Fin (a.r f.1.1.1),
          G ((Equiv.piEquivPiSubtypeProd
            (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
              a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1))).symm (βr, βc)))
    = ∑ β, G β := by
  rw [← Fintype.sum_prod_type (fun p => G ((Equiv.piEquivPiSubtypeProd
    (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
      a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1))).symm p))]
  exact Equiv.sum_comp (Equiv.piEquivPiSubtypeProd
    (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
      a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1))).symm G

set_option maxHeartbeats 1600000 in
/-- **Reindex + recombine** the side-split double sum back to the boundary-bond sum: the
row/column factored form reassembles the master-Fubini `∑ β` form of the recombined point. -/
theorem reindex_recombine (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)) (oEdge : ∀ f, s(oP f, oQ f) = f.1.1)
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    {xs ys : a.V} (hstar : a.G.Adj xs ys) (hxsS : xs ∈ S) (hysS : ys ∈ S)
    (W : a.Param) (rx : a.Row hstar) (cx : a.Col hstar) :
    (∑ βc : (f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
            // ¬ a.Side hstar (oP f)}) → Fin (a.r f.1.1.1),
        (∑ βr : (f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
              // a.Side hstar (oP f)}) → Fin (a.r f.1.1.1),
            (∏ f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
                  // a.Side hstar (oP f)}, a.Hfun (oAdj f.1) W
                (fun z => rx ⟨z.1,
                  a.behind_rowplace S oP oQ oAdj oSide hstar hxsS hysS f.1 f.2 z.2⟩)
                ((finCongr (congrArg a.r (oEdge f.1))).symm (βr f)))
              * SCore W S (fun v => if h : a.Side hstar v.1 then rx ⟨v.1, h⟩ else cx ⟨v.1, h⟩)
                  ((Equiv.piEquivPiSubtypeProd
                    (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
                      a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1))).symm (βr, βc)))
          * (∏ f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
                // ¬ a.Side hstar (oP f)}, a.Hfun (oAdj f.1) W
              (fun z => cx ⟨z.1,
                a.behind_colplace S oP oQ oAdj oSide hstar hxsS hysS f.1 f.2 z.2⟩)
              ((finCongr (congrArg a.r (oEdge f.1))).symm (βc f))))
    = ∑ β : a.BdryBond S,
        SCore W S (fun v => if h : a.Side hstar v.1 then rx ⟨v.1, h⟩ else cx ⟨v.1, h⟩) β
          * ∏ f, a.Hfun (oAdj f) W
              (fun z => if h : a.Side hstar z.1 then rx ⟨z.1, h⟩ else cx ⟨z.1, h⟩)
              ((finCongr (congrArg a.r (oEdge f))).symm (β f)) := by
  classical
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl (fun βr _ => Finset.sum_congr rfl (fun βc _ => ?_))).trans
    (a.sum_bdry_reindex S oP hstar (fun β =>
      SCore W S (fun v => if h : a.Side hstar v.1 then rx ⟨v.1, h⟩ else cx ⟨v.1, h⟩) β
        * ∏ f, a.Hfun (oAdj f) W
            (fun z => if h : a.Side hstar z.1 then rx ⟨z.1, h⟩ else cx ⟨z.1, h⟩)
            ((finCongr (congrArg a.r (oEdge f))).symm (β f))))
  rw [← a.prod_Hfun_recombine S oP oQ oAdj oEdge oSide hstar hxsS hysS W rx cx βr βc]
  ring

/-- The target's `e*`-matricization factors through the side-split of the `θs` S-core
matrix. This is a master-Fubini regrouping of `matricizeOf hstar (represented θs)` at the
`e*`-cut (`hts : represented θs = Tstar`).

Proof: from `matricizeOf hstar Tstar rx cx = represented θs ((extSplit hstar).symm (rx, cx))`,
expand by the master Fubini `represented_eq_sum_SCore` at `θs`. The witnesses are
`Er (rx, (ζr, βr)) := (∏ v : SR-index, ind(rx ⟨v.1.1, v.2⟩ = ζr v))
    * ∏ f : BR-index, a.Hfun (oAdj f.1) θs (fun z => rx ⟨z.1, G3⟩) ((finCongr …).symm (βr f))`
and `Ec` dually on the `¬Side` blocks, where `G3 = behind_rowplace/colplace` places each
subtree vertex on the `e*`-side (`side_hstar_iff_of_behind`). The entry identity is two
`Matrix.mul_apply`s with the `ζr/ζc`-indicators collapsing the `S`-external row/column parts,
then `reindex_recombine` (boundary-bond reindex `∑ βr ∑ βc ↦ ∑ β` + `prod_Hfun_recombine`).
Needs `hysS` so `e* = s(xs, ys)` is not itself a boundary edge (see `bdry_ne_star`). -/
theorem exists_factor_matricizeOf_Tstar {Tstar : a.Ext → ℝ} {θs : a.Param}
    (hts : a.represented θs = Tstar) (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)) (oEdge : ∀ f, s(oP f, oQ f) = f.1.1)
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    (oPart : ∀ y : a.V, y ∉ S → ∃! f, ¬ a.Side (oAdj f) y)
    {xs ys : a.V} (hstar : a.G.Adj xs ys) (hxsS : xs ∈ S) (hysS : ys ∈ S) :
    ∃ (Er : Matrix (a.Row hstar)
        (((v : {v : {v : a.V // v ∈ S} // a.Side hstar v.1}) → Fin (a.n v.1.1))
          × ((f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
              // a.Side hstar (oP f)}) → Fin (a.r f.1.1.1))) ℝ)
      (Ec : Matrix (a.Col hstar)
        (((v : {v : {v : a.V // v ∈ S} // ¬ a.Side hstar v.1}) → Fin (a.n v.1.1))
          × ((f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
              // ¬ a.Side hstar (oP f)}) → Fin (a.r f.1.1.1))) ℝ),
      a.matricizeOf hstar Tstar
        = Er * reshapeSplit
            (Equiv.piEquivPiSubtypeProd (fun v : {v : a.V // v ∈ S} => a.Side hstar v.1)
              (fun v => Fin (a.n v.1)))
            (Equiv.piEquivPiSubtypeProd
              (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
                a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1)))
            (a.SCoreMat θs S) * Ecᵀ := by
  classical
  refine ⟨fun rx p => (∏ v : {v : {v : a.V // v ∈ S} // a.Side hstar v.1},
              if rx ⟨v.1.1, v.2⟩ = p.1 v then (1 : ℝ) else 0)
            * ∏ f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
                // a.Side hstar (oP f)}, a.Hfun (oAdj f.1) θs
                (fun z => rx ⟨z.1, a.behind_rowplace S oP oQ oAdj oSide hstar hxsS hysS f.1 f.2 z.2⟩)
                ((finCongr (congrArg a.r (oEdge f.1))).symm (p.2 f)),
          fun cx q => (∏ v : {v : {v : a.V // v ∈ S} // ¬ a.Side hstar v.1},
              if cx ⟨v.1.1, v.2⟩ = q.1 v then (1 : ℝ) else 0)
            * ∏ f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
                // ¬ a.Side hstar (oP f)}, a.Hfun (oAdj f.1) θs
                (fun z => cx ⟨z.1, a.behind_colplace S oP oQ oAdj oSide hstar hxsS hysS f.1 f.2 z.2⟩)
                ((finCongr (congrArg a.r (oEdge f.1))).symm (q.2 f)),
          ?_⟩
  ext rx cx
  have hL : a.matricizeOf hstar Tstar rx cx
      = a.represented θs ((a.extSplit hstar).symm (rx, cx)) := by rw [← hts]; rfl
  rw [hL, a.represented_eq_sum_SCore θs S oP oQ oAdj oEdge oSide oPart
      ((a.extSplit hstar).symm (rx, cx))]
  simp only [show ∀ v : a.V, (a.extSplit hstar).symm (rx, cx) v
      = if h : a.Side hstar v then rx ⟨v, h⟩ else cx ⟨v, h⟩ from fun _ => rfl]
  symm
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Fintype.sum_prod_type, prod_indicator_eq_ite, ite_mul, one_mul, zero_mul,
    mul_ite, mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have hξ : (Equiv.piEquivPiSubtypeProd (fun v : {v : a.V // v ∈ S} => a.Side hstar v.1)
        (fun v => Fin (a.n v.1))).symm (fun i => rx ⟨i.1.1, i.2⟩, fun i => cx ⟨i.1.1, i.2⟩)
      = (fun v : {v : a.V // v ∈ S} =>
          if h : a.Side hstar v.1 then rx ⟨v.1, h⟩ else cx ⟨v.1, h⟩) := by
    funext v
    rfl
  have hM : ∀ (βr : (f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
            // a.Side hstar (oP f)}) → Fin (a.r f.1.1.1))
        (βc : (f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
            // ¬ a.Side hstar (oP f)}) → Fin (a.r f.1.1.1)),
      reshapeSplit (Equiv.piEquivPiSubtypeProd (fun v : {v : a.V // v ∈ S} => a.Side hstar v.1)
          (fun v => Fin (a.n v.1)))
        (Equiv.piEquivPiSubtypeProd
          (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
            a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1))) (a.SCoreMat θs S)
        (fun i => rx ⟨i.1.1, i.2⟩, βr) (fun i => cx ⟨i.1.1, i.2⟩, βc)
      = SCore θs S (fun v => if h : a.Side hstar v.1 then rx ⟨v.1, h⟩ else cx ⟨v.1, h⟩)
          ((Equiv.piEquivPiSubtypeProd
            (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
              a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1))).symm (βr, βc)) := by
    intro βr βc
    show SCore θs S ((Equiv.piEquivPiSubtypeProd
        (fun v : {v : a.V // v ∈ S} => a.Side hstar v.1) (fun v => Fin (a.n v.1))).symm
        (fun i => rx ⟨i.1.1, i.2⟩, fun i => cx ⟨i.1.1, i.2⟩))
        ((Equiv.piEquivPiSubtypeProd
          (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
            a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1))).symm (βr, βc)) = _
    rw [hξ]
  simp only [hM]
  exact a.reindex_recombine S oP oQ oAdj oEdge oSide hstar hxsS hysS θs rx cx

/-- **Boundary `Hfun`-product recombination into `envFactor`**: the row-side and column-side
`Hfun`-products of a point `y` reassemble the environment factor of `y`'s far restriction. -/
theorem envfactor_recombine (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)) (oEdge : ∀ f, s(oP f, oQ f) = f.1.1)
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    (oPart : ∀ y : a.V, y ∉ S → ∃! f, ¬ a.Side (oAdj f) y)
    {xs ys : a.V} (hstar : a.G.Adj xs ys) (θ : a.Param) (y : a.Ext)
    (βr : (f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
          // a.Side hstar (oP f)}) → Fin (a.r f.1.1.1))
    (βc : (f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
          // ¬ a.Side hstar (oP f)}) → Fin (a.r f.1.1.1)) :
    (∏ f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
          // a.Side hstar (oP f)}, a.Hfun (oAdj f.1) θ (fun z => y z.1)
        ((finCongr (congrArg a.r (oEdge f.1))).symm (βr f)))
      * (∏ f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
          // ¬ a.Side hstar (oP f)}, a.Hfun (oAdj f.1) θ (fun z => y z.1)
        ((finCongr (congrArg a.r (oEdge f.1))).symm (βc f)))
    = a.envFactor θ S ((Equiv.piEquivPiSubtypeProd
        (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
          a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1))).symm (βr, βc)) (fun w => y w.1) := by
  classical
  rw [a.envFactor_eq_prod_Hfun θ S oP oQ oAdj oEdge oSide oPart _ (fun w => y w.1),
    ← Fintype.prod_subtype_mul_prod_subtype (fun f => a.Side hstar (oP f))
      (fun f => a.Hfun (oAdj f) θ (fun z => y z.1)
        ((finCongr (congrArg a.r (oEdge f))).symm
          ((Equiv.piEquivPiSubtypeProd
            (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
              a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1))).symm (βr, βc) f)))]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine Finset.prod_congr rfl (fun f _ => ?_)
    have hb : (Equiv.piEquivPiSubtypeProd
        (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
          a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1))).symm (βr, βc) f.1 = βr f := by
      show (if h : a.Side hstar (oP f.1) then (βr, βc).1 ⟨f.1, h⟩ else (βr, βc).2 ⟨f.1, h⟩) = βr f
      rw [dif_pos f.2]
    rw [hb]
  · refine Finset.prod_congr rfl (fun f _ => ?_)
    have hb : (Equiv.piEquivPiSubtypeProd
        (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
          a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1))).symm (βr, βc) f.1 = βc f := by
      show (if h : a.Side hstar (oP f.1) then (βr, βc).1 ⟨f.1, h⟩ else (βr, βc).2 ⟨f.1, h⟩) = βc f
      rw [dif_neg f.2]
    rw [hb]

/-- Reindex a double `Row × Col` sum as a sum over `Ext` (generic, cheap). -/
theorem sum_extsplit_reindex {xs ys : a.V} (hstar : a.G.Adj xs ys)
    (H : a.Row hstar → a.Col hstar → ℝ) :
    (∑ rx, ∑ cx, H rx cx)
      = ∑ y : a.Ext, H ((a.extSplit hstar) y).1 ((a.extSplit hstar) y).2 := by
  rw [← Fintype.sum_prod_type (fun p => H p.1 p.2)]
  exact (Equiv.sum_comp (a.extSplit hstar) (fun p => H p.1 p.2)).symm

/-- Reindex a sum over `Ext` as a double sum over `S`-externals and far-externals (generic). -/
theorem sum_e0_reindex (S : Finset a.V) (G : a.Ext → ℝ) :
    (∑ y : a.Ext, G y)
      = ∑ η, ∑ xf,
          G ((Equiv.piEquivPiSubtypeProd (fun v : a.V => v ∈ S)
            (fun v => Fin (a.n v))).symm (η, xf)) := by
  rw [← Fintype.sum_prod_type (fun p => G ((Equiv.piEquivPiSubtypeProd (fun v : a.V => v ∈ S)
    (fun v => Fin (a.n v))).symm p))]
  exact (Equiv.sum_comp (Equiv.piEquivPiSubtypeProd (fun v : a.V => v ∈ S)
    (fun v => Fin (a.n v))).symm G).symm

/-- The `θ`-environment pairing's side-split factors through the `θ`-matricization at `e*`.
This is a master-Fubini regrouping of `envPairedMat θ θ S` at the `e*`-cut.

Proof: the entry `(P' * matricize θ * Q'ᵀ) pr pc` expands (two `Matrix.mul_apply`s) into a
`∑ cx ∑ rx`, reindexed to `∑ y : Ext` (`sum_extsplit_reindex`) then `∑ η ∑ xf`
(`sum_e0_reindex`), with `matricize (extSplit y).1 (extSplit y).2 = represented θ y`. The
The `P'`/`Q'` indicators use the same witnesses as the target factorization and pin `η = ξ`
(a `Finset.sum_eq_single` collapse),
and `envfactor_recombine` reassembles the boundary `Hfun`-products into `envFactor`, matching
the master-Fubini form of `envPaired`. Needs `hysS`; see `bdry_ne_star`. -/
theorem exists_factor_reshapeSplit_envPaired (θ : a.Param) (S : Finset a.V)
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)) (oEdge : ∀ f, s(oP f, oQ f) = f.1.1)
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    (oPart : ∀ y : a.V, y ∉ S → ∃! f, ¬ a.Side (oAdj f) y)
    {xs ys : a.V} (hstar : a.G.Adj xs ys) (hxsS : xs ∈ S) (hysS : ys ∈ S) :
    ∃ (P' : Matrix
        (((v : {v : {v : a.V // v ∈ S} // a.Side hstar v.1}) → Fin (a.n v.1.1))
          × ((f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
              // a.Side hstar (oP f)}) → Fin (a.r f.1.1.1))) (a.Row hstar) ℝ)
      (Q' : Matrix
        (((v : {v : {v : a.V // v ∈ S} // ¬ a.Side hstar v.1}) → Fin (a.n v.1.1))
          × ((f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
              // ¬ a.Side hstar (oP f)}) → Fin (a.r f.1.1.1))) (a.Col hstar) ℝ),
      reshapeSplit
          (Equiv.piEquivPiSubtypeProd (fun v : {v : a.V // v ∈ S} => a.Side hstar v.1)
            (fun v => Fin (a.n v.1)))
          (Equiv.piEquivPiSubtypeProd
            (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
              a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1)))
          (a.envPairedMat θ θ S)
        = P' * a.matricize hstar θ * Q'ᵀ := by
  classical
  refine ⟨fun p rx => (∏ v : {v : {v : a.V // v ∈ S} // a.Side hstar v.1},
              if rx ⟨v.1.1, v.2⟩ = p.1 v then (1 : ℝ) else 0)
            * ∏ f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
                // a.Side hstar (oP f)}, a.Hfun (oAdj f.1) θ
                (fun z => rx ⟨z.1, a.behind_rowplace S oP oQ oAdj oSide hstar hxsS hysS f.1 f.2 z.2⟩)
                ((finCongr (congrArg a.r (oEdge f.1))).symm (p.2 f)),
          fun q cx => (∏ v : {v : {v : a.V // v ∈ S} // ¬ a.Side hstar v.1},
              if cx ⟨v.1.1, v.2⟩ = q.1 v then (1 : ℝ) else 0)
            * ∏ f : {f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}
                // ¬ a.Side hstar (oP f)}, a.Hfun (oAdj f.1) θ
                (fun z => cx ⟨z.1, a.behind_colplace S oP oQ oAdj oSide hstar hxsS hysS f.1 f.2 z.2⟩)
                ((finCongr (congrArg a.r (oEdge f.1))).symm (q.2 f)),
          ?_⟩
  ext pr pc
  show a.envPaired θ θ S
      ((Equiv.piEquivPiSubtypeProd (fun v : {v : a.V // v ∈ S} => a.Side hstar v.1)
        (fun v => Fin (a.n v.1))).symm (pr.1, pc.1))
      ((Equiv.piEquivPiSubtypeProd
        (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
          a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1))).symm (pr.2, pc.2)) = _
  symm
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine (a.sum_extsplit_reindex hstar _).trans ?_
  refine (a.sum_e0_reindex S _).trans ?_
  have hmat : ∀ y : a.Ext,
      a.matricize hstar θ ((a.extSplit hstar) y).1 ((a.extSplit hstar) y).2 = a.represented θ y :=
    fun y => by
      show a.represented θ ((a.extSplit hstar).symm ((a.extSplit hstar) y)) = a.represented θ y
      rw [Equiv.symm_apply_apply]
  simp only [hmat,
    show ∀ (y : a.Ext) (w : {x : a.V // a.Side hstar x}), ((a.extSplit hstar) y).1 w = y w.1
      from fun _ _ => rfl,
    show ∀ (y : a.Ext) (w : {x : a.V // ¬ a.Side hstar x}), ((a.extSplit hstar) y).2 w = y w.1
      from fun _ _ => rfl,
    show ∀ (η : a.SExtC S) (xf : a.FarExtC S) (v : {v : a.V // v ∈ S}),
        (Equiv.piEquivPiSubtypeProd (fun v : a.V => v ∈ S) (fun v => Fin (a.n v))).symm (η, xf) v.1
          = η v from fun η xf v => (dif_pos v.2).trans rfl]
  rw [Finset.sum_comm]
  conv_rhs => rw [show a.envPaired θ θ S
      ((Equiv.piEquivPiSubtypeProd (fun v : {v : a.V // v ∈ S} => a.Side hstar v.1)
        (fun v => Fin (a.n v.1))).symm (pr.1, pc.1))
      ((Equiv.piEquivPiSubtypeProd
        (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
          a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1))).symm (pr.2, pc.2))
      = ∑ xf, a.represented θ ((Equiv.piEquivPiSubtypeProd (fun v : a.V => v ∈ S)
              (fun v => Fin (a.n v))).symm
            ((Equiv.piEquivPiSubtypeProd (fun v : {v : a.V // v ∈ S} => a.Side hstar v.1)
              (fun v => Fin (a.n v.1))).symm (pr.1, pc.1), xf))
          * a.envFactor θ S ((Equiv.piEquivPiSubtypeProd
              (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
                a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1))).symm (pr.2, pc.2)) xf from rfl]
  refine Finset.sum_congr rfl (fun xf _ => ?_)
  refine (Finset.sum_eq_single
      ((Equiv.piEquivPiSubtypeProd (fun v : {v : a.V // v ∈ S} => a.Side hstar v.1)
        (fun v => Fin (a.n v.1))).symm (pr.1, pc.1)) (fun η _ hne => ?_)
      (fun h => absurd (Finset.mem_univ _) h)).trans ?_
  · -- vanishing off η = ξ
    obtain ⟨v, hv⟩ := Function.ne_iff.mp hne
    by_cases hs : a.Side hstar v.1
    · have hz : (∏ x_1 : {w : {v : a.V // v ∈ S} // a.Side hstar w.1},
          if η x_1.1 = pr.1 x_1 then (1 : ℝ) else 0) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ ⟨v, hs⟩) (if_neg ?_)
        rw [show (Equiv.piEquivPiSubtypeProd (fun v : {v : a.V // v ∈ S} => a.Side hstar v.1)
            (fun v => Fin (a.n v.1))).symm (pr.1, pc.1) v = pr.1 ⟨v, hs⟩ from dif_pos hs] at hv
        exact hv
      rw [hz]; ring
    · have hz : (∏ x_1 : {w : {v : a.V // v ∈ S} // ¬ a.Side hstar w.1},
          if η x_1.1 = pc.1 x_1 then (1 : ℝ) else 0) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ ⟨v, hs⟩) (if_neg ?_)
        rw [show (Equiv.piEquivPiSubtypeProd (fun v : {v : a.V // v ∈ S} => a.Side hstar v.1)
            (fun v => Fin (a.n v.1))).symm (pr.1, pc.1) v = pc.1 ⟨v, hs⟩ from dif_neg hs] at hv
        exact hv
      rw [hz]; ring
  · -- the η = ξ term
    have hR1 : (∏ x_1 : {w : {v : a.V // v ∈ S} // a.Side hstar w.1},
        if (Equiv.piEquivPiSubtypeProd (fun v : {v : a.V // v ∈ S} => a.Side hstar v.1)
          (fun v => Fin (a.n v.1))).symm (pr.1, pc.1) x_1.1 = pr.1 x_1 then (1 : ℝ) else 0) = 1 :=
      Finset.prod_eq_one (fun x_1 _ => if_pos (dif_pos x_1.2))
    have hC1 : (∏ x_1 : {w : {v : a.V // v ∈ S} // ¬ a.Side hstar w.1},
        if (Equiv.piEquivPiSubtypeProd (fun v : {v : a.V // v ∈ S} => a.Side hstar v.1)
          (fun v => Fin (a.n v.1))).symm (pr.1, pc.1) x_1.1 = pc.1 x_1 then (1 : ℝ) else 0) = 1 :=
      Finset.prod_eq_one (fun x_1 _ => if_pos (dif_neg x_1.2))
    rw [hR1, hC1, one_mul, one_mul, mul_right_comm,
      a.envfactor_recombine S oP oQ oAdj oEdge oSide oPart hstar θ _ pr.2 pc.2,
      show (fun w : {y : a.V // y ∉ S} => (Equiv.piEquivPiSubtypeProd (fun v : a.V => v ∈ S)
          (fun v => Fin (a.n v))).symm ((Equiv.piEquivPiSubtypeProd
            (fun v : {v : a.V // v ∈ S} => a.Side hstar v.1) (fun v => Fin (a.n v.1))).symm
            (pr.1, pc.1), xf) w.1) = xf from funext (fun w => (dif_neg w.2).trans rfl)]
    ring

/-- **(split)** The side-splits of the `θs` S-core and the `θ`-pairing have comparable rank:
they differ by the two-sided boundary Kronecker factor `bdryKron θs θ`, which is a unit. -/
theorem rank_reshapeSplit_SCore_le_envPaired {Tstar : a.Ext → ℝ} {θ θs : a.Param}
    (hmn : a.MinNorm θ) (hcrit : a.Critical Tstar θ) (hts : a.represented θs = Tstar)
    (S : Finset a.V) (K : Finset a.G.edgeSet)
    (hKiff : ∀ E : a.G.edgeSet, E ∈ K ↔ a.EdgeInside S E)
    (hbdry : ∀ E : a.G.edgeSet, E ∉ K → ∀ (u w : a.V) (h : a.G.Adj u w), s(u, w) = E.1 →
      u ∈ S → (a.matricize h θ).rank = a.r s(u, w))
    (oP oQ : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} → a.V)
    (oAdj : ∀ f, a.G.Adj (oP f) (oQ f)) (oEdge : ∀ f, s(oP f, oQ f) = f.1.1)
    (oPS : ∀ f, oP f ∈ S)
    (oSide : ∀ f (z : a.V), ¬ a.Side (oAdj f) z → z ∉ S)
    (oPart : ∀ y : a.V, y ∉ S → ∃! f, ¬ a.Side (oAdj f) y)
    {xs ys : a.V} (hstar : a.G.Adj xs ys)
    (hstarEq : a.SCoreMat θ S * a.bdryKron θ θ S oP oQ oAdj oEdge
      = a.SCoreMat θs S * a.bdryKron θs θ S oP oQ oAdj oEdge) :
    (reshapeSplit
        (Equiv.piEquivPiSubtypeProd (fun v : {v : a.V // v ∈ S} => a.Side hstar v.1)
          (fun v => Fin (a.n v.1)))
        (Equiv.piEquivPiSubtypeProd
          (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
            a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1)))
        (a.SCoreMat θs S)).rank
      ≤ (reshapeSplit
        (Equiv.piEquivPiSubtypeProd (fun v : {v : a.V // v ∈ S} => a.Side hstar v.1)
          (fun v => Fin (a.n v.1)))
        (Equiv.piEquivPiSubtypeProd
          (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} =>
            a.Side hstar (oP f)) (fun f => Fin (a.r f.1.1)))
        (a.envPairedMat θ θ S)).rank := by
  classical
  set eS := Equiv.piEquivPiSubtypeProd (fun v : {v : a.V // v ∈ S} => a.Side hstar v.1)
    (fun v => Fin (a.n v.1)) with heS
  set eB := Equiv.piEquivPiSubtypeProd
    (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} => a.Side hstar (oP f))
    (fun f => Fin (a.r f.1.1)) with heB
  -- `envPairedMat θθ = SCoreMat θs · piKron (bdryGram θsθ)`.
  have hC1θ := a.envPairedMat_eq_SCoreMat_mul_piKron θ θ S oP oQ oAdj oEdge oSide oPart
  have hEnv : a.envPairedMat θ θ S
      = a.SCoreMat θs S * a.bdryKron θs θ S oP oQ oAdj oEdge := hC1θ.trans hstarEq
  -- reshape the boundary-Kronecker product.
  have hfact := reshapeSplit_mul_piKron
    (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} => a.Side hstar (oP f))
    eS (a.SCoreMat θs S) (a.bdryGram θs θ S oP oQ oAdj oEdge)
  rw [← heB] at hfact
  -- the two boundary sub-Kronecker products are units.
  have hKRunit : IsUnit (piKron (fun f : {f : {E : a.G.edgeSet //
        a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} // a.Side hstar (oP f)} =>
      a.bdryGram θs θ S oP oQ oAdj oEdge f.1)) :=
    isUnit_piKron (fun f => a.isUnit_bdryGram hmn hcrit hts S K hKiff hbdry
      oP oQ oAdj oEdge oPS f.1)
  have hKCunit : IsUnit (piKron (fun f : {f : {E : a.G.edgeSet //
        a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} // ¬ a.Side hstar (oP f)} =>
      a.bdryGram θs θ S oP oQ oAdj oEdge f.1)) :=
    isUnit_piKron (fun f => a.isUnit_bdryGram hmn hcrit hts S K hKiff hbdry
      oP oQ oAdj oEdge oPS f.1)
  have hgoalrank : (reshapeSplit eS eB (a.envPairedMat θ θ S)).rank
      = (reshapeSplit eS eB (a.SCoreMat θs S)).rank := by
    rw [hEnv]
    have hr := congrArg Matrix.rank hfact
    rw [rank_mul_eq_left_of_ker_transpose_eq_bot
          (ker_mulVecLin_eq_bot_of_isUnit (isUnit_transpose (isUnit_idKron hKCunit))),
        rank_mul_eq_right_of_ker_eq_bot
          (ker_mulVecLin_eq_bot_of_isUnit (isUnit_idKron (isUnit_transpose hKRunit)))] at hr
    exact hr
  rw [hgoalrank]

set_option maxHeartbeats 800000 in
/-- At a minimum-norm critical point of a realizable target with full
target rank everywhere, given the deficient component `(S, K)` with a deficient inside edge
`e* = s(xs, ys)`, the compressed residual does not vanish identically — some indicator
choice `(ξ, β)` pairs the residual nontrivially against the environment. -/
theorem exists_envPair_ne_zero {Tstar : a.Ext → ℝ} {θ : a.Param}
    (hmn : a.MinNorm θ) (hcrit : a.Critical Tstar θ) (hreal : a.Realizable Tstar)
    (hTfull : ∀ (u w : a.V) (h : a.G.Adj u w), (a.matricizeOf h Tstar).rank = a.r s(u, w))
    (S : Finset a.V) (K : Finset a.G.edgeSet)
    (hKiff : ∀ E : a.G.edgeSet, E ∈ K ↔ a.EdgeInside S E)
    (hbdry : ∀ E : a.G.edgeSet, E ∉ K → ∀ (u w : a.V) (h : a.G.Adj u w), s(u, w) = E.1 →
      u ∈ S → (a.matricize h θ).rank = a.r s(u, w))
    (hconn : ∀ P ⊆ S, P.Nonempty → P ≠ S →
      ∃ (y z : a.V) (hyz : a.G.Adj y z), y ∉ P ∧ z ∈ P ∧
        (⟨s(y, z), by rw [SimpleGraph.mem_edgeSet]; exact hyz⟩ : a.G.edgeSet) ∈ K)
    {xs ys : a.V} (hstar : a.G.Adj xs ys) (hxsS : xs ∈ S) (hysS : ys ∈ S)
    (hdef : (a.matricize hstar θ).rank < a.r s(xs, ys)) :
    ∃ (ξ : a.SExtC S) (β : a.BdryBond S),
      (∑ xf : a.FarExtC S,
        a.residual Tstar θ ((Equiv.piEquivPiSubtypeProd (fun v : a.V => v ∈ S)
          (fun v => Fin (a.n v))).symm (ξ, xf)) * a.envFactor θ S β xf) ≠ 0 := by
  classical
  by_contra hall
  push Not at hall
  set e := Equiv.piEquivPiSubtypeProd (fun v : a.V => v ∈ S) (fun v => Fin (a.n v)) with he
  -- hall : ∀ ξ β, (∑ xf, residual Tstar θ (e.symm (ξ,xf)) * envFactor θ S β xf) = 0
  obtain ⟨θs, hts⟩ := hreal
  obtain ⟨oP, oQ, oAdj, oEdge, oPS, oQS, oSide⟩ :=
    a.exists_boundary_orientation S K hKiff hconn
  have oPart : ∀ y : a.V, y ∉ S → ∃! f, ¬ a.Side (oAdj f) y :=
    fun y hy => a.existsUnique_not_side S oP oQ oAdj oEdge oPS oQS oSide ⟨xs, hxsS⟩ hy
  -- (*) With the residual pairing vanishing identically, the two environment pairing
  -- matrices coincide (the residual is `represented θ − represented θs`).
  have hEqMat : a.envPairedMat θ θ S = a.envPairedMat θs θ S := by
    ext ξ β
    show a.envPaired θ θ S ξ β = a.envPaired θs θ S ξ β
    have hdiff : a.envPaired θ θ S ξ β - a.envPaired θs θ S ξ β
        = ∑ xf : a.FarExtC S,
            a.residual Tstar θ (e.symm (ξ, xf)) * a.envFactor θ S β xf := by
      show (∑ xf : a.FarExtC S, a.represented θ (e.symm (ξ, xf)) * a.envFactor θ S β xf)
          - (∑ xf : a.FarExtC S, a.represented θs (e.symm (ξ, xf)) * a.envFactor θ S β xf) = _
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun xf _ => ?_)
      rw [← sub_mul]
      congr 1
      show a.represented θ (e.symm (ξ, xf)) - a.represented θs (e.symm (ξ, xf))
          = a.represented θ (e.symm (ξ, xf)) - Tstar (e.symm (ξ, xf))
      rw [hts]
    rw [← sub_eq_zero, hdiff]; exact hall ξ β
  -- Factor both environment-pairing matrices through their S-core matrices.
  have hC1θ : a.envPairedMat θ θ S = a.SCoreMat θ S * a.bdryKron θ θ S oP oQ oAdj oEdge :=
    a.envPairedMat_eq_SCoreMat_mul_piKron θ θ S oP oQ oAdj oEdge oSide oPart
  have hC1θs : a.envPairedMat θs θ S
      = a.SCoreMat θs S * a.bdryKron θs θ S oP oQ oAdj oEdge :=
    a.envPairedMat_eq_SCoreMat_mul_piKron θs θ S oP oQ oAdj oEdge oSide oPart
  -- The S-core matrices are related by the boundary Kronecker products.
  have hstarEq : a.SCoreMat θ S * a.bdryKron θ θ S oP oQ oAdj oEdge
      = a.SCoreMat θs S * a.bdryKron θs θ S oP oQ oAdj oEdge := by
    rw [← hC1θ, ← hC1θs, hEqMat]
  -- Side-split reshape along the `e* = s(xs, ys)`-cut: refine the `S`-external coordinates
  -- by `Side hstar` and the boundary bonds by the `e*`-side of `oP f`.
  set eS := Equiv.piEquivPiSubtypeProd (fun v : {v : a.V // v ∈ S} => a.Side hstar v.1)
    (fun v => Fin (a.n v.1)) with heS
  set eB := Equiv.piEquivPiSubtypeProd
    (fun f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E} => a.Side hstar (oP f))
    (fun f => Fin (a.r f.1.1)) with heB
  -- Factor the target matricization through the side-split of the `θs` S-core.
  obtain ⟨Er, Ec, hC4a⟩ :
      ∃ Er Ec, a.matricizeOf hstar Tstar
        = Er * reshapeSplit eS eB (a.SCoreMat θs S) * Ecᵀ :=
    a.exists_factor_matricizeOf_Tstar hts S oP oQ oAdj oEdge oSide oPart hstar hxsS hysS
  -- Factor the `θ` pairing's side-split through the `θ` matricization at `e*`.
  obtain ⟨P', Q', hC4b⟩ :
      ∃ P' Q', reshapeSplit eS eB (a.envPairedMat θ θ S)
        = P' * a.matricize hstar θ * Q'ᵀ :=
    a.exists_factor_reshapeSplit_envPaired θ S oP oQ oAdj oEdge oSide oPart hstar hxsS hysS
  -- (split) the two side-splits have comparable rank (boundary Kronecker factor is a unit).
  have hsplit : (reshapeSplit eS eB (a.SCoreMat θs S)).rank
      ≤ (reshapeSplit eS eB (a.envPairedMat θ θ S)).rank :=
    a.rank_reshapeSplit_SCore_le_envPaired hmn hcrit hts S K hKiff hbdry
      oP oQ oAdj oEdge oPS oSide oPart hstar hstarEq
  -- The rank chain: `r ≤ rank(split SCore θs) ≤ rank(split env θθ) ≤ rank(matricize θ) < r`.
  have hrank_a : a.r s(xs, ys) ≤ (reshapeSplit eS eB (a.SCoreMat θs S)).rank := by
    have h1 : (a.matricizeOf hstar Tstar).rank = a.r s(xs, ys) := hTfull xs ys hstar
    rw [← h1, hC4a]
    exact rank_mul_mul_transpose_le Er (reshapeSplit eS eB (a.SCoreMat θs S)) Ec
  have hrank_b : (reshapeSplit eS eB (a.envPairedMat θ θ S)).rank
      ≤ (a.matricize hstar θ).rank := by
    rw [hC4b]
    exact rank_mul_mul_transpose_le P' (a.matricize hstar θ) Q'
  have hfin : a.r s(xs, ys) ≤ (a.matricize hstar θ).rank :=
    le_trans hrank_a (le_trans hsplit hrank_b)
  omega


end Arch

end TTN
