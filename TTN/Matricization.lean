import TTN.Contraction

/-!
# Edge matricization and the cut factorization

The edge matricization `T(θ)^{(e)}` and the cut factorization `T(θ)^{(e)} = F_e H_eᵀ`
used throughout the loss-landscape argument.

## What is here
* `Side h` — the bipartition of nodes obtained by deleting an internal edge from the
  tree (the component of the chosen endpoint). Decidable, since deleting an edge keeps
  the adjacency decidable and `V` is finite.
* `Row h`, `Col h`, `extSplit` — the reshape `Ext ≃ Row × Col` splitting external
  modes across the cut.
* `matricize h θ` — the edge matricization `T(θ)^{(e)}` as a `Matrix (Row h) (Col h) ℝ`.
* `cut_factorization` (existence form) + `matricize_rank_le` — the rank bound
  `rank(T(θ)^{(e)}) ≤ r_e` used by the forward direction of realizability.

The bipartition is oriented by an adjacency `h : G.Adj u w` (the matricization is
symmetric up to transpose); `Side h` is the component of `u` after deleting `s(u, w)`.
Concrete `F_e`, `H_e` and their kernels and Gram matrices are introduced in the
loss-landscape modules that use them.
-/

open scoped Matrix

namespace TTN

namespace Arch

variable (a : Arch)

/-- The **cut bipartition**: nodes reachable from `u` after deleting the internal edge
`s(u, w)` from the tree. Since the edge is a bridge (tree ⇒ every edge is a bridge),
`u ∈ Side` and `w ∉ Side`, and this is one of the two components of the cut. -/
@[nolint unusedArguments]
def Side {u w : a.V} (_h : a.G.Adj u w) : a.V → Prop :=
  fun x => (a.G.deleteEdges {s(u, w)}).Reachable u x

instance {u w : a.V} (h : a.G.Adj u w) : DecidablePred (a.Side h) := by
  unfold Side; intro x; infer_instance

/-- Row index of the edge matricization: external modes on the `Side` of the cut
(`m_e = ∏_{v ∈ V_e} n_v`). -/
def Row {u w : a.V} (h : a.G.Adj u w) : Type := (v : {x : a.V // a.Side h x}) → Fin (a.n v)

/-- Column index of the edge matricization: external modes off the `Side` of the cut
(`m_eᶜ = ∏_{v ∈ V_eᶜ} n_v`). -/
def Col {u w : a.V} (h : a.G.Adj u w) : Type := (v : {x : a.V // ¬ a.Side h x}) → Fin (a.n v)

instance {u w : a.V} (h : a.G.Adj u w) : Fintype (a.Row h) := by unfold Row; infer_instance
instance {u w : a.V} (h : a.G.Adj u w) : Fintype (a.Col h) := by unfold Col; infer_instance
instance {u w : a.V} (h : a.G.Adj u w) : DecidableEq (a.Row h) := by unfold Row; infer_instance
instance {u w : a.V} (h : a.G.Adj u w) : DecidableEq (a.Col h) := by unfold Col; infer_instance

/-- Reshape the external index across the cut: `Ext ≃ Row × Col`. -/
def extSplit {u w : a.V} (h : a.G.Adj u w) : a.Ext ≃ a.Row h × a.Col h :=
  Equiv.piEquivPiSubtypeProd (a.Side h) (fun v => Fin (a.n v))

/-- **The cut has a unique crossing edge** (the bridge property in disguise): any edge
`s(x, y) ≠ s(u, w)` keeps its endpoints on the same side of the cut. This is the
mathematical heart of the cut factorization — it makes the bond sum split cleanly. -/
theorem side_iff_of_adj {u w : a.V} (h : a.G.Adj u w) {x y : a.V}
    (hxy : a.G.Adj x y) (hne : s(x, y) ≠ s(u, w)) : a.Side h x ↔ a.Side h y := by
  have hadj : (a.G.deleteEdges {s(u, w)}).Adj x y :=
    SimpleGraph.deleteEdges_adj.mpr ⟨hxy, by simpa using hne⟩
  unfold Side
  exact ⟨fun r => r.trans hadj.reachable, fun r => r.trans hadj.symm.reachable⟩

/-- **The two sides of a cut are complementary**: a node is on the `w`-side of the cut at
`s(u, w)` iff it is not on the `u`-side. The tree edge is a bridge, so deleting it leaves
exactly two components, which cover `V` and are disjoint. -/
theorem side_symm_iff_not_side {u w : a.V} (h : a.G.Adj u w) (z : a.V) :
    a.Side h.symm z ↔ ¬ a.Side h z := by
  have hbridge : ¬ (a.G.deleteEdges {s(u, w)}).Reachable u w :=
    SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp a.hT.isAcyclic h
  have hsymm : a.Side h.symm z ↔ (a.G.deleteEdges {s(u, w)}).Reachable w z := by
    change (a.G.deleteEdges {s(w, u)}).Reachable w z ↔ _
    rw [show a.G.deleteEdges {s(w, u)} = a.G.deleteEdges {s(u, w)} by rw [Sym2.eq_swap]]
  have step : ∀ {s t : a.V}, a.G.Adj s t →
      ((a.G.deleteEdges {s(u, w)}).Reachable u s ∨ (a.G.deleteEdges {s(u, w)}).Reachable w s) →
      ((a.G.deleteEdges {s(u, w)}).Reachable u t ∨ (a.G.deleteEdges {s(u, w)}).Reachable w t) := by
    intro s t hadj hP
    by_cases he : s(s, t) = s(u, w)
    · rw [Sym2.eq_iff] at he
      rcases he with ⟨_, htw⟩ | ⟨_, htu⟩
      · exact htw ▸ Or.inr (SimpleGraph.Reachable.refl _)
      · exact htu ▸ Or.inl (SimpleGraph.Reachable.refl _)
    · have hH : (a.G.deleteEdges {s(u, w)}).Adj s t :=
        SimpleGraph.deleteEdges_adj.mpr ⟨hadj, by simpa using he⟩
      exact hP.imp (·.trans hH.reachable) (·.trans hH.reachable)
  have gen : ∀ {s t : a.V}, a.G.Walk s t →
      ((a.G.deleteEdges {s(u, w)}).Reachable u s ∨ (a.G.deleteEdges {s(u, w)}).Reachable w s) →
      ((a.G.deleteEdges {s(u, w)}).Reachable u t ∨ (a.G.deleteEdges {s(u, w)}).Reachable w t) := by
    intro s t W
    induction W with
    | nil => exact id
    | cons hadj _ ih => exact fun hP => ih (step hadj hP)
  have cover : (a.G.deleteEdges {s(u, w)}).Reachable u z
      ∨ (a.G.deleteEdges {s(u, w)}).Reachable w z := by
    obtain ⟨W⟩ := a.hT.connected.preconnected u z
    exact gen W (Or.inl (SimpleGraph.Reachable.refl u))
  rw [hsymm]
  constructor
  · intro hwz huz; exact hbridge (huz.trans hwz.symm)
  · intro huz; exact cover.resolve_left huz

/-- The **edge matricization** `T(θ)^{(e)}` for the internal edge `e = s(u, w)`: the
represented tensor reshaped into a matrix with rows indexed by external modes on the
`Side` of the cut and columns by external modes off it. -/
noncomputable def matricize {u w : a.V} (h : a.G.Adj u w) (θ : a.Param) :
    Matrix (a.Row h) (a.Col h) ℝ :=
  fun row col => a.represented θ ((a.extSplit h).symm (row, col))

/-! ### Infrastructure for the cut factorization

We split the global bond sum across the unique crossing edge `e₀ = s(u,w)`. Every other
edge keeps its endpoints on a single side of the cut, so the bond space factors as
`(value on e₀) × (bonds on the Side) × (bonds on the Col)`. -/

/-- The cut edge `e₀ = s(u, w)` as an element of the edge set. -/
abbrev cutEdge {u w : a.V} (h : a.G.Adj u w) : a.G.edgeSet :=
  ⟨s(u, w), by simpa using h⟩

/-- An edge lies entirely on the `Side` of the cut if both endpoints do. -/
def EdgeSide {u w : a.V} (h : a.G.Adj u w) (e : a.G.edgeSet) : Prop :=
  ∀ x ∈ e.1, a.Side h x

instance instDecidableEdgeSide {u w : a.V} (h : a.G.Adj u w) :
    DecidablePred (a.EdgeSide h) := by
  intro e; unfold EdgeSide; infer_instance

/-- Bond indices on the **side-edges**: edges other than `e₀` with both ends on the Side. -/
def BondSide {u w : a.V} (h : a.G.Adj u w) : Type :=
  (e : {e : a.G.edgeSet // e ≠ a.cutEdge h ∧ a.EdgeSide h e}) → Fin (a.r e.1.1)

/-- Bond indices on the **column-edges**: edges other than `e₀` with both ends off the Side. -/
def BondCol {u w : a.V} (h : a.G.Adj u w) : Type :=
  (e : {e : a.G.edgeSet // e ≠ a.cutEdge h ∧ ¬ a.EdgeSide h e}) → Fin (a.r e.1.1)

instance {u w : a.V} (h : a.G.Adj u w) : Fintype (a.BondSide h) := by
  unfold BondSide; infer_instance
instance {u w : a.V} (h : a.G.Adj u w) : Fintype (a.BondCol h) := by
  unfold BondCol; infer_instance

/-- **Key bridge step**: for a node `v` on the Side, any incident edge other than the cut
edge keeps its other endpoint on the Side too (so it is a side-edge). -/
theorem edgeSide_of_side {u w : a.V} (h : a.G.Adj u w) {v : a.V} (hv : a.Side h v)
    (e : a.G.edgeSet) (hve : v ∈ e.1) (hne : e ≠ a.cutEdge h) : a.EdgeSide h e := by
  intro x hx
  by_cases hxv : x = v
  · exact hxv ▸ hv
  · have hvx : v ≠ x := fun hc => hxv hc.symm
    have hek : e.1 = s(v, x) := (Sym2.mem_and_mem_iff hvx).mp ⟨hve, hx⟩
    have hmem : s(v, x) ∈ a.G.edgeSet := hek ▸ e.2
    have hadj : a.G.Adj v x := by rwa [SimpleGraph.mem_edgeSet] at hmem
    have hne' : s(v, x) ≠ s(u, w) := by
      intro hc
      exact hne (Subtype.ext (hek.trans hc))
    exact (a.side_iff_of_adj h hadj hne').mp hv

/-- Forward map of the bond-splitting equivalence. -/
def bondToFun {u w : a.V} (h : a.G.Adj u w) (b : a.Bond) :
    Fin (a.r (a.cutEdge h).1) × a.BondSide h × a.BondCol h :=
  (b (a.cutEdge h), (fun e => b e.1), (fun e => b e.1))

/-- Inverse map of the bond-splitting equivalence. -/
def bondInvFun {u w : a.V} (h : a.G.Adj u w)
    (p : Fin (a.r (a.cutEdge h).1) × a.BondSide h × a.BondCol h) : a.Bond :=
  fun e =>
    if he : e = a.cutEdge h then he.symm ▸ p.1
    else if hs : a.EdgeSide h e then p.2.1 ⟨e, he, hs⟩
    else p.2.2 ⟨e, he, hs⟩

/-- The bond space splits as `(value on e₀) × (side bonds) × (column bonds)`. -/
def bondEquiv {u w : a.V} (h : a.G.Adj u w) :
    a.Bond ≃ Fin (a.r (a.cutEdge h).1) × a.BondSide h × a.BondCol h where
  toFun := a.bondToFun h
  invFun := a.bondInvFun h
  left_inv := by
    intro b
    funext e
    simp only [bondToFun, bondInvFun]
    split_ifs with he hs
    · subst he; rfl
    · rfl
    · rfl
  right_inv := by
    rintro ⟨k, bs, bc⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · change a.bondInvFun h (k, bs, bc) (a.cutEdge h) = k
      simp [bondInvFun]
    · funext e
      obtain ⟨e, hne, hs⟩ := e
      simp only [bondToFun, bondInvFun, dif_neg hne, dif_pos hs]
    · funext e
      obtain ⟨e, hne, hs⟩ := e
      simp only [bondToFun, bondInvFun, dif_neg hne, dif_neg hs]

@[simp] theorem bondEquiv_symm_apply {u w : a.V} (h : a.G.Adj u w)
    (p : Fin (a.r (a.cutEdge h).1) × a.BondSide h × a.BondCol h) :
    (a.bondEquiv h).symm p = a.bondInvFun h p := rfl

/-- On a Side node, the restricted bond is independent of the column-bond coordinate. -/
theorem restrict_bondInvFun_side {u w : a.V} (h : a.G.Adj u w) {v : a.V} (hv : a.Side h v)
    (k : Fin (a.r (a.cutEdge h).1)) (bs : a.BondSide h) (bc bc' : a.BondCol h) :
    Bond.restrict (a.bondInvFun h (k, bs, bc)) v
      = Bond.restrict (a.bondInvFun h (k, bs, bc')) v := by
  funext e
  simp only [Bond.restrict, bondInvFun]
  by_cases he0 : (⟨e.1, e.2.1⟩ : a.G.edgeSet) = a.cutEdge h
  · rw [dif_pos he0, dif_pos he0]
  · have hes : a.EdgeSide h ⟨e.1, e.2.1⟩ :=
      a.edgeSide_of_side h hv ⟨e.1, e.2.1⟩ e.2.2 he0
    rw [dif_neg he0, dif_neg he0, dif_pos hes, dif_pos hes]

/-- On a non-Side node, the restricted bond is independent of the side-bond coordinate. -/
theorem restrict_bondInvFun_col {u w : a.V} (h : a.G.Adj u w) {v : a.V} (hv : ¬ a.Side h v)
    (k : Fin (a.r (a.cutEdge h).1)) (bs bs' : a.BondSide h) (bc : a.BondCol h) :
    Bond.restrict (a.bondInvFun h (k, bs, bc)) v
      = Bond.restrict (a.bondInvFun h (k, bs', bc)) v := by
  funext e
  simp only [Bond.restrict, bondInvFun]
  by_cases he0 : (⟨e.1, e.2.1⟩ : a.G.edgeSet) = a.cutEdge h
  · rw [dif_pos he0, dif_pos he0]
  · have hes : ¬ a.EdgeSide h ⟨e.1, e.2.1⟩ := fun hall => hv (hall v e.2.2)
    rw [dif_neg he0, dif_neg he0, dif_neg hes, dif_neg hes]

/-- A default column-bond, used to pin the (irrelevant) column coordinate inside `F_e`. -/
def colDefault {u w : a.V} (h : a.G.Adj u w) : a.BondCol h :=
  fun e => ⟨0, a.hr e.1.1 e.1.2⟩

/-- A default side-bond, used to pin the (irrelevant) side coordinate inside `H_e`. -/
def sideDefault {u w : a.V} (h : a.G.Adj u w) : a.BondSide h :=
  fun e => ⟨0, a.hr e.1.1 e.1.2⟩

/-- The left factor `F_e`: rows indexed by Side-external modes, columns by the cut bond. -/
noncomputable def Ffun {u w : a.V} (h : a.G.Adj u w) (θ : a.Param) :
    Matrix (a.Row h) (Fin (a.r s(u, w))) ℝ :=
  fun row k => ∑ bs : a.BondSide h,
    ∏ v : {x // a.Side h x},
      θ v.1 (Bond.restrict (a.bondInvFun h (k, bs, a.colDefault h)) v.1) (row v)

/-- The right factor `H_e`: rows indexed by Col-external modes, columns by the cut bond. -/
noncomputable def Hfun {u w : a.V} (h : a.G.Adj u w) (θ : a.Param) :
    Matrix (a.Col h) (Fin (a.r s(u, w))) ℝ :=
  fun col k => ∑ bc : a.BondCol h,
    ∏ v : {x // ¬ a.Side h x},
      θ v.1 (Bond.restrict (a.bondInvFun h (k, a.sideDefault h, bc)) v.1) (col v)

/-- Reading off a Side external mode from the reshaped index. -/
theorem extSplit_symm_row {u w : a.V} (h : a.G.Adj u w) (row : a.Row h) (col : a.Col h)
    (v : {x // a.Side h x}) : (a.extSplit h).symm (row, col) v.1 = row v := by
  have hh : (a.extSplit h).symm (row, col) v.1
      = if hp : a.Side h v.1 then row ⟨v.1, hp⟩ else col ⟨v.1, hp⟩ := rfl
  rw [hh, dif_pos v.2]

/-- Reading off a Col external mode from the reshaped index. -/
theorem extSplit_symm_col {u w : a.V} (h : a.G.Adj u w) (row : a.Row h) (col : a.Col h)
    (v : {x // ¬ a.Side h x}) : (a.extSplit h).symm (row, col) v.1 = col v := by
  have hh : (a.extSplit h).symm (row, col) v.1
      = if hp : a.Side h v.1 then row ⟨v.1, hp⟩ else col ⟨v.1, hp⟩ := rfl
  rw [hh, dif_neg v.2]

/-- The per-bond summand splits as a product over the Side times a product over the Col,
each depending only on its own bond coordinates (Side ↦ `bs`, Col ↦ `bc`). -/
theorem prod_split {u w : a.V} (h : a.G.Adj u w) (θ : a.Param)
    (row : a.Row h) (col : a.Col h)
    (k : Fin (a.r (a.cutEdge h).1)) (bs : a.BondSide h) (bc : a.BondCol h) :
    (∏ v, θ v (Bond.restrict (a.bondInvFun h (k, bs, bc)) v) ((a.extSplit h).symm (row, col) v))
      = (∏ v : {x // a.Side h x},
          θ v.1 (Bond.restrict (a.bondInvFun h (k, bs, a.colDefault h)) v.1) (row v))
        * (∏ v : {x // ¬ a.Side h x},
          θ v.1 (Bond.restrict (a.bondInvFun h (k, a.sideDefault h, bc)) v.1) (col v)) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (a.Side h) (fun v =>
    θ v (Bond.restrict (a.bondInvFun h (k, bs, bc)) v) ((a.extSplit h).symm (row, col) v))]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    rw [a.restrict_bondInvFun_side h v.2 k bs bc (a.colDefault h),
        a.extSplit_symm_row h row col v]
  · apply Finset.prod_congr rfl
    intro v _
    rw [a.restrict_bondInvFun_col h v.2 k bs (a.sideDefault h) bc,
        a.extSplit_symm_col h row col v]

/-- **Cut factorization** (concrete form): the edge matricization factors as
`F_e H_eᵀ` through the bond space `Fin (r_e)` of the cut edge, with the two explicit
half-tree contractions `Ffun`/`Hfun` as the factors. Proof reorganizes the global bond
sum as a Fubini split across the unique crossing edge `e` (the tree edge is a bridge, so
no other edge crosses the cut). -/
theorem matricize_FH {u w : a.V} (h : a.G.Adj u w) (θ : a.Param) :
    a.matricize h θ = a.Ffun h θ * (a.Hfun h θ)ᵀ := by
  ext row col
  have key : a.matricize h θ row col
      = ∑ k, ∑ bs : a.BondSide h, ∑ bc : a.BondCol h,
        (∏ v : {x // a.Side h x},
          θ v.1 (Bond.restrict (a.bondInvFun h (k, bs, a.colDefault h)) v.1) (row v))
        * (∏ v : {x // ¬ a.Side h x},
          θ v.1 (Bond.restrict (a.bondInvFun h (k, a.sideDefault h, bc)) v.1) (col v)) := by
    simp only [matricize, represented]
    rw [← Equiv.sum_comp (a.bondEquiv h).symm
      (fun b => ∏ v, θ v (Bond.restrict b v) ((a.extSplit h).symm (row, col) v))]
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl
      (fun bs _ => Finset.sum_congr rfl (fun bc _ => ?_)))
    exact a.prod_split h θ row col k bs bc
  rw [key, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.transpose_apply]
  simp only [Ffun, Hfun]
  rw [Fintype.sum_mul_sum]

/-- **Cut factorization** (existence form): `T(θ)^{(e)} = F Hᵀ` for some factors `F`, `H`.
Weakening of `matricize_FH`, which names the witnesses. -/
theorem cut_factorization {u w : a.V} (h : a.G.Adj u w) (θ : a.Param) :
    ∃ (F : Matrix (a.Row h) (Fin (a.r s(u, w))) ℝ)
      (H : Matrix (a.Col h) (Fin (a.r s(u, w))) ℝ),
      a.matricize h θ = F * Hᵀ :=
  ⟨a.Ffun h θ, a.Hfun h θ, a.matricize_FH h θ⟩

/-- Every represented tensor satisfies `rank(T(θ)^{(e)}) ≤ r_e`. The forward
direction of the realizability characterization. -/
theorem matricize_rank_le {u w : a.V} (h : a.G.Adj u w) (θ : a.Param) :
    (a.matricize h θ).rank ≤ a.r s(u, w) := by
  obtain ⟨F, H, hFH⟩ := a.cut_factorization h θ
  rw [hFH]
  calc (F * Hᵀ).rank ≤ F.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin (a.r s(u, w))) := F.rank_le_card_width
    _ = a.r s(u, w) := Fintype.card_fin _

end Arch

end TTN
