import TTN.Landscape.Descent
import TTN.Landscape.Criticality

/-!
# Stripping a full-rank side of a cut

One strip: collapse the **whole far side** of a full-rank cut `s(u, w)` into an effective
external mode at `u` (dimension `r_e`), producing the side architecture. The gauge that
orthonormalizes the far factor `H_e` is carried as an **invertible reparametrization of the
retained side** (never a mutation of the base point), so descent families on the stripped
problem pull back to families through the original point. This construction is formalized
for comparison with the prose proof; the final main theorem uses the component-supported
descent directly.

Definitions (all real):
* `sideArch h` — the `Side`-induced architecture, `u`'s external mode bumped to `n_u·r_e`.
* `sideParam h θ` — restriction of `θ` to the side, `u` folding its cut-bond mode.
* `rowPack h row j` / `rowExtract` / `jExtractS` — the `Ext`-reshape `(Row h) × Fin r_e ≃`
  side-`Ext`.
* `sideTarget h B` — the effective target read off a `Row × r_e` matrix (`B := T*⁽ᵉ⁾H₀`).
* `pullParam h θ M φ` — the strip's family map: far side frozen at `θ`, side taken from `φ`
  (unfolded), with `Mᵀ` applied on `u`'s cut-bond slot.

Main results:
* `side_induce_connected` — the side component induces a connected subgraph.
* `Ffun_eq_represented_sideParam` — the bridge `Ffun h θ = side-represented (sideParam θ)`.
* `loss_pullParam`: `L(pull φ) = L_side(φ) + C_e` for all side parameters `φ`,
  with `C_e = ½(‖T*‖² − ‖T*⁽ᵉ⁾H₀‖²)`, given `H₀ = Hfun·M` with orthonormal columns.
* `pullParam_sideParam` — the base point is on the family.
* `continuous_pullParam` — the family map is continuous.
* dormancy and rank-compression transports (`matE`-kernel and `matricize`-rank facts).
-/

open scoped Matrix

namespace TTN

namespace Arch

variable {a : Arch}

/-- The `Side` component of a cut induces a **connected** subgraph (walks in the edge-deleted
graph stay on the side and transfer to the induced graph). -/
theorem side_induce_connected {u w : a.V} (h : a.G.Adj u w) :
    (a.G.induce {x : a.V | a.Side h x}).Connected := by
  classical
  have hu : u ∈ {x : a.V | a.Side h x} := a.side_left h
  have hreach : ∀ z : {x : a.V | a.Side h x},
      (a.G.induce {x : a.V | a.Side h x}).Reachable ⟨u, hu⟩ z := by
    rintro ⟨z, hz⟩
    obtain ⟨W⟩ := (hz : a.Side h z)
    have hsupp : ∀ x ∈ W.support, x ∈ {x : a.V | a.Side h x} := by
      intro x hx
      exact ⟨W.takeUntil x hx⟩
    have hsupp' : ∀ x ∈ (W.mapLe (SimpleGraph.deleteEdges_le _)).support,
        x ∈ {x : a.V | a.Side h x} := by
      intro x hx
      apply hsupp
      rwa [SimpleGraph.Walk.support_mapLe_eq_support] at hx
    exact ⟨(W.mapLe (SimpleGraph.deleteEdges_le _)).induce _ hsupp'⟩
  rw [SimpleGraph.connected_iff]
  exact ⟨fun x y => (hreach x).symm.trans (hreach y), ⟨⟨u, hu⟩⟩⟩

/-- **The side architecture**: vertices are the `u`-side of the cut at `s(u, w)`, the graph is
induced, bond dimensions are inherited, and `u` absorbs the cut bond as an external mode
(dimension bumped to `n_u · r_e`). -/
noncomputable def sideArch {u w : a.V} (h : a.G.Adj u w) : Arch where
  V := ↥{x : a.V | a.Side h x}
  G := a.G.induce {x : a.V | a.Side h x}
  hT := by
    rw [SimpleGraph.isTree_iff]
    exact ⟨a.side_induce_connected h, a.hT.isAcyclic.induce _⟩
  r := fun e => a.r (e.map Subtype.val)
  n := fun x => if x.1 = u then a.n u * a.r s(u, w) else a.n x.1
  hr := by
    intro e he
    apply a.hr
    induction e using Sym2.ind with
    | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at he
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
      exact he
  hn := by
    intro x
    by_cases hx : x.1 = u
    · simp only [hx, if_pos]
      exact Nat.mul_pos (a.hn u) (a.hr s(u, w) (by rw [SimpleGraph.mem_edgeSet]; exact h))
    · simp only [hx, if_neg, not_false_iff]
      exact a.hn x.1

variable {u w : a.V}

/-- `u` as a vertex of the side architecture. -/
def uSide (h : a.G.Adj u w) : (a.sideArch h).V := ⟨u, a.side_left h⟩

/-- At the absorbing node `u`, the side external dimension is the bumped `n_u · r_e`. -/
theorem sideArch_n_eq_u (h : a.G.Adj u w) (y : (a.sideArch h).V) (hy : y.1 = u) :
    (a.sideArch h).n y = a.n u * a.r s(u, w) := by
  show (if y.1 = u then a.n u * a.r s(u, w) else a.n y.1) = _
  rw [if_pos hy]

/-- Away from the absorbing node, the side external dimension is unchanged. -/
theorem sideArch_n_eq_ne (h : a.G.Adj u w) (y : (a.sideArch h).V) (hy : y.1 ≠ u) :
    (a.sideArch h).n y = a.n y.1 := by
  show (if y.1 = u then a.n u * a.r s(u, w) else a.n y.1) = _
  rw [if_neg hy]

/-- An edge of the side graph maps (under `Subtype.val`) to an edge of the original graph. -/
theorem side_edge_mem (h : a.G.Adj u w) {e : Sym2 (a.sideArch h).V}
    (he : e ∈ (a.sideArch h).G.edgeSet) : Sym2.map Subtype.val e ∈ a.G.edgeSet := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.mem_edgeSet] at he
    exact (SimpleGraph.mem_edgeSet a.G).mpr he

/-- An incidence in the side architecture maps to an incidence in the original graph. Note
`(sideArch h).r e' = a.r (e'.map val)` *definitionally*, so bond indices transport
cast-free. -/
def incSideToOrig (h : a.G.Adj u w) {vr : (a.sideArch h).V}
    (e' : (a.sideArch h).Inc vr) : a.Inc vr.1 :=
  ⟨Sym2.map Subtype.val e'.1, a.side_edge_mem h e'.2.1, Sym2.mem_map.mpr ⟨vr, e'.2.2, rfl⟩⟩

/-- An original incidence at a side vertex, other than the cut edge, keeps both endpoints on
the side (`edgeSide_of_side`). -/
theorem inc_side_subset (h : a.G.Adj u w) {vr : (a.sideArch h).V} (e'' : a.Inc vr.1)
    (hne : (⟨e''.1, e''.2.1⟩ : a.G.edgeSet) ≠ a.cutEdge h) :
    ∀ y ∈ e''.1, y ∈ {x : a.V | a.Side h x} := by
  intro y hy
  exact a.edgeSide_of_side h vr.2 ⟨e''.1, e''.2.1⟩ e''.2.2 hne y hy

/-- An incidence at a side vertex other than `u` is never the cut edge. -/
theorem inc_ne_cut_of_ne_u (h : a.G.Adj u w) {vr : (a.sideArch h).V} (hvu : vr.1 ≠ u)
    (e'' : a.Inc vr.1) : (⟨e''.1, e''.2.1⟩ : a.G.edgeSet) ≠ a.cutEdge h := by
  intro hc
  have hval : e''.1 = s(u, w) := congrArg Subtype.val hc
  have hmem : vr.1 ∈ e''.1 := e''.2.2
  rw [hval, Sym2.mem_iff] at hmem
  rcases hmem with hh | hh
  · exact hvu hh
  · exact a.not_side_right h ((congrArg (a.Side h) hh).mp vr.2)

/-- An original edge with both endpoints on the side, attached, is a side edge. -/
theorem side_edge_mem' (h : a.G.Adj u w) :
    ∀ (s : Sym2 a.V), s ∈ a.G.edgeSet →
      ∀ (hp : ∀ y ∈ s, y ∈ {x : a.V | a.Side h x}),
      Sym2.attachWith s hp ∈ (a.sideArch h).G.edgeSet := by
  intro s
  induction s using Sym2.ind with
  | _ p q =>
    intro hs hp
    rw [SimpleGraph.mem_edgeSet] at hs
    exact (SimpleGraph.mem_edgeSet _).mpr hs

/-- Push an original incidence at a side vertex (whose edge avoids the cut) into the side
architecture. -/
def origIncToSide (h : a.G.Adj u w) {vr : (a.sideArch h).V} (e'' : a.Inc vr.1)
    (hp : ∀ y ∈ e''.1, y ∈ {x : a.V | a.Side h x}) : (a.sideArch h).Inc vr :=
  ⟨Sym2.attachWith e''.1 hp, a.side_edge_mem' h e''.1 e''.2.1 hp, by
      have hmem : vr.1 ∈ Sym2.map Subtype.val (Sym2.attachWith e''.1 hp) := by
        rw [Sym2.attachWith_map_subtypeVal]; exact e''.2.2
      obtain ⟨y, hy, hyv⟩ := Sym2.mem_map.mp hmem
      exact (Subtype.ext hyv : y = vr) ▸ hy⟩

/-- Round-trip: `incSideToOrig` undoes `origIncToSide`. -/
theorem incSideToOrig_origIncToSide (h : a.G.Adj u w) {vr : (a.sideArch h).V}
    (e'' : a.Inc vr.1) (hp : ∀ y ∈ e''.1, y ∈ {x : a.V | a.Side h x}) :
    a.incSideToOrig h (a.origIncToSide h e'' hp) = e'' := by
  apply Subtype.ext
  show Sym2.map Subtype.val (Sym2.attachWith e''.1 hp) = e''.1
  exact Sym2.attachWith_map_subtypeVal hp

/-- Round-trip: `origIncToSide` undoes `incSideToOrig`. -/
theorem origIncToSide_incSideToOrig (h : a.G.Adj u w) {vr : (a.sideArch h).V}
    (e' : (a.sideArch h).Inc vr)
    (hp : ∀ y ∈ (a.incSideToOrig h e').1, y ∈ {x : a.V | a.Side h x}) :
    a.origIncToSide h (a.incSideToOrig h e') hp = e' := by
  apply Subtype.ext
  exact attachWith_map_subtypeVal_self e'.1 hp

/-- Mode multiplications at the same slot compose by matrix multiplication. -/
theorem modeMul_modeMul (v : a.V) (e : a.Inc v)
    (N₂ N₁ : Matrix (Fin (a.r e.1)) (Fin (a.r e.1)) ℝ) (W : a.NodeTensor v) :
    a.modeMul v e N₂ (a.modeMul v e N₁ W) = a.modeMul v e (N₂ * N₁) W := by
  funext bi x
  simp only [modeMul, Function.update_self, Function.update_idem, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- Mode multiplication by the identity is the identity. -/
theorem modeMul_one (v : a.V) (e : a.Inc v) (W : a.NodeTensor v) :
    a.modeMul v e (1 : Matrix (Fin (a.r e.1)) (Fin (a.r e.1)) ℝ) W = W := by
  funext bi x
  simp only [modeMul, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq (Finset.univ) (bi e) (fun k => W (Function.update bi e k) x)]
  simp [Function.update_eq_self]

/-- **The fold**: embed `(Row h) × Fin r_e` into the side `Ext` (the `u`-slot packs
`(row_u, j)` into the bumped mode; every other side node passes through). -/
noncomputable def rowPack (h : a.G.Adj u w) (row : a.Row h) (j : Fin (a.r s(u, w))) :
    (a.sideArch h).Ext :=
  fun y => if hy : y.1 = u then
    finCongr (a.sideArch_n_eq_u h y hy).symm
      (finProdFinEquiv (row ⟨u, a.side_left h⟩, j))
  else
    finCongr (a.sideArch_n_eq_ne h y hy).symm (row ⟨y.1, y.2⟩)

/-- Extract the `Row` data (u un-bumped) from a side external index. -/
noncomputable def rowExtract (h : a.G.Adj u w) (xr : (a.sideArch h).Ext) : a.Row h :=
  fun y => if hyu : y.1 = u then
    finCongr (show a.n u = a.n y.1 by rw [hyu])
      (finProdFinEquiv.symm
        (finCongr (a.sideArch_n_eq_u h ⟨y.1, y.2⟩ hyu) (xr ⟨y.1, y.2⟩))).1
  else
    finCongr (a.sideArch_n_eq_ne h ⟨y.1, y.2⟩ hyu) (xr ⟨y.1, y.2⟩)

/-- Extract the folded cut-bond value from a side external index. -/
noncomputable def jExtractS (h : a.G.Adj u w) (xr : (a.sideArch h).Ext) :
    Fin (a.r s(u, w)) :=
  (finProdFinEquiv.symm
    (finCongr (a.sideArch_n_eq_u h (uSide h) rfl) (xr (uSide h)))).2

/-- **The effective target** read off a `Row × r_e` matrix (used with `B := T*⁽ᵉ⁾ · H₀`). -/
noncomputable def sideTarget (h : a.G.Adj u w)
    (B : Matrix (a.Row h) (Fin (a.r s(u, w))) ℝ) (xr : (a.sideArch h).Ext) : ℝ :=
  B (a.rowExtract h xr) (a.jExtractS h xr)

/-- **Side restriction of the parameters**: side nodes keep their tensors, with `u` folding
its cut-bond mode into the bumped external mode. -/
noncomputable def sideParam (h : a.G.Adj u w) (θ : a.Param) : (a.sideArch h).Param :=
  fun vr bi' xr' =>
    if hvu : vr.1 = u then
      θ vr.1
        (fun e'' => if he : (⟨e''.1, e''.2.1⟩ : a.G.edgeSet) = a.cutEdge h
          then finCongr (congrArg a.r (congrArg Subtype.val he).symm)
            (finProdFinEquiv.symm (finCongr (a.sideArch_n_eq_u h vr hvu) xr')).2
          else finCongr (congrArg a.r (Sym2.attachWith_map_subtypeVal
              (a.inc_side_subset h e'' he)))
            (bi' (a.origIncToSide h e'' (a.inc_side_subset h e'' he))))
        (finCongr (show a.n u = a.n vr.1 by rw [hvu])
          (finProdFinEquiv.symm (finCongr (a.sideArch_n_eq_u h vr hvu) xr')).1)
    else
      θ vr.1
        (fun e'' => finCongr (congrArg a.r (Sym2.attachWith_map_subtypeVal
            (a.inc_side_subset h e'' (a.inc_ne_cut_of_ne_u h hvu e''))))
          (bi' (a.origIncToSide h e''
            (a.inc_side_subset h e'' (a.inc_ne_cut_of_ne_u h hvu e'')))))
        (finCongr (a.sideArch_n_eq_ne h vr hvu) xr')

/-- **The unfolded `u`-tensor of a side parameter**: read `φ` at `u`, packing the original
external index and the cut-bond value into the bumped mode. -/
noncomputable def unfoldU (h : a.G.Adj u w) (φ : (a.sideArch h).Param) : a.NodeTensor u :=
  fun bi₀ xv₀ => φ (uSide h) (fun e' => bi₀ (a.incSideToOrig h e'))
    (finCongr (a.sideArch_n_eq_u h (uSide h) rfl).symm
      (finProdFinEquiv (xv₀, bi₀ (adjIncLeft h))))

/-- **The strip's family map**: far side frozen at `θ`; side nodes taken from `φ` — `u`'s
bumped mode unfolded back into `(external, cut-bond)` with the gauge `Mᵀ` applied on the
cut-bond slot (`modeMul`). Descent families on the side problem pull back through this to
families through the original point. -/
noncomputable def pullParam (h : a.G.Adj u w) (θ : a.Param)
    (M : Matrix (Fin (a.r s(u, w))) (Fin (a.r s(u, w))) ℝ)
    (φ : (a.sideArch h).Param) : a.Param :=
  fun v bi xv =>
    if hvu : v = u then
      a.modeMul u (adjIncLeft h) Mᵀ (a.unfoldU h φ) (hvu ▸ bi)
        (finCongr (congrArg a.n hvu) xv)
    else if hv : a.Side h v then
      φ ⟨v, hv⟩ (fun e' => bi (a.incSideToOrig h e'))
        (finCongr (a.sideArch_n_eq_ne h ⟨v, hv⟩ hvu).symm xv)
    else θ v bi xv

/-! ### Bond correspondence: side-architecture bonds ↔ side-edges of the cut -/

/-- The `EdgeSide` predicate, rephrased as set membership (for `Sym2.attachWith`). -/
theorem edgeSide_mem_side (h : a.G.Adj u w)
    (e : {e : a.G.edgeSet // e ≠ a.cutEdge h ∧ a.EdgeSide h e}) :
    ∀ y ∈ e.1.1, y ∈ {x : a.V | a.Side h x} :=
  fun y hy => e.2.2 y hy

/-- A side-architecture edge, pushed to the original graph, avoids the cut edge and keeps
both endpoints on the `Side`. -/
def sideEdgeIdx (h : a.G.Adj u w) (E : (a.sideArch h).G.edgeSet) :
    {e : a.G.edgeSet // e ≠ a.cutEdge h ∧ a.EdgeSide h e} :=
  ⟨⟨Sym2.map Subtype.val E.1, a.side_edge_mem h E.2⟩,
    fun hc => by
      have hw : w ∈ Sym2.map Subtype.val E.1 := by
        rw [show Sym2.map Subtype.val E.1 = s(u, w) from congrArg Subtype.val hc]
        exact Sym2.mem_mk_right u w
      obtain ⟨y, _, hyw⟩ := Sym2.mem_map.mp hw
      have hyS := y.2
      rw [hyw] at hyS
      exact a.not_side_right h hyS,
    fun x hx => by
      obtain ⟨y, _, hyx⟩ := Sym2.mem_map.mp hx
      rw [← hyx]
      exact y.2⟩

/-- Bond transport from the side-edge subtype to the side architecture (cast-free: the
side architecture's bond dimension at `E` is *definitionally* `a.r (E.1.map val)`). -/
def sideBondOf (h : a.G.Adj u w) (bs : a.BondSide h) : (a.sideArch h).Bond :=
  fun E => bs (a.sideEdgeIdx h E)

/-- Bond transport from the side architecture back to the side-edge subtype. -/
noncomputable def bondSideOf (h : a.G.Adj u w) (b : (a.sideArch h).Bond) : a.BondSide h :=
  fun e => finCongr (congrArg a.r (Sym2.attachWith_map_subtypeVal (a.edgeSide_mem_side h e)))
    (b ⟨Sym2.attachWith e.1.1 (a.edgeSide_mem_side h e),
        a.side_edge_mem' h e.1.1 e.1.2 (a.edgeSide_mem_side h e)⟩)

/-- The bond spaces of the cut correspondence: side-edge bonds ≃ side-architecture bonds. -/
noncomputable def sideBondEquiv (h : a.G.Adj u w) : a.BondSide h ≃ (a.sideArch h).Bond where
  toFun := a.sideBondOf h
  invFun := a.bondSideOf h
  left_inv := by
    intro bs
    funext e
    have hkey : a.sideEdgeIdx h ⟨Sym2.attachWith e.1.1 (a.edgeSide_mem_side h e),
        a.side_edge_mem' h e.1.1 e.1.2 (a.edgeSide_mem_side h e)⟩ = e :=
      Subtype.ext (Subtype.ext (Sym2.attachWith_map_subtypeVal (a.edgeSide_mem_side h e)))
    apply Fin.ext
    simp only [bondSideOf, sideBondOf, finCongr_apply_coe]
    exact congrArg (fun z : {e' : a.G.edgeSet // e' ≠ a.cutEdge h ∧ a.EdgeSide h e'} =>
      ((bs z).val : ℕ)) hkey
  right_inv := by
    intro b
    funext E
    have hkey : ∀ (hp : ∀ y ∈ Sym2.map Subtype.val E.1, y ∈ {x : a.V | a.Side h x})
        (hmem : Sym2.attachWith (Sym2.map Subtype.val E.1) hp ∈ (a.sideArch h).G.edgeSet),
        (⟨Sym2.attachWith (Sym2.map Subtype.val E.1) hp, hmem⟩ : (a.sideArch h).G.edgeSet)
          = E :=
      fun hp _ => Subtype.ext (attachWith_map_subtypeVal_self E.1 hp)
    apply Fin.ext
    simp only [sideBondOf, bondSideOf, sideEdgeIdx]
    exact congrArg (fun Z : (a.sideArch h).G.edgeSet => ((b Z).val : ℕ)) (hkey _ _)

/-- Value-congruence for `finProdFinEquiv` through component-wise `val` equality. -/
theorem finProdFinEquiv_val_congr {m n : ℕ} (p p' : Fin m × Fin n)
    (h1 : p.1.val = p'.1.val) (h2 : p.2.val = p'.2.val) :
    (finProdFinEquiv p).val = (finProdFinEquiv p').val := by
  have hp : p = p' := Prod.ext (Fin.ext h1) (Fin.ext h2)
  rw [hp]

/-- A side incidence pushed to the original graph is never the cut edge. -/
theorem incSideToOrig_ne_cut (h : a.G.Adj u w) {vr : (a.sideArch h).V}
    (e' : (a.sideArch h).Inc vr) :
    (⟨(a.incSideToOrig h e').1, (a.incSideToOrig h e').2.1⟩ : a.G.edgeSet)
      ≠ a.cutEdge h := by
  intro hc
  have hw : w ∈ (a.incSideToOrig h e').1 := by
    rw [show (a.incSideToOrig h e').1 = s(u, w) from congrArg Subtype.val hc]
    exact Sym2.mem_mk_right u w
  obtain ⟨y, _, hyw⟩ := Sym2.mem_map.mp hw
  have hyS := y.2
  rw [hyw] at hyS
  exact a.not_side_right h hyS

/-- Per-node summand match away from `u` (`represented_sideParam` engine). -/
theorem sideParam_sideBondOf_ne (h : a.G.Adj u w) (θ : a.Param) (row : a.Row h)
    (j : Fin (a.r s(u, w))) (bs : a.BondSide h) (vr : (a.sideArch h).V) (hvu : vr.1 ≠ u) :
    a.sideParam h θ vr (Bond.restrict (a.sideBondOf h bs) vr) (a.rowPack h row j vr)
      = θ vr.1 (Bond.restrict (a.bondInvFun h (j, bs, a.colDefault h)) vr.1)
          (row ⟨vr.1, vr.2⟩) := by
  classical
  rw [sideParam, dif_neg hvu]
  congr 1
  · funext e''
    have hne : (⟨e''.1, e''.2.1⟩ : a.G.edgeSet) ≠ a.cutEdge h :=
      a.inc_ne_cut_of_ne_u h hvu e''
    have hes : a.EdgeSide h ⟨e''.1, e''.2.1⟩ :=
      a.inc_side_subset h e'' (a.inc_ne_cut_of_ne_u h hvu e'')
    have hkey : a.sideEdgeIdx h
        ⟨(a.origIncToSide h e''
            (a.inc_side_subset h e'' (a.inc_ne_cut_of_ne_u h hvu e''))).1,
          (a.origIncToSide h e''
            (a.inc_side_subset h e'' (a.inc_ne_cut_of_ne_u h hvu e''))).2.1⟩
        = ⟨⟨e''.1, e''.2.1⟩, hne, hes⟩ :=
      Subtype.ext (Subtype.ext (Sym2.attachWith_map_subtypeVal
        (a.inc_side_subset h e'' (a.inc_ne_cut_of_ne_u h hvu e''))))
    apply Fin.ext
    simp only [Bond.restrict, sideBondOf, bondInvFun, dif_neg hne, dif_pos hes,
      finCongr_apply_coe]
    exact congrArg (fun z : {e : a.G.edgeSet // e ≠ a.cutEdge h ∧ a.EdgeSide h e} =>
      ((bs z).val : ℕ)) hkey
  · apply Fin.ext
    rw [show a.rowPack h row j vr = finCongr (a.sideArch_n_eq_ne h vr hvu).symm
        (row ⟨vr.1, vr.2⟩) from dif_neg hvu]
    simp only [finCongr_apply_coe]

/-- Per-node summand match at `u` (`represented_sideParam` engine). -/
theorem sideParam_sideBondOf_u (h : a.G.Adj u w) (θ : a.Param) (row : a.Row h)
    (j : Fin (a.r s(u, w))) (bs : a.BondSide h) (vr : (a.sideArch h).V) (hvu : vr.1 = u) :
    a.sideParam h θ vr (Bond.restrict (a.sideBondOf h bs) vr) (a.rowPack h row j vr)
      = θ vr.1 (Bond.restrict (a.bondInvFun h (j, bs, a.colDefault h)) vr.1)
          (row ⟨vr.1, vr.2⟩) := by
  classical
  have hval : ∀ {x y : a.G.edgeSet} (hxy : x = y) (k' : Fin (a.r x.1)),
      ((hxy ▸ k' : Fin (a.r y.1))).val = k'.val := fun hxy k' => by cases hxy; rfl
  have hfold : finProdFinEquiv.symm
      (finCongr (a.sideArch_n_eq_u h vr hvu) (a.rowPack h row j vr))
      = (row ⟨u, a.side_left h⟩, j) := by
    rw [show a.rowPack h row j vr = finCongr (a.sideArch_n_eq_u h vr hvu).symm
        (finProdFinEquiv (row ⟨u, a.side_left h⟩, j)) from dif_pos hvu,
      finCongr_finCongr_symm, Equiv.symm_apply_apply]
  have hfold1 : (finProdFinEquiv.symm
      (finCongr (a.sideArch_n_eq_u h vr hvu) (a.rowPack h row j vr))).1
      = row ⟨u, a.side_left h⟩ := congrArg Prod.fst hfold
  have hfold2 : (finProdFinEquiv.symm
      (finCongr (a.sideArch_n_eq_u h vr hvu) (a.rowPack h row j vr))).2
      = j := congrArg Prod.snd hfold
  rw [sideParam, dif_pos hvu, hfold1, hfold2]
  congr 1
  · funext e''
    by_cases he : (⟨e''.1, e''.2.1⟩ : a.G.edgeSet) = a.cutEdge h
    · rw [dif_pos he]
      apply Fin.ext
      simp only [Bond.restrict, bondInvFun, dif_pos he, finCongr_apply_coe]
      exact (hval he.symm j).symm
    · rw [dif_neg he]
      have hes : a.EdgeSide h ⟨e''.1, e''.2.1⟩ := a.inc_side_subset h e'' he
      have hkey : a.sideEdgeIdx h
          ⟨(a.origIncToSide h e'' (a.inc_side_subset h e'' he)).1,
            (a.origIncToSide h e'' (a.inc_side_subset h e'' he)).2.1⟩
          = ⟨⟨e''.1, e''.2.1⟩, he, hes⟩ :=
        Subtype.ext (Subtype.ext (Sym2.attachWith_map_subtypeVal
          (a.inc_side_subset h e'' he)))
      apply Fin.ext
      simp only [Bond.restrict, sideBondOf, bondInvFun, dif_neg he, dif_pos hes,
        finCongr_apply_coe]
      exact congrArg (fun z : {e : a.G.edgeSet // e ≠ a.cutEdge h ∧ a.EdgeSide h e} =>
        ((bs z).val : ℕ)) hkey
  · apply Fin.ext
    simp only [finCongr_apply_coe]
    exact congrArg (fun z : {x : a.V // a.Side h x} => ((row z).val : ℕ))
      (show (⟨u, a.side_left h⟩ : {x : a.V // a.Side h x}) = ⟨vr.1, vr.2⟩
        from Subtype.ext hvu.symm)

/-- Unfolding the side restriction at `u` recovers the original `u`-tensor (the
fold/unfold round-trip on the `u`-slot). -/
theorem unfoldU_sideParam (h : a.G.Adj u w) (ψ : a.Param) :
    a.unfoldU h (a.sideParam h ψ) = ψ u := by
  classical
  funext bi₀ xv₀
  rw [unfoldU, sideParam, dif_pos (show (uSide h : (a.sideArch h).V).1 = u from rfl),
    finCongr_finCongr_symm, Equiv.symm_apply_apply]
  congr 1
  · funext e''
    by_cases he : (⟨e''.1, e''.2.1⟩ : a.G.edgeSet) = a.cutEdge h
    · rw [dif_pos he]
      have he'' : e'' = adjIncLeft h :=
        Subtype.ext (show e''.1 = s(u, w) from congrArg Subtype.val he)
      apply Fin.ext
      simp only [finCongr_apply_coe]
      exact congrArg (fun z : a.Inc u => ((bi₀ z).val : ℕ)) he''.symm
    · rw [dif_neg he]
      apply Fin.ext
      simp only [finCongr_apply_coe]
      exact congrArg (fun z : a.Inc u => ((bi₀ z).val : ℕ))
        (a.incSideToOrig_origIncToSide h e'' _)

/-- The ungauged pull-back's `u`-tensor is the unfolded `u`-tensor of `φ`. -/
theorem pullParam_one_apply_u (h : a.G.Adj u w) (θ : a.Param) (φ : (a.sideArch h).Param) :
    a.pullParam h θ 1 φ u = a.unfoldU h φ := by
  funext bi xv
  rw [pullParam, dif_pos rfl, Matrix.transpose_one, a.modeMul_one]
  exact rfl

/-- Restricting the ungauged pull-back to the side recovers `φ` (round-trip). -/
theorem sideParam_pullParam_one (h : a.G.Adj u w) (θ : a.Param) (φ : (a.sideArch h).Param) :
    a.sideParam h (a.pullParam h θ 1 φ) = φ := by
  classical
  funext vr
  obtain ⟨vv, hv⟩ := vr
  funext bi' xr'
  by_cases hvu : vv = u
  · subst hvu
    rw [sideParam,
      dif_pos (show ((⟨vv, hv⟩ : (a.sideArch h).V)).1 = vv from rfl),
      a.pullParam_one_apply_u h θ φ, unfoldU]
    refine congrArg₂ _ ?_ ?_
    · funext e'
      simp only [dif_neg (a.incSideToOrig_ne_cut h e')]
      apply Fin.ext
      simp only [finCongr_apply_coe]
      exact congrArg (fun z => ((bi' z).val : ℕ))
        (a.origIncToSide_incSideToOrig h e' _)
    · apply Fin.ext
      simp only [finCongr_apply_coe]
      have hxr : xr'.val = (finProdFinEquiv (finProdFinEquiv.symm
          (finCongr (a.sideArch_n_eq_u h ⟨vv, hv⟩
            (show ((⟨vv, hv⟩ : (a.sideArch h).V)).1 = vv from rfl)) xr'))).val := by
        rw [Equiv.apply_symm_apply]
        simp only [finCongr_apply_coe]
      rw [hxr]
      exact finProdFinEquiv_val_congr _ _ (by simp) (by simp)
  · rw [sideParam, dif_neg (show ¬((⟨vv, hv⟩ : (a.sideArch h).V)).1 = u from hvu),
      pullParam, dif_neg hvu, dif_pos (show a.Side h vv from hv)]
    refine congrArg₂ _ ?_ ?_
    · funext e'
      apply Fin.ext
      simp only [finCongr_apply_coe]
      exact congrArg (fun z => ((bi' z).val : ℕ))
        (a.origIncToSide_incSideToOrig h e' _)
    · apply Fin.ext
      simp only [finCongr_apply_coe]

/-! ### The strip package -/

/-- **The `Ffun` bridge**: the side architecture's represented tensor of the restricted
parameters reads off the left cut factor. -/
theorem represented_sideParam (h : a.G.Adj u w) (θ : a.Param)
    (row : a.Row h) (j : Fin (a.r s(u, w))) :
    (a.sideArch h).represented (a.sideParam h θ) (a.rowPack h row j)
      = a.Ffun h θ row j := by
  classical
  simp only [represented, Ffun]
  refine (Fintype.sum_equiv (a.sideBondEquiv h) _ _ (fun bs => ?_)).symm
  refine (Fintype.prod_equiv
    (Equiv.subtypeEquivRight (q := a.Side h) (fun x => Iff.rfl)) _ _ (fun vr => ?_)).symm
  by_cases hvu : vr.1 = u
  · exact a.sideParam_sideBondOf_u h θ row j bs vr hvu
  · exact a.sideParam_sideBondOf_ne h θ row j bs vr hvu

/-- Value of `rowPack` at a vertex over `u`. -/
theorem rowPack_apply_eq (h : a.G.Adj u w) (row : a.Row h) (j : Fin (a.r s(u, w)))
    (y : (a.sideArch h).V) (hy : y.1 = u) :
    a.rowPack h row j y = finCongr (a.sideArch_n_eq_u h y hy).symm
      (finProdFinEquiv (row ⟨u, a.side_left h⟩, j)) := dif_pos hy

/-- Value of `rowPack` at a vertex away from `u`. -/
theorem rowPack_apply_ne (h : a.G.Adj u w) (row : a.Row h) (j : Fin (a.r s(u, w)))
    (y : (a.sideArch h).V) (hy : y.1 ≠ u) :
    a.rowPack h row j y
      = finCongr (a.sideArch_n_eq_ne h y hy).symm (row ⟨y.1, y.2⟩) := dif_neg hy

/-- The fold and its extractions are mutually inverse. -/
theorem rowExtract_rowPack (h : a.G.Adj u w) (row : a.Row h) (j : Fin (a.r s(u, w))) :
    a.rowExtract h (a.rowPack h row j) = row := by
  funext y
  apply Fin.ext
  by_cases hyu : y.1 = u
  · simp only [rowExtract, dif_pos hyu, a.rowPack_apply_eq h row j ⟨y.1, y.2⟩ hyu,
      finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Equiv.symm_apply_apply, Fin.val_cast]
    exact congrArg (fun z : {x : a.V // a.Side h x} => (row z).val)
      (Subtype.ext hyu.symm : (⟨u, a.side_left h⟩ : {x : a.V // a.Side h x}) = y)
  · simp only [rowExtract, dif_neg hyu, a.rowPack_apply_ne h row j ⟨y.1, y.2⟩ hyu,
      finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Fin.val_cast]

theorem jExtractS_rowPack (h : a.G.Adj u w) (row : a.Row h) (j : Fin (a.r s(u, w))) :
    a.jExtractS h (a.rowPack h row j) = j := by
  simp only [jExtractS, a.rowPack_apply_eq h row j (uSide h) rfl]
  simp

/-- `rowPack` inverts the extraction pair. -/
theorem rowPack_extract (h : a.G.Adj u w) (xr : (a.sideArch h).Ext) :
    a.rowPack h (a.rowExtract h xr) (a.jExtractS h xr) = xr := by
  funext y
  by_cases hyu : y.1 = u
  · obtain rfl : y = uSide h := Subtype.ext hyu
    rw [a.rowPack_apply_eq h _ _ (uSide h) rfl]
    apply Fin.ext
    simp only [finCongr_apply, Fin.val_cast]
    have hfst : a.rowExtract h xr ⟨u, a.side_left h⟩
        = (finProdFinEquiv.symm
            (finCongr (a.sideArch_n_eq_u h (uSide h) rfl) (xr (uSide h)))).1 := by
      simp only [rowExtract, dif_pos rfl]
      rfl
    rw [hfst, show a.jExtractS h xr = (finProdFinEquiv.symm
        (finCongr (a.sideArch_n_eq_u h (uSide h) rfl) (xr (uSide h)))).2 from rfl,
      Prod.mk.eta, Equiv.apply_symm_apply]
    simp [finCongr_apply]
  · rw [a.rowPack_apply_ne h _ _ y hyu]
    have hre : a.rowExtract h xr ⟨y.1, y.2⟩
        = finCongr (a.sideArch_n_eq_ne h ⟨y.1, y.2⟩ hyu) (xr ⟨y.1, y.2⟩) := by
      simp only [rowExtract, dif_neg hyu]
    rw [hre]
    apply Fin.ext
    simp only [finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Fin.val_cast]
    rfl

/-! ### The pulled-back cut factors and the loss decomposition -/

/-- The side architecture's represented tensor of `φ`, reshaped by `rowPack` into a
`Row × r_e` matrix — the left cut factor produced by the (ungauged) pull-back. -/
noncomputable def sideFfun (h : a.G.Adj u w) (φ : (a.sideArch h).Param) :
    Matrix (a.Row h) (Fin (a.r s(u, w))) ℝ :=
  fun row j => (a.sideArch h).represented φ (a.rowPack h row j)

/-- The fold `rowPack` as an equivalence (inverse: the extraction pair). -/
noncomputable def rowPackEquiv (h : a.G.Adj u w) :
    a.Row h × Fin (a.r s(u, w)) ≃ (a.sideArch h).Ext where
  toFun p := a.rowPack h p.1 p.2
  invFun xr := (a.rowExtract h xr, a.jExtractS h xr)
  left_inv p := Prod.ext (a.rowExtract_rowPack h p.1 p.2) (a.jExtractS_rowPack h p.1 p.2)
  right_inv xr := a.rowPack_extract h xr

/-- The effective target reads off the matrix through the fold. -/
theorem sideTarget_rowPack (h : a.G.Adj u w)
    (B : Matrix (a.Row h) (Fin (a.r s(u, w))) ℝ) (row : a.Row h)
    (j : Fin (a.r s(u, w))) : a.sideTarget h B (a.rowPack h row j) = B row j := by
  simp only [sideTarget]
  rw [a.rowExtract_rowPack h row j, a.jExtractS_rowPack h row j]

/-- `Hfun` ignores the pulled-back side: the far factor of the pull is the far factor
of `θ`. -/
theorem Hfun_pullParam (h : a.G.Adj u w) (θ : a.Param)
    (M : Matrix (Fin (a.r s(u, w))) (Fin (a.r s(u, w))) ℝ) (φ : (a.sideArch h).Param) :
    a.Hfun h (a.pullParam h θ M φ) = a.Hfun h θ := by
  funext col k
  simp only [Hfun]
  refine Finset.sum_congr rfl (fun bc _ => Finset.prod_congr rfl (fun v _ => ?_))
  have hvu : v.1 ≠ u := fun hc => v.2 (by rw [hc]; exact a.side_left h)
  rw [pullParam, dif_neg hvu, dif_neg v.2]

/-- The gauged pull is the ungauged pull with `Mᵀ` hitting the `u`-slot. -/
theorem pullParam_eq_update (h : a.G.Adj u w) (θ : a.Param)
    (M : Matrix (Fin (a.r s(u, w))) (Fin (a.r s(u, w))) ℝ) (φ : (a.sideArch h).Param) :
    a.pullParam h θ M φ
      = Function.update (a.pullParam h θ 1 φ) u
          (a.modeMul u (adjIncLeft h) Mᵀ (a.pullParam h θ 1 φ u)) := by
  funext v bi xv
  by_cases hvu : v = u
  · subst hvu
    rw [Function.update_self, a.pullParam_one_apply_u h θ φ, pullParam, dif_pos rfl]
    exact rfl
  · rw [Function.update_of_ne hvu, pullParam, pullParam, dif_neg hvu, dif_neg hvu]

/-- The left cut factor of the pulled-back family: `F(pull θ M φ) = F_φ · M`. -/
theorem Ffun_pullParam (h : a.G.Adj u w) (θ : a.Param)
    (M : Matrix (Fin (a.r s(u, w))) (Fin (a.r s(u, w))) ℝ) (φ : (a.sideArch h).Param) :
    a.Ffun h (a.pullParam h θ M φ) = a.sideFfun h φ * M := by
  have hbase : a.Ffun h (a.pullParam h θ 1 φ) = a.sideFfun h φ := by
    funext row j
    exact (a.represented_sideParam h (a.pullParam h θ 1 φ) row j).symm.trans
      (congrArg (fun p => (a.sideArch h).represented p (a.rowPack h row j))
        (a.sideParam_pullParam_one h θ φ))
  rw [a.pullParam_eq_update h θ M φ,
    a.Ffun_update_modeMul h (a.pullParam h θ 1 φ) Mᵀ, Matrix.transpose_transpose, hbase]

/-- Matricization of the pulled-back family: `T(pull θ M φ)⁽ᵉ⁾ = F_φ · M · H_θᵀ`. Note the
gauge enters as `M`, NOT `Mᵀ`: the effective right factor is `H_θ · Mᵀ`. -/
theorem matricize_pullParam (h : a.G.Adj u w) (θ : a.Param)
    (M : Matrix (Fin (a.r s(u, w))) (Fin (a.r s(u, w))) ℝ) (φ : (a.sideArch h).Param) :
    a.matricize h (a.pullParam h θ M φ)
      = a.sideFfun h φ * M * (a.Hfun h θ)ᵀ := by
  rw [a.matricize_FH h, a.Hfun_pullParam h θ M φ, a.Ffun_pullParam h θ M φ]

/-- **Orthonormal-column loss decomposition** (pure matrix algebra): if `Hᵀ H = 1`, then
`‖F Hᵀ − T‖² = ‖F − T H‖² + (‖T‖² − ‖T H‖²)` in squared Frobenius norms. -/
theorem loss_orth_decomp {R C : Type*} [Fintype R] [Fintype C] {r : ℕ}
    (F : Matrix R (Fin r) ℝ) (T : Matrix R C ℝ) (H : Matrix C (Fin r) ℝ)
    (horth : Hᵀ * H = 1) :
    (∑ row, ∑ col, ((F * Hᵀ) row col - T row col) ^ 2)
      = (∑ row, ∑ j, (F row j - (T * H) row j) ^ 2)
        + ((∑ row, ∑ col, (T row col) ^ 2) - ∑ row, ∑ j, ((T * H) row j) ^ 2) := by
  classical
  have hFF : (F * Hᵀ) * (F * Hᵀ)ᵀ = F * Fᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Hᵀ H Fᵀ, horth, Matrix.one_mul]
  have hcross : (F * Hᵀ) * Tᵀ = F * (T * H)ᵀ := by
    rw [Matrix.transpose_mul, ← Matrix.mul_assoc]
  have hentryFF : ∀ row : R, (∑ j, (F row j) ^ 2) = ∑ col, ((F * Hᵀ) row col) ^ 2 := by
    intro row
    have h1 := Matrix.ext_iff.mpr hFF row row
    rw [Matrix.mul_apply, Matrix.mul_apply] at h1
    simp only [Matrix.transpose_apply] at h1
    calc (∑ j, (F row j) ^ 2) = ∑ j, F row j * F row j :=
          Finset.sum_congr rfl fun j _ => pow_two (F row j)
      _ = ∑ col, (F * Hᵀ) row col * (F * Hᵀ) row col := h1.symm
      _ = ∑ col, ((F * Hᵀ) row col) ^ 2 :=
          Finset.sum_congr rfl fun col _ => (pow_two _).symm
  have hentryCross : ∀ row : R,
      (∑ col, (F * Hᵀ) row col * T row col) = ∑ j, F row j * (T * H) row j := by
    intro row
    have h1 := Matrix.ext_iff.mpr hcross row row
    rw [Matrix.mul_apply, Matrix.mul_apply] at h1
    simp only [Matrix.transpose_apply] at h1
    exact h1
  have hrow : ∀ row : R,
      (∑ col, ((F * Hᵀ) row col - T row col) ^ 2)
        = (∑ j, (F row j - (T * H) row j) ^ 2)
          + ((∑ col, (T row col) ^ 2) - ∑ j, ((T * H) row j) ^ 2) := by
    intro row
    have e1 : (∑ col, ((F * Hᵀ) row col - T row col) ^ 2)
        = ((∑ col, ((F * Hᵀ) row col) ^ 2)
            - 2 * (∑ col, (F * Hᵀ) row col * T row col)) + ∑ col, (T row col) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun col _ => by ring
    have e2 : (∑ j, (F row j - (T * H) row j) ^ 2)
        = ((∑ j, (F row j) ^ 2)
            - 2 * (∑ j, F row j * (T * H) row j)) + ∑ j, ((T * H) row j) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, e2, hentryFF row, hentryCross row]
    ring
  rw [Finset.sum_congr rfl fun row _ => hrow row, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

/-- **Loss decomposition, family form.** `pullParam` applies `Mᵀ` on the
cut-bond slot, so the family map is taken at `Mᵀ`: if `H₀ := Hfun h θ * M` has orthonormal
columns, then for EVERY side parameter `φ`,
`L(pullParam θ Mᵀ φ) = L_side(φ against T*⁽ᵉ⁾H₀) + ½(‖T*‖² − ‖T*⁽ᵉ⁾H₀‖²)`.
(An earlier draft paired `pullParam … M` with `H₀ = Hfun · M`; that orientation is false —
2-node counterexample with M = [[1,1],[0,1]], H = [[1,-1],[0,1]]ᵀ… — this is the corrected
statement.) -/
theorem loss_pullParam (h : a.G.Adj u w) (Tstar : a.Ext → ℝ) (θ : a.Param)
    (M : Matrix (Fin (a.r s(u, w))) (Fin (a.r s(u, w))) ℝ)
    (horth : (a.Hfun h θ * M)ᵀ * (a.Hfun h θ * M) = 1) (φ : (a.sideArch h).Param) :
    a.loss Tstar (a.pullParam h θ Mᵀ φ)
      = (a.sideArch h).loss (a.sideTarget h (a.matricizeOf h Tstar * (a.Hfun h θ * M))) φ
        + (1 / 2) * ((∑ x, (Tstar x) ^ 2)
          - ∑ p, ∑ q, ((a.matricizeOf h Tstar * (a.Hfun h θ * M)) p q) ^ 2) := by
  classical
  -- (1) the pulled point matricizes against the orthonormal factor `H₀ = H_θ · M`
  have hmat : a.matricize h (a.pullParam h θ Mᵀ φ)
      = a.sideFfun h φ * (a.Hfun h θ * M)ᵀ := by
    rw [a.matricize_pullParam h θ Mᵀ φ, Matrix.transpose_mul, ← Matrix.mul_assoc]
  -- (2) reshape the loss across the cut
  have hL : a.loss Tstar (a.pullParam h θ Mᵀ φ)
      = (1 / 2) * ∑ row, ∑ col,
          ((a.sideFfun h φ * (a.Hfun h θ * M)ᵀ) row col
            - a.matricizeOf h Tstar row col) ^ 2 := by
    rw [loss]
    congr 1
    rw [← (a.extSplit h).symm.sum_comp
        (fun x => (a.represented (a.pullParam h θ Mᵀ φ) x - Tstar x) ^ 2),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun row _ => Finset.sum_congr rfl (fun col _ => ?_))
    rw [← hmat]
    rfl
  -- (3) reshape the side loss along the fold
  have hR : (a.sideArch h).loss
        (a.sideTarget h (a.matricizeOf h Tstar * (a.Hfun h θ * M))) φ
      = (1 / 2) * ∑ row, ∑ j,
          (a.sideFfun h φ row j
            - (a.matricizeOf h Tstar * (a.Hfun h θ * M)) row j) ^ 2 := by
    rw [loss]
    congr 1
    rw [← Equiv.sum_comp (a.rowPackEquiv h)
        (fun xr => ((a.sideArch h).represented φ xr
          - a.sideTarget h (a.matricizeOf h Tstar * (a.Hfun h θ * M)) xr) ^ 2),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun row _ => Finset.sum_congr rfl (fun j _ => ?_))
    simp only [rowPackEquiv, Equiv.coe_fn_mk]
    rw [a.sideTarget_rowPack h (a.matricizeOf h Tstar * (a.Hfun h θ * M)) row j]
    rfl
  -- (4) reshape the target norm and assemble
  have hTsq : (∑ x, (Tstar x) ^ 2)
      = ∑ row, ∑ col, (a.matricizeOf h Tstar row col) ^ 2 := by
    rw [← (a.extSplit h).symm.sum_comp (fun x => (Tstar x) ^ 2), Fintype.sum_prod_type]
    rfl
  rw [hL, hR, hTsq,
    loss_orth_decomp (a.sideFfun h φ) (a.matricizeOf h Tstar) (a.Hfun h θ * M) horth]
  ring

/-- The base point lies on the strip family: pulling back the (inverse-gauged) side
restriction of `θ` recovers `θ`, provided `M` is invertible. -/
theorem pullParam_sideParam (h : a.G.Adj u w) (θ : a.Param)
    {M : Matrix (Fin (a.r s(u, w))) (Fin (a.r s(u, w))) ℝ} (hM : IsUnit M.det) :
    a.pullParam h θ M
        (a.sideParam h (Function.update θ u (a.modeMul u (adjIncLeft h) M⁻¹ᵀ (θ u))))
      = θ := by
  classical
  funext v bi xv
  rw [pullParam]
  by_cases hvu : v = u
  · subst hvu
    rw [dif_pos rfl,
      a.unfoldU_sideParam h (Function.update θ v (a.modeMul v (adjIncLeft h) M⁻¹ᵀ (θ v))),
      Function.update_self, a.modeMul_modeMul, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul _ hM, Matrix.transpose_one, a.modeMul_one]
    exact rfl
  · rw [dif_neg hvu]
    by_cases hv : a.Side h v
    · rw [dif_pos hv, sideParam,
        dif_neg (show ((⟨v, hv⟩ : (a.sideArch h).V)).1 ≠ u from hvu),
        show Function.update θ u (a.modeMul u (adjIncLeft h) M⁻¹ᵀ (θ u))
            ((⟨v, hv⟩ : (a.sideArch h).V)).1 = θ v from Function.update_of_ne hvu _ _]
      refine congrArg₂ _ ?_ ?_
      · funext e''
        apply Fin.ext
        simp only [finCongr_apply_coe]
        exact congrArg (fun z : a.Inc v => ((bi z).val : ℕ))
          (a.incSideToOrig_origIncToSide h e'' _)
      · apply Fin.ext
        simp only [finCongr_apply_coe]
    · rw [dif_neg hv]

/-- The strip family map is continuous in the side parameter. -/
theorem continuous_pullParam (h : a.G.Adj u w) (θ : a.Param)
    (M : Matrix (Fin (a.r s(u, w))) (Fin (a.r s(u, w))) ℝ) :
    Continuous (a.pullParam h θ M) := by
  apply continuous_pi
  intro v
  show Continuous fun φ : (a.sideArch h).Param => a.pullParam h θ M φ v
  apply continuous_pi
  intro bi
  apply continuous_pi
  intro xv
  show Continuous fun φ : (a.sideArch h).Param => a.pullParam h θ M φ v bi xv
  simp only [pullParam]
  by_cases hvu : v = u
  · simp only [dif_pos hvu]
    show Continuous fun φ : (a.sideArch h).Param =>
      ∑ k, Mᵀ ((hvu ▸ bi) (adjIncLeft h)) k
        * a.unfoldU h φ (Function.update (hvu ▸ bi) (adjIncLeft h) k)
            (finCongr (congrArg a.n hvu) xv)
    apply continuous_finset_sum
    intro k _
    refine continuous_const.mul ?_
    show Continuous fun φ : (a.sideArch h).Param =>
      φ (uSide h)
        (fun e' => Function.update (hvu ▸ bi) (adjIncLeft h) k (a.incSideToOrig h e'))
        (finCongr (a.sideArch_n_eq_u h (uSide h) rfl).symm
          (finProdFinEquiv (finCongr (congrArg a.n hvu) xv,
            Function.update (hvu ▸ bi) (adjIncLeft h) k (adjIncLeft h))))
    exact (continuous_apply _).comp ((continuous_apply _).comp (continuous_apply (uSide h)))
  · simp only [dif_neg hvu]
    by_cases hv : a.Side h v
    · simp only [dif_pos hv]
      exact (continuous_apply _).comp ((continuous_apply _).comp (continuous_apply _))
    · simp only [dif_neg hv]
      exact continuous_const

end Arch

end TTN
