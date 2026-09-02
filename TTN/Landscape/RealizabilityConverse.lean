import TTN.Landscape.Realizability
import TTN.RankFactor

/-!
# Realizability converse via leaf removal

The **converse** of the edge-rank characterization (edge-rank bound implies realizable) and the full iff, by
strong induction on `|V|` via **leaf removal** (not the paper's root-nestedness): peel a leaf
`v` (neighbour `u`, edge `e`); the leaf cut factors `T*^(e) = A Bᵀ` minimally (`Matrix.exists_factor_of_rank_le`);
`A` becomes the leaf node tensor and `B` the target of a **reduced** TTN where `u` absorbs the
bond `e` as an external mode of dimension `r_e`; then apply the inductive hypothesis. The
full-Tucker-rank proof reuses the same reduction.
-/

open scoped Matrix
namespace TTN

namespace Arch

variable (a : Arch)

/-- The **edge-rank bound** in the realizability characterization. -/
def RankBound (Tstar : a.Ext → ℝ) : Prop :=
  ∀ (u w : a.V) (h : a.G.Adj u w), (a.matricizeOf h Tstar).rank ≤ a.r s(u, w)

/-- `v` is a **leaf with neighbour `u`**: `v`'s only graph-neighbour is `u`. -/
def IsLeafWith (v u : a.V) : Prop := a.G.Adj v u ∧ ∀ y, a.G.Adj v y → y = u

/-- **The leaf cut isolates `v`.** Deleting the leaf's only edge `s(v,u)` leaves `v`
with no incident edges, so the `Side` of that cut (the component of `v`) is `{v}`. -/
theorem side_leaf {v u : a.V} (hl : a.IsLeafWith v u) (x : a.V) :
    a.Side hl.1 x ↔ x = v := by
  constructor
  · rintro ⟨p⟩
    cases p with
    | nil => rfl
    | cons hadj _ =>
      rw [SimpleGraph.deleteEdges_adj] at hadj
      obtain ⟨hvw, hne⟩ := hadj
      exact absurd (by rw [hl.2 _ hvw]; rfl) hne
  · rintro rfl
    exact SimpleGraph.Reachable.refl _

/-- The **reduced architecture** obtained by deleting a leaf `v` (neighbour `u`): nodes
are `V \ {v}`, the graph is `G` restricted, bond dims are inherited, and `u` absorbs the
bond `e = s(v,u)` as an external mode — its external dimension is bumped to `nᵤ · rₑ`.
(Mirrors Thm 5.2's reduction: "`u`'s former bond mode along `e` becomes an external mode
of dimension `rₑ`".) -/
noncomputable def reducedArch {v u : a.V} (hl : a.IsLeafWith v u) : Arch where
  V := ↥({v}ᶜ : Set a.V)
  G := a.G.induce {v}ᶜ
  hT := by
    have hdeg : a.G.degree v = 1 :=
      SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr ⟨u, hl.1, hl.2⟩
    rw [SimpleGraph.isTree_iff]
    exact ⟨a.hT.connected.induce_compl_singleton_of_degree_eq_one hdeg,
      a.hT.isAcyclic.induce _⟩
  r := fun e => a.r (e.map Subtype.val)
  n := fun x => if x.1 = u then a.n u * a.r s(v, u) else a.n x.1
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
      exact Nat.mul_pos (a.hn u) (a.hr s(v, u) (by rw [SimpleGraph.mem_edgeSet]; exact hl.1))
    · simp only [hx, if_neg, not_false_iff]
      exact a.hn x.1

/-! ### Reduced architecture: vertex/dimension reduction lemmas

Helpers for reading off `reducedArch`'s external dimensions. `u`'s external mode is bumped
to `n_u · r_e`; every other node keeps its original dimension. -/

/-- The leaf's neighbour is distinct from the leaf. -/
theorem reduced_uNeV {v u : a.V} (hl : a.IsLeafWith v u) : u ≠ v := hl.1.ne.symm

/-- `u` viewed as a vertex of the reduced architecture. -/
def reducedU {v u : a.V} (hl : a.IsLeafWith v u) : (a.reducedArch hl).V :=
  ⟨u, by rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact a.reduced_uNeV hl⟩

/-- At the absorbing node `u`, the reduced external dimension is the bumped `n_u · r_e`. -/
theorem reducedArch_n_eq_u {v u : a.V} (hl : a.IsLeafWith v u)
    (y : (a.reducedArch hl).V) (hy : y.1 = u) :
    (a.reducedArch hl).n y = a.n u * a.r s(v, u) := by
  show (if y.1 = u then a.n u * a.r s(v, u) else a.n y.1) = _
  rw [if_pos hy]

/-- Away from the absorbing node, the reduced external dimension is unchanged. -/
theorem reducedArch_n_eq_ne {v u : a.V} (hl : a.IsLeafWith v u)
    (y : (a.reducedArch hl).V) (hy : y.1 ≠ u) :
    (a.reducedArch hl).n y = a.n y.1 := by
  show (if y.1 = u then a.n u * a.r s(v, u) else a.n y.1) = _
  rw [if_neg hy]

/-- **Ext correspondence.** Lift an original external index `x` together with a bond value
`j ∈ Fin r_e` to a reduced external index: the leaf `v` is dropped, the absorbing node `u`
packs `(x_u, j)` into its bumped mode (via `finProdFinEquiv`), and every other node passes
through unchanged. -/
noncomputable def pack {v u : a.V} (hl : a.IsLeafWith v u) (x : a.Ext)
    (j : Fin (a.r s(v, u))) : (a.reducedArch hl).Ext :=
  fun y => if hy : y.1 = u then
    finCongr (a.reducedArch_n_eq_u hl y hy).symm (finProdFinEquiv (x u, j))
  else
    finCongr (a.reducedArch_n_eq_ne hl y hy).symm (x y.1)

/-- A `Col` node `y` (off the leaf cut) is distinct from the leaf `v`, hence a reduced vertex. -/
def colToReduced {v u : a.V} (hl : a.IsLeafWith v u)
    (y : {x : a.V // ¬ a.Side hl.1 x}) : (a.reducedArch hl).V :=
  ⟨y.1, by
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact fun h => y.2 ((a.side_leaf hl y.1).mpr h)⟩

/-- Extract the bond value `j` packed into the absorbing node `u` of a reduced external index. -/
noncomputable def jExtract {v u : a.V} (hl : a.IsLeafWith v u)
    (xr : (a.reducedArch hl).Ext) : Fin (a.r s(v, u)) :=
  (finProdFinEquiv.symm
    (finCongr (a.reducedArch_n_eq_u hl (a.reducedU hl) rfl) (xr (a.reducedU hl)))).2

/-- Extract the `Col`-indexed external data (`u` un-bumped) from a reduced external index. -/
noncomputable def colExtract {v u : a.V} (hl : a.IsLeafWith v u)
    (xr : (a.reducedArch hl).Ext) : a.Col hl.1 :=
  fun y => if hyu : y.1 = u then
    finCongr (show a.n u = a.n y.1 by rw [hyu])
      (finProdFinEquiv.symm
        (finCongr (a.reducedArch_n_eq_u hl (a.colToReduced hl y) hyu) (xr (a.colToReduced hl y)))).1
  else
    finCongr (a.reducedArch_n_eq_ne hl (a.colToReduced hl y) hyu) (xr (a.colToReduced hl y))

/-- **The reduced target** `T̃*` read off the right cut-factor `B`: a reduced external index is
split into its `Col` data and the bond value at `u`, and fed to `B`. (Designed so that
`Tred B (pack x j) = B ((extSplit x).2) j`, the bridge to the factorization `T*^(e) = A Bᵀ`.) -/
noncomputable def Tred {v u : a.V} (hl : a.IsLeafWith v u)
    (B : Matrix (a.Col hl.1) (Fin (a.r s(v, u))) ℝ) (xr : (a.reducedArch hl).Ext) : ℝ :=
  B (a.colExtract hl xr) (a.jExtract hl xr)

/-- An edge of the reduced graph maps (under `Subtype.val`) to an edge of the original graph. -/
theorem reduced_edge_mem {v u : a.V} (hl : a.IsLeafWith v u)
    {e : Sym2 (a.reducedArch hl).V} (he : e ∈ (a.reducedArch hl).G.edgeSet) :
    Sym2.map Subtype.val e ∈ a.G.edgeSet := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.mem_edgeSet] at he
    exact (SimpleGraph.mem_edgeSet a.G).mpr he

/-- An incidence in the reduced architecture maps to an incidence in the original (same node,
edge pushed forward by `Subtype.val`). Note `reducedArch.r e' = a.r (e'.map val)` *definitionally*,
so reduced bond indices transport along this with no cast. -/
def incReducedToOrig {v u : a.V} (hl : a.IsLeafWith v u) {wr : (a.reducedArch hl).V}
    (e' : (a.reducedArch hl).Inc wr) : a.Inc wr.1 :=
  ⟨Sym2.map Subtype.val e'.1, a.reduced_edge_mem hl e'.2.1, Sym2.mem_map.mpr ⟨wr, e'.2.2, rfl⟩⟩

/-- **Assemble `θ` from the leaf tensor and the reduced parameters.** `v` gets the leaf tensor
`Wᵥ` (its only incident edge is `e`, so its bond index is just `Fin r_e`); the absorbing node
`u` gets `θ̃ᵤ` with the bond value on `e` folded into its bumped external mode; every other node
passes through `θ̃` (bond indices relabelled via `incReducedToOrig`). -/
noncomputable def liftParam {v u : a.V} (hl : a.IsLeafWith v u)
    (Wv : Fin (a.r s(v, u)) → Fin (a.n v) → ℝ) (θr : (a.reducedArch hl).Param) : a.Param :=
  fun w bi xw =>
    if hwv : w = v then
      Wv (bi ⟨s(v, u), by rw [SimpleGraph.mem_edgeSet]; exact hl.1, by rw [hwv]; exact Sym2.mem_mk_left v u⟩)
         (finCongr (congrArg a.n hwv) xw)
    else if hwu : w = u then
      θr (a.reducedU hl) (fun e' => (hwu ▸ bi) (a.incReducedToOrig hl e'))
         (finCongr (a.reducedArch_n_eq_u hl (a.reducedU hl) rfl).symm
            (finProdFinEquiv (finCongr (congrArg a.n hwu) xw,
              bi ⟨s(v, u), by rw [SimpleGraph.mem_edgeSet]; exact hl.1,
                by rw [hwu]; exact Sym2.mem_mk_right v u⟩)))
    else
      θr ⟨w, by rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hwv⟩
         (fun e' => bi (a.incReducedToOrig hl e'))
         (finCongr (a.reducedArch_n_eq_ne hl ⟨w, by
            rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hwv⟩ hwu).symm xw)

/-- The leaf's external index `Fin (n v)` viewed as a `Row hl.1` (every `Row` node is `v`). -/
noncomputable def rowOf {v u : a.V} (hl : a.IsLeafWith v u) (xv : Fin (a.n v)) : a.Row hl.1 :=
  fun y => finCongr (congrArg a.n ((a.side_leaf hl y.1).mp y.2)).symm xv

/-! ### Round-trip lemmas: `pack` is a section of the extraction maps -/

/-- Value of `pack` at the absorbing node `u`. -/
theorem pack_reducedU {v u : a.V} (hl : a.IsLeafWith v u) (x : a.Ext) (j : Fin (a.r s(v, u))) :
    a.pack hl x j (a.reducedU hl)
      = finCongr (a.reducedArch_n_eq_u hl (a.reducedU hl) rfl).symm (finProdFinEquiv (x u, j)) :=
  dif_pos rfl

/-- `jExtract` recovers the bond value that `pack` folded into `u`. -/
theorem jExtract_pack {v u : a.V} (hl : a.IsLeafWith v u) (x : a.Ext)
    (j : Fin (a.r s(v, u))) : a.jExtract hl (a.pack hl x j) = j := by
  simp only [jExtract, a.pack_reducedU hl x j]
  simp

/-- `rowOf` of the leaf coordinate is the `Row` part of the external split. -/
theorem rowOf_eq {v u : a.V} (hl : a.IsLeafWith v u) (x : a.Ext) :
    a.rowOf hl (x v) = (a.extSplit hl.1 x).1 := by
  funext y
  have hy1 : y.1 = v := (a.side_leaf hl y.1).mp y.2
  apply Fin.ext
  simp only [rowOf, finCongr_apply, Fin.val_cast]
  exact (congrArg (fun w => (x w).val) hy1).symm

/-- Value of `pack` at a `Col` node that coincides with `u`. -/
theorem pack_colToReduced_eq {v u : a.V} (hl : a.IsLeafWith v u) (x : a.Ext)
    (j : Fin (a.r s(v, u))) (y : {x : a.V // ¬ a.Side hl.1 x}) (hyu : y.1 = u) :
    a.pack hl x j (a.colToReduced hl y)
      = finCongr (a.reducedArch_n_eq_u hl (a.colToReduced hl y) hyu).symm
          (finProdFinEquiv (x u, j)) :=
  dif_pos hyu

/-- Value of `pack` at a `Col` node distinct from `u`. -/
theorem pack_colToReduced_ne {v u : a.V} (hl : a.IsLeafWith v u) (x : a.Ext)
    (j : Fin (a.r s(v, u))) (y : {x : a.V // ¬ a.Side hl.1 x}) (hyu : ¬ y.1 = u) :
    a.pack hl x j (a.colToReduced hl y)
      = finCongr (a.reducedArch_n_eq_ne hl (a.colToReduced hl y) hyu).symm (x y.1) :=
  dif_neg hyu

/-- `colExtract` recovers the `Col` part of the external split from `pack`. -/
theorem colExtract_pack {v u : a.V} (hl : a.IsLeafWith v u) (x : a.Ext)
    (j : Fin (a.r s(v, u))) : a.colExtract hl (a.pack hl x j) = (a.extSplit hl.1 x).2 := by
  funext y
  apply Fin.ext
  by_cases hyu : y.1 = u
  · simp only [colExtract, dif_pos hyu, a.pack_colToReduced_eq hl x j y hyu, finCongr_apply,
      Fin.cast_cast, Fin.cast_eq_self, Equiv.symm_apply_apply, Fin.val_cast]
    exact (congrArg (fun w => (x w).val) hyu).symm
  · simp only [colExtract, dif_neg hyu, a.pack_colToReduced_ne hl x j y hyu,
      finCongr_apply, Fin.val_cast]
    rfl

/-- **Factorization → target.** A leaf-cut factorization `T*^(e) = A Bᵀ` reads `T*` off as a
sum over the cut bond of the two factors, evaluated at the external split of `x`. -/
theorem target_eq_sum {v u : a.V} (hl : a.IsLeafWith v u) (Tstar : a.Ext → ℝ)
    (A : Matrix (a.Row hl.1) (Fin (a.r s(v, u))) ℝ) (B : Matrix (a.Col hl.1) (Fin (a.r s(v, u))) ℝ)
    (hAB : a.matricizeOf hl.1 Tstar = A * Bᵀ) (x : a.Ext) :
    Tstar x = ∑ j, A (a.extSplit hl.1 x).1 j * B (a.extSplit hl.1 x).2 j := by
  have hx : Tstar x
      = a.matricizeOf hl.1 Tstar (a.extSplit hl.1 x).1 (a.extSplit hl.1 x).2 := by
    show Tstar x = Tstar ((a.extSplit hl.1).symm ((a.extSplit hl.1 x).1, (a.extSplit hl.1 x).2))
    rw [Prod.mk.eta, Equiv.symm_apply_apply]
  rw [hx, hAB, Matrix.mul_apply]
  simp only [Matrix.transpose_apply]

/-! ### The two heavyweight lemmas

`represented_liftParam` is the bond-sum reindex engine (cf. `cut_factorization`);
`reduced_rankBound` is the rank-monotonicity transfer to the smaller tree. -/

/-- **Leaf-split identity (engine).** Contracting the lifted parameters factors as the leaf
tensor against the reduced represented tensor, summed over the leaf bond. Proved by reindexing
the global bond sum `a.Bond ≃ Fin r_e × reducedArch.Bond` and splitting the node product at `v`. -/
theorem represented_liftParam {v u : a.V} (hl : a.IsLeafWith v u)
    (Wv : Fin (a.r s(v, u)) → Fin (a.n v) → ℝ) (θr : (a.reducedArch hl).Param) (x : a.Ext) :
    a.represented (a.liftParam hl Wv θr) x
      = ∑ j, Wv j (x v) * (a.reducedArch hl).represented θr (a.pack hl x j) := by
  classical
  -- An edge incident to the leaf `v` is the leaf edge `e₀ = s(v,u)`.
  have hv_edge : ∀ (e : a.G.edgeSet), v ∈ e.1 → e = a.cutEdge hl.1 := by
    intro e he
    have hspec : s(v, Sym2.Mem.other' he) = e.1 := Sym2.other_spec' he
    have hadj : a.G.Adj v (Sym2.Mem.other' he) := by
      rw [← SimpleGraph.mem_edgeSet, hspec]; exact e.2
    have hyu : Sym2.Mem.other' he = u := hl.2 _ hadj
    apply Subtype.ext
    rw [← hspec, hyu]
  -- Hence any non-leaf edge avoids `v`, so its endpoints are reduced vertices.
  have vNotMem : ∀ (e : a.G.edgeSet), e ≠ a.cutEdge hl.1 →
      ∀ y ∈ e.1, y ∈ ({v}ᶜ : Set a.V) := by
    intro e hne y hy
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hyv
    exact hne (hv_edge e (hyv ▸ hy))
  -- Such an edge, lifted to the reduced vertices, lies in the reduced edge set.
  have edgeMem : ∀ (s : Sym2 a.V), s ∈ a.G.edgeSet →
      ∀ (hp : ∀ y ∈ s, y ∈ ({v}ᶜ : Set a.V)),
      Sym2.attachWith s hp ∈ (a.reducedArch hl).G.edgeSet := by
    intro s
    induction s using Sym2.ind with
    | _ p q =>
      intro hs hp
      rw [SimpleGraph.mem_edgeSet] at hs
      exact (SimpleGraph.mem_edgeSet _).mpr hs
  -- `attach` after pushing forward by `val` is the identity on reduced edges.
  have mapAttach : ∀ (t : Sym2 (a.reducedArch hl).V)
      (hp : ∀ y ∈ Sym2.map Subtype.val t, y ∈ ({v}ᶜ : Set a.V)),
      Sym2.attachWith (Sym2.map Subtype.val t) hp = t := by
    intro t
    induction t using Sym2.ind with
    | _ p q => intro hp; rfl
  -- Transporting a bond value along an edge equality.
  have castB : ∀ (F : a.Bond) {s t : Sym2 a.V} (hs : s ∈ a.G.edgeSet)
      (ht : t ∈ a.G.edgeSet) (hst : s = t),
      finCongr (congrArg a.r hst) (F ⟨s, hs⟩) = F ⟨t, ht⟩ := by
    intro F s t hs ht hst
    subst hst; rfl
  -- The red-side transport.
  have castBr : ∀ (F : (a.reducedArch hl).Bond) {s t : Sym2 (a.reducedArch hl).V}
      (hs : s ∈ (a.reducedArch hl).G.edgeSet) (ht : t ∈ (a.reducedArch hl).G.edgeSet) (hst : s = t),
      finCongr (congrArg (a.reducedArch hl).r hst) (F ⟨s, hs⟩) = F ⟨t, ht⟩ := by
    intro F s t hs ht hst
    subst hst; rfl
  -- A lifted reduced edge is never the leaf edge.
  have h_liftE_ne : ∀ (e' : (a.reducedArch hl).G.edgeSet),
      (⟨Sym2.map Subtype.val e'.1, a.reduced_edge_mem hl e'.2⟩ : a.G.edgeSet) ≠ a.cutEdge hl.1 := by
    intro e' hcon
    have hmap : Sym2.map Subtype.val e'.1 = s(v, u) := congrArg Subtype.val hcon
    have hv : v ∈ Sym2.map Subtype.val e'.1 := by rw [hmap]; exact Sym2.mem_mk_left v u
    rw [Sym2.mem_map] at hv
    obtain ⟨y, hy, hyv⟩ := hv
    exact y.2 (Set.mem_singleton_iff.mpr hyv)
  -- Rewrite the RHS as a single sum over `Fin r_e × reduced bonds`.
  simp only [represented, Finset.mul_sum]
  rw [← Fintype.sum_prod_type (fun p : Fin (a.r s(v,u)) × (a.reducedArch hl).Bond =>
        Wv p.1 (x v) * ∏ w', θr w' (Bond.restrict p.2 w') (a.pack hl x p.1 w'))]
  -- Reindex the global bond sum across the leaf edge.
  refine Finset.sum_bij'
    (fun (b : a.Bond) _ => (b (a.cutEdge hl.1),
        fun e' => b ⟨Sym2.map Subtype.val e'.1, a.reduced_edge_mem hl e'.2⟩))
    (fun (p : Fin (a.r s(v,u)) × (a.reducedArch hl).Bond) _ => fun e =>
        if he : e = a.cutEdge hl.1 then he.symm ▸ p.1
        else finCongr (congrArg a.r (Sym2.attachWith_map_subtypeVal (vNotMem e he)))
               (p.2 ⟨Sym2.attachWith e.1 (vNotMem e he), edgeMem e.1 e.2 (vNotMem e he)⟩))
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · -- left inverse
    intro b _
    funext e
    dsimp only
    by_cases he : e = a.cutEdge hl.1
    · subst he; rw [dif_pos rfl]
    · rw [dif_neg he]
      exact castB b _ e.2 (Sym2.attachWith_map_subtypeVal (vNotMem e he))
  · -- right inverse
    intro p _
    apply Prod.ext
    · dsimp only
      rw [dif_pos rfl]
    · funext e'
      dsimp only
      rw [dif_neg (h_liftE_ne e')]
      exact castBr p.2 _ e'.2 (mapAttach e'.1 (vNotMem _ (h_liftE_ne e')))
  · -- summand equality
    intro b _
    dsimp only
    rw [Fintype.prod_eq_mul_prod_compl v
          (fun w => a.liftParam hl Wv θr w (Bond.restrict b w) (x w))]
    congr 1
    · -- the leaf factor `v` contributes `Wᵥ` against the leaf bond value
      simp only [liftParam]
      rw [dif_pos trivial]
      rfl
    · -- the remaining nodes reassemble the reduced represented tensor
      rw [Finset.prod_subtype (p := fun y => y ∈ ({v}ᶜ : Set a.V)) ({v}ᶜ : Finset a.V)
            (fun y => by simp) (fun w => a.liftParam hl Wv θr w (Bond.restrict b w) (x w))]
      refine Finset.prod_congr rfl ?_
      rintro ⟨w, hw⟩ _
      have hwv : w ≠ v := fun h => (Set.mem_compl_iff _ _).mp hw (Set.mem_singleton_iff.mpr h)
      by_cases hwu : w = u
      · -- absorbing node `u`: the leaf bond folds into `u`'s bumped external mode
        subst hwu
        rw [liftParam]
        simp only [dif_neg hwv]
        rw [dif_pos trivial]
        simp only [pack]
        rw [dif_pos trivial]
        rfl
      · -- any other node passes through unchanged
        rw [liftParam]
        simp only [dif_neg hwv, dif_neg hwu]
        rw [pack]
        simp only [dif_neg hwu]
        rfl

/-- **Reduced rank bound (monotonicity).** If the target satisfies the edge-rank bound and its
leaf cut factors *minimally* as `T*^(e) = A Bᵀ` — with `hBz` (`B`'s columns beyond `rank` vanish)
and `hAli` (`A`'s used columns linearly independent), both supplied by `Matrix.exists_factor_of_rank_le`
(the latter through the eliminator `Matrix.eq_zero_of_sum_smul_col_eq_zero`)
— then the reduced target `Tred B` again satisfies the edge-rank bound: each reduced matricization
has rank at most the corresponding original one. Minimality is essential: for an arbitrary
factorization the leaf-contraction `Φ_A` can raise the reduced-edge rank above `r_{e'}`, whereas
under `hBz`/`hAli` it is injective on `B`'s support, so `rank(Tred^(e')) = rank(T*^(e')) ≤ r_{e'}`. -/
theorem reduced_rankBound {v u : a.V} (hl : a.IsLeafWith v u) {Tstar : a.Ext → ℝ}
    (hb : a.RankBound Tstar) {A : Matrix (a.Row hl.1) (Fin (a.r s(v, u))) ℝ}
    {B : Matrix (a.Col hl.1) (Fin (a.r s(v, u))) ℝ}
    (hAB : a.matricizeOf hl.1 Tstar = A * Bᵀ)
    (hBz : ∀ (l : Fin (a.r s(v, u))), (a.matricizeOf hl.1 Tstar).rank ≤ (l : ℕ) → ∀ j, B j l = 0)
    (hAli : ∀ (g : Fin (a.r s(v, u)) → ℝ),
        (∀ (l : Fin (a.r s(v, u))), (a.matricizeOf hl.1 Tstar).rank ≤ (l : ℕ) → g l = 0) →
        (∑ l, g l • (fun i => A i l)) = 0 → g = 0) :
    (a.reducedArch hl).RankBound (a.Tred hl B) := by
  classical
  -- the reduced cut induces the same bipartition on the surviving vertices (leaf removal)
  have side_corr : ∀ {p q : (a.reducedArch hl).V} (h' : (a.reducedArch hl).G.Adj p q)
      (ha : a.G.Adj p.1 q.1) (z : (a.reducedArch hl).V),
      (a.reducedArch hl).Side h' z ↔ a.Side ha z.1 := by
    intro p q h' ha z
    have hpv : p.1 ≠ v := fun hc => p.2 (Set.mem_singleton_iff.mpr hc)
    have hqv : q.1 ≠ v := fun hc => q.2 (Set.mem_singleton_iff.mpr hc)
    have hzv : z.1 ≠ v := fun hc => z.2 (Set.mem_singleton_iff.mpr hc)
    have hmap : ∀ {x y : (a.reducedArch hl).V}, s(x, y) = s(p, q) ↔ s(x.1, y.1) = s(p.1, q.1) := by
      intro x y
      simp only [Sym2.eq_iff, Subtype.val_inj]
      tauto
    unfold Side
    constructor
    · intro hr
      refine SimpleGraph.Reachable.map ⟨Subtype.val, ?_⟩ hr
      intro x y hxy
      rw [SimpleGraph.deleteEdges_adj] at hxy ⊢
      refine ⟨hxy.1, fun hc => hxy.2 ?_⟩
      rw [Set.mem_singleton_iff] at hc ⊢
      exact hmap.mpr hc
    · intro hr
      obtain ⟨P, hP⟩ := hr.exists_isPath
      have hsub : ((a.G.deleteEdges {s(p.1, q.1)}).neighborSet v).Subsingleton := by
        intro x hx y hy
        rw [SimpleGraph.mem_neighborSet, SimpleGraph.deleteEdges_adj] at hx hy
        rw [hl.2 x hx.1, hl.2 y hy.1]
      have hvnotin : v ∉ P.support :=
        hP.isTrail.not_mem_support_of_subsingleton_neighborSet (Ne.symm hpv) (Ne.symm hzv) hsub
      have hsupp : ∀ x ∈ P.support, x ∈ ({v}ᶜ : Set a.V) := by
        intro x hx
        rw [Set.mem_compl_iff, Set.mem_singleton_iff]
        rintro rfl; exact hvnotin hx
      have hGeq : (a.reducedArch hl).G.deleteEdges {s(p, q)}
          = (a.G.deleteEdges {s(p.1, q.1)}).induce ({v}ᶜ : Set a.V) := by
        ext x y
        simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.comap_adj,
          Set.mem_singleton_iff]
        show (a.G.Adj x.1 y.1 ∧ ¬ s(x, y) = s(p, q))
          ↔ (a.G.Adj x.1 y.1 ∧ ¬ s(x.1, y.1) = s(p.1, q.1))
        rw [hmap]
      rw [hGeq]
      exact (P.induce ({v}ᶜ : Set a.V) hsupp).reachable
  -- key lemma: the configuration where `u` (hence `v`) is on the Side (Row) of the cut
  have keyA : ∀ {p q : (a.reducedArch hl).V} (h' : (a.reducedArch hl).G.Adj p q)
      (ha : a.G.Adj p.1 q.1), a.Side ha u →
      ((a.reducedArch hl).matricizeOf h' (a.Tred hl B)).rank ≤ (a.matricizeOf ha Tstar).rank := by
    intro p q h' ha hSu
    have hpv : p.1 ≠ v := fun hc => p.2 (Set.mem_singleton_iff.mpr hc)
    have hqv : q.1 ≠ v := fun hc => q.2 (Set.mem_singleton_iff.mpr hc)
    have hSv : a.Side ha v := hSu.trans (SimpleGraph.Adj.reachable (by
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨hl.1.symm, ?_⟩
      rw [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨_, h1⟩ | ⟨_, h2⟩)
      · exact hqv h1.symm
      · exact hpv h2.symm))
    -- index correspondence on the free (Col) side
    let eIdx : {z : (a.reducedArch hl).V // ¬ (a.reducedArch hl).Side h' z}
        ≃ {x : a.V // ¬ a.Side ha x} :=
      { toFun := fun z => ⟨z.1.1, fun hc => z.2 ((side_corr h' ha z.1).mpr hc)⟩
        invFun := fun x => ⟨⟨x.1, by
            rw [Set.mem_compl_iff, Set.mem_singleton_iff]
            exact fun hc => (hc ▸ x.2) hSv⟩,
          fun hc => x.2 ((side_corr h' ha _).mp hc)⟩
        left_inv := fun z => by ext; rfl
        right_inv := fun x => by ext; rfl }
    have hzu : ∀ z : {z : (a.reducedArch hl).V // ¬ (a.reducedArch hl).Side h' z}, z.1.1 ≠ u := by
      intro z hc
      exact z.2 ((side_corr h' ha z.1).mpr (by rw [hc]; exact hSu))
    let eCol : (a.reducedArch hl).Col h' ≃ a.Col ha :=
      Equiv.piCongr eIdx (fun z => finCongr (a.reducedArch_n_eq_ne hl z.1 (hzu z)))
    set Mred' := ((a.reducedArch hl).matricizeOf h' (a.Tred hl B)).submatrix id ⇑eCol.symm
      with hMred'
    have hrankred : Mred'.rank = ((a.reducedArch hl).matricizeOf h' (a.Tred hl B)).rank :=
      Matrix.rank_submatrix _ (Equiv.refl _) eCol.symm
    rw [← hrankred]
    refine Matrix.rank_le_rank_of_ker_le (a.matricizeOf ha Tstar) Mred' ?_
    intro w hw
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    -- the leaf-contracted quantity
    let F : a.Row ha → Fin (a.r s(v, u)) → ℝ :=
      fun R j => ∑ C, B ((a.extSplit hl.1 ((a.extSplit ha).symm (R, C))).2) j * w C
    have hFeq : ∀ (R : a.Row ha) j,
        F R j = ∑ C, B ((a.extSplit hl.1 ((a.extSplit ha).symm (R, C))).2) j * w C :=
      fun _ _ => rfl
    -- non-leaf modes of `(extSplit ha).symm` ignore the leaf value
    have hExt_upd : ∀ (R : a.Row ha) (s : Fin (a.n v)) (C : a.Col ha) (y : a.V), y ≠ v →
        (a.extSplit ha).symm (Function.update R ⟨v, hSv⟩ s, C) y
          = (a.extSplit ha).symm (R, C) y := by
      intro R s C y hy
      show (if h : a.Side ha y then _ else _) = (if h : a.Side ha y then _ else _)
      by_cases h : a.Side ha y
      · have hne : (⟨y, h⟩ : {x // a.Side ha x}) ≠ ⟨v, hSv⟩ :=
          fun hc => hy (congrArg Subtype.val hc)
        rw [dif_pos h, dif_pos h]
        exact Function.update_of_ne hne s R
      · rw [dif_neg h, dif_neg h]
    -- M_orig.mulVec expands through the leaf factorization
    have hMorig : ∀ R : a.Row ha, (a.matricizeOf ha Tstar).mulVec w R
        = ∑ j, A (a.rowOf hl (R ⟨v, hSv⟩)) j * F R j := by
      intro R
      have hmv : (a.matricizeOf ha Tstar).mulVec w R
          = ∑ C, (a.matricizeOf ha Tstar) R C * w C := rfl
      rw [hmv]
      have hstep : ∀ C, (a.matricizeOf ha Tstar) R C
          = ∑ j, A (a.rowOf hl (R ⟨v, hSv⟩)) j
              * B ((a.extSplit hl.1 ((a.extSplit ha).symm (R, C))).2) j := by
        intro C
        show Tstar ((a.extSplit ha).symm (R, C)) = _
        rw [a.target_eq_sum hl Tstar A B hAB ((a.extSplit ha).symm (R, C))]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← a.rowOf_eq hl ((a.extSplit ha).symm (R, C)), a.extSplit_symm_row ha R C ⟨v, hSv⟩]
      simp_rw [hstep, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hFeq, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun C _ => by ring)
    -- F is supported on `{< rank}` (hBz)
    have hFsupp : ∀ R (l : Fin (a.r s(v, u))),
        (a.matricizeOf hl.1 Tstar).rank ≤ (l : ℕ) → F R l = 0 := by
      intro R l hl'
      rw [hFeq]
      refine Finset.sum_eq_zero (fun C _ => ?_)
      rw [hBz l hl', zero_mul]
    -- `rowOf` is surjective onto `Row hl.1`
    have hrowOf_surj : Function.Surjective (a.rowOf hl) := by
      intro row
      refine ⟨((a.extSplit hl.1).symm (row, fun y => ⟨0, a.hn y.1⟩)) v, ?_⟩
      rw [a.rowOf_eq hl, Equiv.apply_symm_apply]
    -- F ignores the leaf value
    have hFupd : ∀ (R : a.Row ha) s, F (Function.update R ⟨v, hSv⟩ s) = F R := by
      intro R s
      funext j
      rw [hFeq, hFeq]
      refine Finset.sum_congr rfl (fun C _ => ?_)
      have harg : (a.extSplit hl.1 ((a.extSplit ha).symm (Function.update R ⟨v, hSv⟩ s, C))).2
          = (a.extSplit hl.1 ((a.extSplit ha).symm (R, C))).2 := by
        funext y
        have hyv : y.1 ≠ v := fun hc => y.2 ((a.side_leaf hl y.1).mpr hc)
        show ((a.extSplit ha).symm (Function.update R ⟨v, hSv⟩ s, C)) y.1
          = ((a.extSplit ha).symm (R, C)) y.1
        exact hExt_upd R s C y.1 hyv
      rw [harg]
    -- Claim 1: F ≡ 0
    have hClaim1 : ∀ R j, F R j = 0 := by
      intro R j
      have hkey : ∀ row : a.Row hl.1, ∑ l, A row l * F R l = 0 := by
        intro row
        obtain ⟨s, hs⟩ := hrowOf_surj row
        have hval := congrFun hw (Function.update R ⟨v, hSv⟩ s)
        rw [hMorig, Function.update_self, hs, hFupd] at hval
        exact hval
      have hg : F R = 0 := by
        refine hAli (F R) (hFsupp R) ?_
        funext row
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← hkey row]
        exact Finset.sum_congr rfl (fun l _ => by ring)
      exact congrFun hg j
    -- M_red' side: bridge to F via the reduced cut
    funext R'
    -- `u` as a reduced Side vertex
    let uRed : {z // (a.reducedArch hl).Side h' z} :=
      ⟨a.reducedU hl, (side_corr h' ha (a.reducedU hl)).mpr hSu⟩
    -- bond value packed at `u`
    let jval : Fin (a.r s(v, u)) :=
      (finProdFinEquiv.symm
        (finCongr (a.reducedArch_n_eq_u hl (a.reducedU hl) rfl) (R' uRed))).2
    -- reconstruct an original Row index from `R'` (leaf value arbitrary)
    let combineRow : a.Row ha := fun w =>
      if hwv : w.1 = v then (⟨0, a.hn w.1⟩ : Fin (a.n w.1))
      else if hwu : w.1 = u then
        finCongr (congrArg a.n hwu).symm
          (finProdFinEquiv.symm
            (finCongr (a.reducedArch_n_eq_u hl (a.reducedU hl) rfl) (R' uRed))).1
      else
        finCongr (a.reducedArch_n_eq_ne hl ⟨w.1, hwv⟩ hwu)
          (R' ⟨⟨w.1, hwv⟩, (side_corr h' ha ⟨w.1, hwv⟩).mpr w.2⟩)
    -- the key bridge: the reduced external index is a `pack`
    have hbridge : ∀ C : a.Col ha, ((a.reducedArch hl).extSplit h').symm (R', eCol.symm C)
        = a.pack hl ((a.extSplit ha).symm (combineRow, C)) jval := by
      intro C
      funext z
      show (if h : (a.reducedArch hl).Side h' z then R' ⟨z, h⟩ else (eCol.symm C) ⟨z, h⟩)
        = a.pack hl ((a.extSplit ha).symm (combineRow, C)) jval z
      by_cases hzu : z.1 = u
      · obtain rfl : z = a.reducedU hl := Subtype.ext hzu
        have hzside : (a.reducedArch hl).Side h' (a.reducedU hl) :=
          (side_corr h' ha (a.reducedU hl)).mpr hSu
        rw [dif_pos hzside, a.pack_reducedU hl ((a.extSplit ha).symm (combineRow, C)) jval,
          a.extSplit_symm_row ha combineRow C ⟨u, hSu⟩]
        have hcr : combineRow ⟨u, hSu⟩
            = (finProdFinEquiv.symm
                (finCongr (a.reducedArch_n_eq_u hl (a.reducedU hl) rfl) (R' uRed))).1 := by
          show (if hwv : u = v then (⟨0, a.hn u⟩ : Fin (a.n u))
              else if hwu : u = u then finCongr (congrArg a.n hwu).symm
                (finProdFinEquiv.symm
                  (finCongr (a.reducedArch_n_eq_u hl (a.reducedU hl) rfl) (R' uRed))).1
              else _) = _
          rw [dif_neg hl.1.ne', dif_pos rfl, finCongr_refl, Equiv.refl_apply]
        rw [hcr]
        show R' ⟨a.reducedU hl, hzside⟩
          = finCongr (a.reducedArch_n_eq_u hl (a.reducedU hl) rfl).symm
              (finProdFinEquiv ((finProdFinEquiv.symm
                  (finCongr (a.reducedArch_n_eq_u hl (a.reducedU hl) rfl) (R' uRed))).1,
                (finProdFinEquiv.symm
                  (finCongr (a.reducedArch_n_eq_u hl (a.reducedU hl) rfl) (R' uRed))).2))
        rw [Prod.mk.eta, Equiv.apply_symm_apply, ← finCongr_symm, Equiv.symm_apply_apply]
        exact a.reducedArch_n_eq_u hl (a.reducedU hl) rfl
      · have hzv : z.1 ≠ v := fun hc => z.2 (Set.mem_singleton_iff.mpr hc)
        have hpack : a.pack hl ((a.extSplit ha).symm (combineRow, C)) jval z
            = finCongr (a.reducedArch_n_eq_ne hl z hzu).symm
                ((a.extSplit ha).symm (combineRow, C) z.1) := by
          simp only [Arch.pack, dif_neg hzu]
        by_cases hzside : (a.reducedArch hl).Side h' z
        · rw [dif_pos hzside, hpack]
          have hzsa : a.Side ha z.1 := (side_corr h' ha z).mp hzside
          have hx : (a.extSplit ha).symm (combineRow, C) z.1 = combineRow ⟨z.1, hzsa⟩ :=
            a.extSplit_symm_row ha combineRow C ⟨z.1, hzsa⟩
          have hcr2 : combineRow ⟨z.1, hzsa⟩
              = finCongr (a.reducedArch_n_eq_ne hl z hzu) (R' ⟨z, hzside⟩) := by
            show (if hwv : z.1 = v then (⟨0, a.hn z.1⟩ : Fin (a.n z.1))
                else if hwu : z.1 = u then finCongr (congrArg a.n hwu).symm
                    (finProdFinEquiv.symm
                      (finCongr (a.reducedArch_n_eq_u hl (a.reducedU hl) rfl) (R' uRed))).1
                else finCongr (a.reducedArch_n_eq_ne hl ⟨z.1, hwv⟩ hwu)
                  (R' ⟨⟨z.1, hwv⟩, (side_corr h' ha ⟨z.1, hwv⟩).mpr hzsa⟩))
              = finCongr (a.reducedArch_n_eq_ne hl z hzu) (R' ⟨z, hzside⟩)
            rw [dif_neg hzv, dif_neg hzu]
            rfl
          rw [hx, hcr2, ← finCongr_symm, Equiv.symm_apply_apply]
          exact a.reducedArch_n_eq_ne hl z hzu
        · rw [dif_neg hzside, hpack]
          have hnsa : ¬ a.Side ha z.1 := fun hc => hzside ((side_corr h' ha z).mpr hc)
          have hx : (a.extSplit ha).symm (combineRow, C) z.1 = C ⟨z.1, hnsa⟩ :=
            a.extSplit_symm_col ha combineRow C ⟨z.1, hnsa⟩
          rw [hx]
          rfl
    -- assemble: each column of `Mred'` is an `F` value, which vanishes
    show (Mred' *ᵥ w) R' = 0
    have hcol : ∀ C : a.Col ha, Mred' R' C
        = B ((a.extSplit hl.1 ((a.extSplit ha).symm (combineRow, C))).2) jval := by
      intro C
      show a.Tred hl B (((a.reducedArch hl).extSplit h').symm (R', eCol.symm C)) = _
      rw [hbridge C]
      simp only [Arch.Tred, a.colExtract_pack, a.jExtract_pack]
    have hsum : (Mred' *ᵥ w) R'
        = ∑ C, B ((a.extSplit hl.1 ((a.extSplit ha).symm (combineRow, C))).2) jval * w C := by
      show ∑ C, Mred' R' C * w C = _
      exact Finset.sum_congr rfl (fun C _ => by rw [hcol C])
    rw [hsum, ← hFeq combineRow jval]
    exact hClaim1 combineRow jval
  -- main: dispatch on which side `u` lands on
  intro p q h'
  have ha : a.G.Adj p.1 q.1 := h'
  rw [show (a.reducedArch hl).r s(p, q) = a.r s(p.1, q.1) from rfl]
  by_cases hSu : a.Side ha u
  · exact (keyA h' ha hSu).trans (hb p.1 q.1 ha)
  · -- case B: `u` on the Col side; flip the orientation and reuse `keyA`
    -- (`side_symm_iff_not_side` / `rank_matricizeOf_symm` do the cut-orientation bookkeeping)
    have hSu' : a.Side ha.symm u := (a.side_symm_iff_not_side ha u).mpr hSu
    calc ((a.reducedArch hl).matricizeOf h' (a.Tred hl B)).rank
        = ((a.reducedArch hl).matricizeOf h'.symm (a.Tred hl B)).rank :=
          ((a.reducedArch hl).rank_matricizeOf_symm h' (a.Tred hl B)).symm
      _ ≤ (a.matricizeOf ha.symm Tstar).rank := keyA h'.symm ha.symm hSu'
      _ ≤ a.r s(q.1, p.1) := hb q.1 p.1 ha.symm
      _ = a.r s(p.1, q.1) := by rw [Sym2.eq_swap]

/-! ### Assembly: strong induction on `|V|` -/

/-- Strong-induction core: every architecture satisfying the edge-rank bound realizes its
target, by induction on the number of nodes via leaf removal. -/
theorem rank_le_imp_realizable_aux : ∀ (N : ℕ) (b : Arch), Fintype.card b.V = N →
    ∀ (T : b.Ext → ℝ), b.RankBound T → b.Realizable T := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro b hcard T hb
    by_cases hnt : Nontrivial b.V
    · -- Inductive step: peel a leaf.
      obtain ⟨v, hv⟩ := b.hT.exists_vert_degree_one_of_nontrivial
      obtain ⟨u, hadj, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
      have hl : b.IsLeafWith v u := ⟨hadj, huniq⟩
      obtain ⟨A, B, hAB, hBz, hAli'⟩ :=
        Matrix.exists_factor_of_rank_le (b.matricizeOf hl.1 T) (hb v u hl.1)
      have hAli := Matrix.eq_zero_of_sum_smul_col_eq_zero (hb v u hl.1) hAli'
      have hbr : (b.reducedArch hl).RankBound (b.Tred hl B) :=
        b.reduced_rankBound hl hb hAB hBz hAli
      have hNlt : N - 1 < N := by
        have : 1 < Fintype.card b.V := Fintype.one_lt_card_iff_nontrivial.mpr hnt
        omega
      have hcard' : Fintype.card (b.reducedArch hl).V = N - 1 := by
        show Fintype.card ↥({v}ᶜ : Set b.V) = N - 1
        rw [Fintype.card_compl_set, hcard]
        simp
      obtain ⟨θr, hθr⟩ := ih (N - 1) hNlt (b.reducedArch hl) hcard' (b.Tred hl B) hbr
      refine ⟨b.liftParam hl (fun j xv => A (b.rowOf hl xv) j) θr, ?_⟩
      funext x
      rw [b.represented_liftParam hl _ θr x]
      simp only [hθr, Tred, b.colExtract_pack hl x, b.jExtract_pack hl x, b.rowOf_eq hl x]
      exact (b.target_eq_sum hl T A B hAB x).symm
    · -- Base case: a single node (the model is then just `T` itself).
      have hsub : Subsingleton b.V := not_nontrivial_iff_subsingleton.mp hnt
      obtain ⟨w₀⟩ := b.hT.connected.nonempty
      have hbe : IsEmpty ↥b.G.edgeSet := by
        constructor
        rintro ⟨e, he⟩
        induction e using Sym2.ind with
        | _ p q =>
          rw [SimpleGraph.mem_edgeSet] at he
          exact he.ne (Subsingleton.elim p q)
      haveI : Unique b.Bond :=
        ⟨⟨fun e => isEmptyElim e⟩, fun _ => funext fun e => isEmptyElim e⟩
      refine ⟨fun w _ xv => T (fun w' => Fin.cast (congrArg b.n (Subsingleton.elim w' w)).symm xv),
        ?_⟩
      funext x
      simp only [represented]
      rw [Fintype.sum_unique, Fintype.prod_subsingleton _ w₀]
      congr 1
      funext w'
      apply Fin.ext
      simp only [Fin.val_cast]
      exact (congrArg (fun w => (x w).val) (Subsingleton.elim w' w₀)).symm

/-- **Realizability converse.** The edge-rank bound implies realizability. -/
theorem rank_le_imp_realizable {Tstar : a.Ext → ℝ} (hb : a.RankBound Tstar) :
    a.Realizable Tstar :=
  rank_le_imp_realizable_aux (Fintype.card a.V) a rfl Tstar hb

/-- **Paper correspondence (partial): Proposition C.1, realizability characterization.**
This is the exact aggregate-index rank-characterization clause; it does not formalize the
proposition's prescribed-subspace clause. A target tensor is realizable by the TTN architecture with bond
dimensions `{r_e}` iff every internal-edge matricization has rank at most `r_e`. Combines the
forward direction (`realizable_imp_rank_le`, `TTN/Landscape/Realizability.lean`) with the converse above. -/
theorem realizable_iff_rank_le {Tstar : a.Ext → ℝ} :
    a.Realizable Tstar ↔ a.RankBound Tstar := by
  constructor
  · intro hr u w h; exact a.realizable_imp_rank_le hr h
  · exact a.rank_le_imp_realizable

end Arch

end TTN
