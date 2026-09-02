import TTN.Landscape.RealizabilityConverse

/-!
# No spurious critical points at full Tucker rank

Definition 5.1 (`FullTuckerRank`), the **leaf case** of the environment-rank lemma
(`Hfun_full_col_rank`), and Theorem 5.2: *any critical point of `L` that is not a global minimum is not full Tucker
rank*, equivalently *a full-Tucker-rank critical point of a realizable target is a global minimum*
(`critical_fullRank_isGlobalMin`). The proof is by strong induction on `|V|` using leaf
removal, the reduction in `RealizabilityConverse.lean`, and the QR gauge
`exists_orthonormalize`.

## Scope notes (fidelity)

* The environment-rank lemma is formalized only in the form the induction consumes: the `H_e` factor of a
  **leaf** cut has full column rank. The paper's general lemma (arbitrary edge, either factor) is
  not stated in that full generality here.
* **Realizability** is an explicit hypothesis (`hreal` / `RankBound`) of Theorem 5.2 here. The
  paper's statement leaves it implicit (its proof invokes "Realizability gives
  `rank(T*⁽ᵉ⁾) ≤ r_e`", a standing assumption on the target throughout §5).
* **`Critical`** is stated variationally (all first-order variations vanish); the bridge to
  Mathlib's derivative — `Critical ↔` every line derivative of the loss vanishes, in the
  `HasDerivAt` sense — is `critical_iff_hasDerivAt_line` in `TTN/Landscape/Criticality.lean`.
-/

open scoped Matrix MatrixOrder
namespace TTN

namespace Arch

variable (a : Arch)

/-! ### Definition 5.1 (full Tucker rank) and the critical-point / global-min predicates -/

/-- The **mode-`e` unfolding** `matₑ(W)` of a node tensor `W` at node `v`: rows indexed by the
`e`-bond `Fin r_e`, columns by the remaining incident bonds together with `v`'s external mode.
Splits the bond multi-index `BondIdx v` at the coordinate `e` via `Equiv.piSplitAt`. -/
noncomputable def matE (v : a.V) (e : a.Inc v) (W : a.NodeTensor v) :
    Matrix (Fin (a.r e.1)) (((e' : {e' : a.Inc v // e' ≠ e}) → Fin (a.r e'.1.1)) × Fin (a.n v)) ℝ :=
  fun k rest => W ((Equiv.piSplitAt e (fun e' => Fin (a.r e'.1))).symm (k, rest.1)) rest.2

/-- **Paper correspondence: Definition 5.1, full Tucker rank.** A parameter point `θ` has
*full Tucker rank* if for
every node `v` and every incident bond `e`, the mode-`e` unfolding of `W_v` has full row rank
`r_e`. (Each internal edge `s(u,w)` is incident to both endpoints, so this is exactly Def 5.1:
"for every internal edge and each endpoint, `matₑ(W_v)` has rank `r_e`".) -/
def FullTuckerRank (θ : a.Param) : Prop :=
  ∀ (v : a.V) (e : a.Inc v), (a.matE v e (θ v)).rank = a.r e.1

/-- **Critical point** of the squared loss `L(θ) = ½‖T(θ) - T*‖²`. Variational form: every
first-order variation vanishes. `represented (update θ v δ)` is exactly the directional
derivative of `T` in the direction of perturbing `W_v` by `δ` (the represented tensor is
multilinear — degree one in each node tensor), so this says `∇L(θ) = 0`. -/
def Critical (Tstar : a.Ext → ℝ) (θ : a.Param) : Prop :=
  ∀ (v : a.V) (δ : a.NodeTensor v),
    ∑ x : a.Ext, a.residual Tstar θ x * a.represented (Function.update θ v δ) x = 0

/-- **Global minimum** of the squared loss. -/
def IsGlobalMin (Tstar : a.Ext → ℝ) (θ : a.Param) : Prop :=
  ∀ θ' : a.Param, a.loss Tstar θ ≤ a.loss Tstar θ'

/-! ### Leaf setup: the leaf tensor as an `n_v × r_e` matrix, and its cut factors -/

variable {a}

/-- Every bond incident to a leaf `v` is the leaf edge `s(v, u)`. -/
theorem leaf_inc_eq {v u : a.V} (hl : a.IsLeafWith v u) (e' : a.Inc v) : e'.1 = s(v, u) := by
  have hspec : s(v, Sym2.Mem.other' e'.2.2) = e'.1 := Sym2.other_spec' e'.2.2
  have hadj : a.G.Adj v (Sym2.Mem.other' e'.2.2) := by
    rw [← SimpleGraph.mem_edgeSet, hspec]; exact e'.2.1
  rw [← hspec, hl.2 _ hadj]

/-- The leaf bond multi-index sending `v`'s unique incident edge to `k : Fin r_e`. -/
noncomputable def leafBondIdx {v u : a.V} (hl : a.IsLeafWith v u) (k : Fin (a.r s(v, u))) :
    a.BondIdx v :=
  fun e' => finCongr (congrArg a.r (leaf_inc_eq hl e')).symm k

/-- The **leaf node tensor** as an `n_v × r_e` matrix: `W_v` with its single bond mode as the
column index. This is the left cut factor `F_e` for the leaf cut. -/
noncomputable def Wleaf {v u : a.V} (hl : a.IsLeafWith v u) (θ : a.Param) :
    Matrix (Fin (a.n v)) (Fin (a.r s(v, u))) ℝ :=
  fun xv k => θ v (a.leafBondIdx hl k) xv

/-- The leaf's unique incident bond, packaged as an `Inc v`. -/
def leafInc {v u : a.V} (hl : a.IsLeafWith v u) : a.Inc v :=
  ⟨s(v, u), by rw [SimpleGraph.mem_edgeSet]; exact hl.1, Sym2.mem_mk_left v u⟩

/-! ### Cut factorization at a leaf (`matricize_FH` itself lives in `TTN/Matricization.lean`) -/

/-- For a leaf cut, the left factor `Ffun` is just the leaf node tensor `W_v` (the only `Side` node
is `v`, and its only bond is the cut edge). -/
theorem Ffun_leaf {v u : a.V} (hl : a.IsLeafWith v u) (θ : a.Param)
    (row : a.Row hl.1) (k : Fin (a.r s(v, u))) :
    a.Ffun hl.1 θ row k = θ v (a.leafBondIdx hl k) (row ⟨v, (a.side_leaf hl v).mpr rfl⟩) := by
  classical
  -- No non-cut edge lies entirely on the leaf `Side = {v}`, so `BondSide` is trivial.
  have hemptyBS : IsEmpty {e : a.G.edgeSet // e ≠ a.cutEdge hl.1 ∧ a.EdgeSide hl.1 e} := by
    refine ⟨fun w => ?_⟩
    obtain ⟨⟨s, hs⟩, hw⟩ := w
    revert hs hw
    induction s using Sym2.ind with
    | _ p q =>
      intro hs hw
      obtain ⟨_, hes⟩ := hw
      have hpv : p = v := (a.side_leaf hl p).mp (hes p (Sym2.mem_mk_left p q))
      have hqv : q = v := (a.side_leaf hl q).mp (hes q (Sym2.mem_mk_right p q))
      rw [SimpleGraph.mem_edgeSet] at hs
      exact hs.ne (hpv.trans hqv.symm)
  haveI : Unique (a.BondSide hl.1) := by
    haveI := hemptyBS
    exact ⟨⟨fun e => isEmptyElim e⟩, fun f => funext fun e => isEmptyElim e⟩
  haveI : Subsingleton {p // a.Side hl.1 p} :=
    ⟨fun x y => Subtype.ext ((a.side_leaf hl x.1).mp x.2 |>.trans ((a.side_leaf hl y.1).mp y.2).symm)⟩
  have hval : ∀ {x y : a.G.edgeSet} (h : x = y) (k' : Fin (a.r x.1)),
      ((h ▸ k' : Fin (a.r y.1))).val = k'.val := fun h k' => by cases h; rfl
  simp only [Ffun]
  rw [Fintype.sum_unique, Fintype.prod_subsingleton _ ⟨v, (a.side_leaf hl v).mpr rfl⟩]
  congr 1
  funext e'
  have he' : (⟨e'.1, e'.2.1⟩ : a.G.edgeSet) = a.cutEdge hl.1 := Subtype.ext (leaf_inc_eq hl e')
  apply Fin.ext
  simp only [Bond.restrict, bondInvFun, leafBondIdx, dif_pos he', finCongr_apply, Fin.val_cast]
  exact hval he'.symm k

/-- `Hfun` depends only on the non-`Side` (column-side) node tensors, so updating a `Side` node
leaves it unchanged. In particular the leaf cut's `Hfun` ignores the leaf tensor. -/
theorem Hfun_update_side {x y : a.V} (h : a.G.Adj x y) (θ : a.Param)
    {z : a.V} (hz : a.Side h z) (δ : a.NodeTensor z) :
    a.Hfun h (Function.update θ z δ) = a.Hfun h θ := by
  funext col k
  simp only [Hfun]
  refine Finset.sum_congr rfl (fun bc _ => Finset.prod_congr rfl (fun w _ => ?_))
  have hwz : w.1 ≠ z := fun hc => w.2 (hc ▸ hz)
  rw [Function.update_of_ne hwz]

/-- `rowOf` recovers a `Row` index from its leaf value. -/
theorem rowOf_v_value {v u : a.V} (hl : a.IsLeafWith v u) (row : a.Row hl.1) :
    a.rowOf hl (row ⟨v, (a.side_leaf hl v).mpr rfl⟩) = row := by
  funext y
  have hy : y.1 = v := (a.side_leaf hl y.1).mp y.2
  apply Fin.ext
  simp only [rowOf, finCongr_apply, Fin.val_cast]
  exact (congrArg (fun z => (row z).val) (Subtype.ext hy.symm : (⟨v, _⟩ : {p // a.Side hl.1 p}) = y))

/-- **Criticality at the leaf pins the residual's column space** (Theorem 5.2, Step 1): the
matricized residual, right-multiplied by the cut factor `Hfun`, vanishes. This is where the
variational `Critical` condition feeds the linear-algebra argument. -/
theorem crit_leaf {v u : a.V} (hl : a.IsLeafWith v u) {Tstar : a.Ext → ℝ} {θ : a.Param}
    (hcrit : a.Critical Tstar θ) :
    a.matricizeOf hl.1 (a.residual Tstar θ) * a.Hfun hl.1 θ = 0 := by
  classical
  set Rmat := a.matricizeOf hl.1 (a.residual Tstar θ) with hRmat
  set P := Rmat * a.Hfun hl.1 θ with hP
  -- Feeding a leaf perturbation `δ` into criticality gives ⟨P, Ffun(update)⟩ = 0.
  have hkey : ∀ δ : a.NodeTensor v,
      ∑ row : a.Row hl.1, ∑ k, P row k * a.Ffun hl.1 (Function.update θ v δ) row k = 0 := by
    intro δ
    have hc := hcrit v δ
    rw [← (a.extSplit hl.1).symm.sum_comp
      (fun x => a.residual Tstar θ x * a.represented (Function.update θ v δ) x),
      Fintype.sum_prod_type] at hc
    -- each summand is `Rmat row col * matricize(update) row col`
    have hmat : a.matricize hl.1 (Function.update θ v δ)
        = a.Ffun hl.1 (Function.update θ v δ) * (a.Hfun hl.1 θ)ᵀ := by
      rw [a.matricize_FH hl.1 (Function.update θ v δ),
        a.Hfun_update_side hl.1 θ ((a.side_leaf hl v).mpr rfl) δ]
    have hstep : ∀ row col,
        a.residual Tstar θ ((a.extSplit hl.1).symm (row, col))
          * a.represented (Function.update θ v δ) ((a.extSplit hl.1).symm (row, col))
        = ∑ k, (Rmat row col) * (a.Ffun hl.1 (Function.update θ v δ) row k
            * a.Hfun hl.1 θ col k) := by
      intro row col
      have h1 : a.residual Tstar θ ((a.extSplit hl.1).symm (row, col)) = Rmat row col := rfl
      have h2 : a.represented (Function.update θ v δ) ((a.extSplit hl.1).symm (row, col))
          = a.matricize hl.1 (Function.update θ v δ) row col := rfl
      rw [h1, h2, hmat, Matrix.mul_apply]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by rw [Matrix.transpose_apply])
    -- reassemble into `∑ row ∑ k P row k * Ffun(update) row k`
    rw [Finset.sum_congr rfl (fun row _ =>
      Finset.sum_congr rfl (fun col _ => hstep row col))] at hc
    -- hc : ∑ row ∑ col ∑ k Rmat row col * (Ffun row k * Hfun col k) = 0
    rw [← hc]
    refine Finset.sum_congr rfl (fun row _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hP, Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun col _ => by ring)
  -- Choose `δ` reproducing `P`, then ⟨P,P⟩ = 0 ⟹ P = 0.
  set δP : a.NodeTensor v := fun bond xv => P (a.rowOf hl xv) (bond (a.leafInc hl)) with hδP
  have hFfunP : a.Ffun hl.1 (Function.update θ v δP) = P := by
    funext row k
    rw [a.Ffun_leaf hl (Function.update θ v δP) row k, Function.update_self]
    show P (a.rowOf hl (row ⟨v, (a.side_leaf hl v).mpr rfl⟩))
        (a.leafBondIdx hl k (a.leafInc hl)) = P row k
    rw [a.rowOf_v_value hl row]
    congr 1
  have hPP := hkey δP
  rw [hFfunP] at hPP
  have : ∀ row : a.Row hl.1, ∀ k, P row k = 0 := by
    have hnn : ∀ row : a.Row hl.1, (0 : ℝ) ≤ ∑ k, P row k * P row k :=
      fun row => Finset.sum_nonneg fun k _ => mul_self_nonneg _
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun row _ => hnn row)).mp hPP
    intro row k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_self_nonneg (P row k))).mp
      (hz row (Finset.mem_univ row)) k (Finset.mem_univ k)
    exact mul_self_eq_zero.mp this
  funext row k
  exact this row k

/-! ### Reduced parameters: decomposing `θ` as `liftParam` of a leaf tensor + reduced params

The inverse of `liftParam`: strip a leaf, absorbing its bond into `u`'s external mode.
This lets the induction apply its hypothesis to `reducedParam θ` on the smaller tree. -/

/-- An original edge (with both endpoints off the leaf `v`) is a reduced edge. -/
theorem reduced_edge_mem' {v u : a.V} (hl : a.IsLeafWith v u) :
    ∀ (s : Sym2 a.V), s ∈ a.G.edgeSet → ∀ (hp : ∀ y ∈ s, y ∈ ({v}ᶜ : Set a.V)),
      Sym2.attachWith s hp ∈ (a.reducedArch hl).G.edgeSet := by
  intro s
  induction s using Sym2.ind with
  | _ p q =>
    intro hs hp
    rw [SimpleGraph.mem_edgeSet] at hs
    exact (SimpleGraph.mem_edgeSet _).mpr hs

/-- Push an original incidence at `wr` (whose edge avoids the leaf `v`) into the reduced
architecture — the inverse of `incReducedToOrig`. -/
def origIncToReduced {v u : a.V} (hl : a.IsLeafWith v u) {wr : (a.reducedArch hl).V}
    (e'' : a.Inc wr.1) (hp : ∀ y ∈ e''.1, y ∈ ({v}ᶜ : Set a.V)) : (a.reducedArch hl).Inc wr :=
  ⟨Sym2.attachWith e''.1 hp, a.reduced_edge_mem' hl e''.1 e''.2.1 hp, by
    have hmem : wr.1 ∈ Sym2.map Subtype.val (Sym2.attachWith e''.1 hp) := by
      rw [Sym2.attachWith_map_subtypeVal]; exact e''.2.2
    obtain ⟨y, hy, hyv⟩ := Sym2.mem_map.mp hmem
    have : y = wr := Subtype.ext hyv
    exact this ▸ hy⟩

/-- If a bond incident to a reduced vertex `wr` avoids the leaf edge, its far endpoint avoids `v`. -/
theorem inc_notMem_v {v u : a.V} (hl : a.IsLeafWith v u) {wr : (a.reducedArch hl).V}
    (e'' : a.Inc wr.1) (hne : e''.1 ≠ s(v, u)) : ∀ y ∈ e''.1, y ∈ ({v}ᶜ : Set a.V) := by
  intro y hy
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  rintro rfl
  -- now `v ∈ e''.1` and `wr.1 ∈ e''.1`, with `wr.1 ≠ v`
  have hwrv : wr.1 ≠ y := by
    have h2 := wr.2
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at h2
    exact h2
  have hek : e''.1 = s(wr.1, y) := (Sym2.mem_and_mem_iff hwrv).mp ⟨e''.2.2, hy⟩
  have hadj : a.G.Adj wr.1 y := by
    rw [← SimpleGraph.mem_edgeSet, ← hek]; exact e''.2.1
  exact hne (hek.trans (by rw [hl.2 wr.1 hadj.symm, Sym2.eq_swap]))

/-- A bond incident to a reduced vertex other than `u` is never the leaf edge. -/
theorem inc_ne_leaf {v u : a.V} (hl : a.IsLeafWith v u) {wr : (a.reducedArch hl).V}
    (hwu : wr.1 ≠ u) (e'' : a.Inc wr.1) : e''.1 ≠ s(v, u) := by
  intro he
  have hmem : wr.1 ∈ s(v, u) := he ▸ e''.2.2
  rw [Sym2.mem_iff] at hmem
  have hwrv : wr.1 ≠ v := by
    have h2 := wr.2
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at h2
    exact h2
  rcases hmem with h | h
  · exact hwrv h
  · exact hwu h

/-- **Reduced parameters** (inverse of `liftParam`): peel the leaf `v`, folding its bond into `u`'s
external mode. Satisfies `liftParam hl (leaf tensor of θ) (reducedParam θ) = θ`. -/
noncomputable def reducedParam {v u : a.V} (hl : a.IsLeafWith v u) (θ : a.Param) :
    (a.reducedArch hl).Param :=
  fun wr bi' xr' =>
    if hwu : wr.1 = u then
      θ wr.1
        (fun e'' => if he : e''.1 = s(v, u)
          then finCongr (congrArg a.r he.symm)
            (finProdFinEquiv.symm (finCongr (a.reducedArch_n_eq_u hl wr hwu) xr')).2
          else finCongr (congrArg a.r (Sym2.attachWith_map_subtypeVal (a.inc_notMem_v hl e'' he)))
            (bi' (a.origIncToReduced hl e'' (a.inc_notMem_v hl e'' he))))
        (finCongr (show a.n u = a.n wr.1 by rw [hwu])
          (finProdFinEquiv.symm (finCongr (a.reducedArch_n_eq_u hl wr hwu) xr')).1)
    else
      θ wr.1
        (fun e'' => finCongr (congrArg a.r (Sym2.attachWith_map_subtypeVal
            (a.inc_notMem_v hl e'' (a.inc_ne_leaf hl hwu e''))))
          (bi' (a.origIncToReduced hl e'' (a.inc_notMem_v hl e'' (a.inc_ne_leaf hl hwu e'')))))
        (finCongr (a.reducedArch_n_eq_ne hl wr hwu) xr')

/-- **Decomposition of `θ`.** Any parameter point is `liftParam` of its own leaf tensor and reduced
parameters. This lets the induction pass to the reduced tree. -/
theorem liftParam_reducedParam {v u : a.V} (hl : a.IsLeafWith v u) (θ : a.Param) :
    a.liftParam hl (fun j xv => a.Wleaf hl θ xv j) (a.reducedParam hl θ) = θ := by
  classical
  funext w bi xw
  rw [liftParam]
  by_cases hwv : w = v
  · rw [dif_pos hwv]
    subst hwv
    haveI hss : Subsingleton (a.Inc w) :=
      ⟨fun e1 e2 => Subtype.ext ((leaf_inc_eq hl e1).trans (leaf_inc_eq hl e2).symm)⟩
    simp only [Wleaf, finCongr_refl, Equiv.refl_apply]
    congr 1
    funext e'
    apply Fin.ext
    simp only [leafBondIdx, finCongr_apply, Fin.val_cast]
    rw [Subsingleton.elim e' (a.leafInc hl)]
    rfl
  · rw [dif_neg hwv]
    by_cases hwu : w = u
    · rw [dif_pos hwu]
      subst hwu
      rw [reducedParam, dif_pos (show (a.reducedU hl).1 = w from rfl)]
      congr 1
      · funext e''
        by_cases he : e''.1 = s(v, w)
        · rw [dif_pos he]
          apply Fin.ext
          simp [Fin.val_cast]
          exact (congrArg (fun z : a.Inc w => ((bi z).val : ℕ))
            (show e'' = (⟨s(v, w), by rw [SimpleGraph.mem_edgeSet]; exact hl.1,
                Sym2.mem_mk_right v w⟩ : a.Inc w) from Subtype.ext he)).symm
        · rw [dif_neg he]
          have hround : a.incReducedToOrig hl
              (a.origIncToReduced hl e'' (a.inc_notMem_v hl e'' he)) = e'' :=
            Subtype.ext (Sym2.attachWith_map_subtypeVal _)
          apply Fin.ext
          simp [Fin.val_cast]
          exact congrArg (fun z : a.Inc w => ((bi z).val : ℕ)) hround
      · apply Fin.ext
        simp [Fin.val_cast]
    · rw [dif_neg hwu]
      rw [reducedParam, dif_neg hwu]
      congr 1
      funext e''
      have hround : a.incReducedToOrig hl
          (a.origIncToReduced hl e'' (a.inc_notMem_v hl e'' (a.inc_ne_leaf hl hwu e''))) = e'' :=
        Subtype.ext (Sym2.attachWith_map_subtypeVal _)
      apply Fin.ext
      simp [Fin.val_cast]
      exact congrArg (fun z : a.Inc w => ((bi z).val : ℕ)) hround

/-! ### Rank lemmas for the leaf reduction -/

/-- The mode-`e` unfolding at the leaf incidence has the same rank as the leaf matrix `W_v`:
for a leaf `v` the remaining-bond coordinate of `matₑ(W_v)` is trivial (a leaf has a unique
incident bond), so the unfolding is `Wleafᵀ` up to column reindexing. -/
theorem matE_leafInc_rank {v u : a.V} (hl : a.IsLeafWith v u) (θ' : a.Param) :
    (a.matE v (a.leafInc hl) (θ' v)).rank = (a.Wleaf hl θ').rank := by
  classical
  haveI hss : Subsingleton (a.Inc v) :=
    ⟨fun e1 e2 => Subtype.ext ((leaf_inc_eq hl e1).trans (leaf_inc_eq hl e2).symm)⟩
  have hemp : IsEmpty {e' : a.Inc v // e' ≠ a.leafInc hl} :=
    ⟨fun e' => e'.2 (Subsingleton.elim _ _)⟩
  haveI huniq : Subsingleton ((e' : {e' : a.Inc v // e' ≠ a.leafInc hl}) → Fin (a.r e'.1.1)) := by
    haveI := hemp; infer_instance
  -- Collapse the (trivial) remaining-bond product coordinate.
  let ecol : ((e' : {e' : a.Inc v // e' ≠ a.leafInc hl}) → Fin (a.r e'.1.1)) × Fin (a.n v)
      ≃ Fin (a.n v) :=
    { toFun := Prod.snd
      invFun := fun xv => (fun e' => (hemp.false e').elim, xv)
      left_inv := fun p => Prod.ext (Subsingleton.elim _ _) rfl
      right_inv := fun _ => rfl }
  -- `matₑ(W_v)` is `Wleafᵀ` after collapsing that coordinate.
  have hmatE : a.matE v (a.leafInc hl) (θ' v)
      = (a.Wleaf hl θ')ᵀ.submatrix (Equiv.refl _) ecol := by
    ext k p
    obtain ⟨rest, xv⟩ := p
    simp only [matE, Matrix.submatrix_apply, Matrix.transpose_apply, Wleaf, Equiv.refl_apply]
    show (θ' v) ((Equiv.piSplitAt (a.leafInc hl) fun e' => Fin (a.r e'.1)).symm (k, rest)) xv
      = (θ' v) (a.leafBondIdx hl k) xv
    congr 1
    funext j
    have hj : j = a.leafInc hl := Subsingleton.elim _ _
    subst hj
    simp only [Equiv.piSplitAt_symm_apply, leafBondIdx]
    rfl
  calc (a.matE v (a.leafInc hl) (θ' v)).rank
      = ((a.Wleaf hl θ')ᵀ.submatrix (Equiv.refl _) ecol).rank := congrArg Matrix.rank hmatE
    _ = (a.Wleaf hl θ')ᵀ.rank := Matrix.rank_submatrix _ _ _
    _ = (a.Wleaf hl θ').rank := Matrix.rank_transpose _

/-- **Leaf full column rank.** For a leaf `v`, the mode-`e` unfolding *is* `W_v` (only one incident
bond, `matE_leafInc_rank`), so full Tucker rank at `v` makes the leaf tensor `W_v` an `n_v × r_e`
matrix of full column rank `r_e`. -/
theorem Wleaf_full_col_rank {v u : a.V} (hl : a.IsLeafWith v u) {θ : a.Param}
    (hftr : a.FullTuckerRank θ) : (a.Wleaf hl θ).rank = a.r s(v, u) := by
  rw [← a.matE_leafInc_rank hl θ]
  exact hftr v (a.leafInc hl)

/-- **Orthonormalization / reduced QR** (pure linear algebra). A real matrix of full column rank
admits an invertible right factor making its columns orthonormal (`(W M)ᵀ (W M) = 1`). This is the
gauge normalization of Theorem 5.2 Step 0 (`W_v = Q S`, keep `Q`). Isolated; proved via congruence
of the SPD Gram matrix `WᵀW` to the identity (Cholesky / spectral). -/
theorem exists_orthonormalize {m k : ℕ} (W : Matrix (Fin m) (Fin k) ℝ) (hW : W.rank = k) :
    ∃ M : Matrix (Fin k) (Fin k) ℝ, IsUnit M.det ∧ (W * M)ᵀ * (W * M) = 1 := by
  -- G := Wᵀ * W is positive semidefinite
  have hGpsd : (Wᵀ * W).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self W
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hGnonneg : (0 : Matrix (Fin k) (Fin k) ℝ) ≤ Wᵀ * W :=
    Matrix.nonneg_iff_posSemidef.mpr hGpsd
  -- G has full rank k, hence its determinant is a unit
  have hGrank : (Wᵀ * W).rank = k := by rw [Matrix.rank_transpose_mul_self]; exact hW
  have hGunit : IsUnit (Wᵀ * W) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit,
        linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    rw [Matrix.rank_eq_finrank_span_cols] at hGrank
    exact hGrank.symm
  have hGdet : IsUnit (Wᵀ * W).det := (Matrix.isUnit_iff_isUnit_det _).mp hGunit
  -- S := √G satisfies S * S = G, is symmetric, and has unit determinant
  set S := CFC.sqrt (Wᵀ * W) with hSdef
  have hSS : S * S = Wᵀ * W := CFC.sqrt_mul_sqrt_self (Wᵀ * W) hGnonneg
  have hSsymm : Sᵀ = S := by
    have hpsd : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
    have h1 : Sᴴ = S := hpsd.1
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
  have hSdet : IsUnit S.det := by
    rw [isUnit_iff_ne_zero]
    intro h
    apply hGdet.ne_zero
    rw [← hSS, Matrix.det_mul, h, mul_zero]
  -- M := S⁻¹ works
  refine ⟨S⁻¹, ?_, ?_⟩
  · have h1 : (S⁻¹).det * S.det = 1 := by
      rw [← Matrix.det_mul, Matrix.nonsing_inv_mul _ hSdet, Matrix.det_one]
    rw [isUnit_iff_ne_zero]
    intro hz
    rw [hz, zero_mul] at h1
    exact one_ne_zero h1.symm
  · have hMt : (S⁻¹)ᵀ = S⁻¹ := by rw [Matrix.transpose_nonsing_inv, hSsymm]
    rw [Matrix.transpose_mul, hMt]
    have expand : S⁻¹ * Wᵀ * (W * S⁻¹) = S⁻¹ * (Wᵀ * W) * S⁻¹ := by
      simp only [Matrix.mul_assoc]
    rw [expand, ← hSS, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSdet,
      Matrix.one_mul, Matrix.mul_nonsing_inv _ hSdet]

/-- Round-trip: `incReducedToOrig` undoes `origIncToReduced`. -/
theorem incReducedToOrig_origIncToReduced {v u : a.V} (hl : a.IsLeafWith v u)
    {wr : (a.reducedArch hl).V} (e'' : a.Inc wr.1)
    (hp : ∀ y ∈ e''.1, y ∈ ({v}ᶜ : Set a.V)) :
    a.incReducedToOrig hl (a.origIncToReduced hl e'' hp) = e'' := by
  apply Subtype.ext
  show Sym2.map Subtype.val (Sym2.attachWith e''.1 hp) = e''.1
  exact Sym2.attachWith_map_subtypeVal hp

/-- Attaching a proof after pushing a `Sym2` over a subtype forward by `val` is the identity. -/
theorem attachWith_map_subtypeVal_self {α : Type*} {p : α → Prop} (s : Sym2 {x // p x})
    (hp : ∀ y ∈ Sym2.map Subtype.val s, p y) :
    Sym2.attachWith (Sym2.map Subtype.val s) hp = s := by
  revert hp
  induction s using Sym2.ind with
  | _ x y => intro hp; rfl

/-- Round-trip: `origIncToReduced` undoes `incReducedToOrig`. -/
theorem origIncToReduced_incReducedToOrig {v u : a.V} (hl : a.IsLeafWith v u)
    {wr : (a.reducedArch hl).V} (e' : (a.reducedArch hl).Inc wr)
    (hp : ∀ y ∈ (a.incReducedToOrig hl e').1, y ∈ ({v}ᶜ : Set a.V)) :
    a.origIncToReduced hl (a.incReducedToOrig hl e') hp = e' := by
  apply Subtype.ext
  exact attachWith_map_subtypeVal_self e'.1 hp

/-- `origIncToReduced` and `incReducedToOrig` are mutually inverse: the reduced-incidence
equation is equivalent to the original-incidence equation. -/
theorem origIncToReduced_eq_iff {v u : a.V} (hl : a.IsLeafWith v u)
    {wr : (a.reducedArch hl).V} {e'' : a.Inc wr.1}
    (hp : ∀ y ∈ e''.1, y ∈ ({v}ᶜ : Set a.V)) (e' : (a.reducedArch hl).Inc wr) :
    a.origIncToReduced hl e'' hp = e' ↔ e'' = a.incReducedToOrig hl e' := by
  constructor
  · intro h
    rw [← a.incReducedToOrig_origIncToReduced hl e'' hp, h]
  · intro h
    subst h
    exact a.origIncToReduced_incReducedToOrig hl e' hp

/-- A reduced incidence, pushed to the original graph, is never the leaf edge. -/
theorem incReducedToOrig_ne_leaf {v u : a.V} (hl : a.IsLeafWith v u)
    {wr : (a.reducedArch hl).V} (e' : (a.reducedArch hl).Inc wr) :
    (a.incReducedToOrig hl e').1 ≠ s(v, u) := by
  intro hcon
  have hv : v ∈ Sym2.map Subtype.val e'.1 := by
    show v ∈ (a.incReducedToOrig hl e').1
    rw [hcon]; exact Sym2.mem_mk_left v u
  obtain ⟨y, _, hyv⟩ := Sym2.mem_map.mp hv
  exact y.2 (Set.mem_singleton_iff.mpr hyv)

/-- `incReducedToOrig` preserves distinctness (it is injective on incidences). -/
theorem incReducedToOrig_ne {v u : a.V} (hl : a.IsLeafWith v u)
    {wr : (a.reducedArch hl).V} {E e' : (a.reducedArch hl).Inc wr} (h : E ≠ e') :
    a.incReducedToOrig hl E ≠ a.incReducedToOrig hl e' := by
  intro hc
  apply h
  have hp : ∀ z ∈ (a.incReducedToOrig hl E).1, z ∈ ({v}ᶜ : Set a.V) :=
    a.inc_notMem_v hl (a.incReducedToOrig hl E) (a.incReducedToOrig_ne_leaf hl E)
  rw [← a.origIncToReduced_incReducedToOrig hl E hp]
  exact (a.origIncToReduced_eq_iff hl hp e').mpr hc

/-- Transporting a `Fin (g i)` along an index equality preserves the underlying value. -/
theorem val_eqRec {ι : Type*} {g : ι → ℕ} {i j : ι} (h : j = i) (k : Fin (g i)) :
    (h ▸ k : Fin (g j)).val = k.val := by cases h; rfl

/-- `finCongr` composed with its inverse cancels. -/
theorem finCongr_finCongr_symm {m n : ℕ} (h : m = n) (x : Fin n) :
    finCongr h (finCongr h.symm x) = x := by cases h; rfl

/-- `finCongr` composed with its inverse cancels (other order). -/
theorem finCongr_symm_finCongr {m n : ℕ} (h : m = n) (x : Fin m) :
    finCongr h.symm (finCongr h x) = x := by cases h; rfl

/-- **Reduced full Tucker rank** (Theorem 5.2, Step 2). Unfolding ranks at the surviving nodes are
unchanged, so the reduced parameters again have full Tucker rank. -/
theorem reduced_fullRank {v u : a.V} (hl : a.IsLeafWith v u) {θ : a.Param}
    (hftr : a.FullTuckerRank θ) : (a.reducedArch hl).FullTuckerRank (a.reducedParam hl θ) := by
  classical
  intro wr e'
  suffices key : ((a.reducedArch hl).matE wr e' (a.reducedParam hl θ wr)).rank
      = (a.matE wr.1 (a.incReducedToOrig hl e') (θ wr.1)).rank by
    rw [key]; exact hftr wr.1 (a.incReducedToOrig hl e')
  by_cases hwu : wr.1 = u
  · -- case wr.1 = u : the leaf bond folds into u's bumped external mode
    have hnu : a.n wr.1 = a.n u := by rw [hwu]
    let leafI : a.Inc wr.1 :=
      ⟨s(v, u), by rw [SimpleGraph.mem_edgeSet]; exact hl.1, by rw [hwu]; exact Sym2.mem_mk_right v u⟩
    have hleafI_ne : leafI ≠ a.incReducedToOrig hl e' :=
      fun h => a.incReducedToOrig_ne_leaf hl e' (congrArg Subtype.val h.symm)
    let en :
        (((F : {F : a.Inc wr.1 // F ≠ a.incReducedToOrig hl e'}) → Fin (a.r F.1.1))
            × Fin (a.n wr.1))
          ≃ (((E : {E : (a.reducedArch hl).Inc wr // E ≠ e'}) → Fin ((a.reducedArch hl).r E.1.1))
            × Fin ((a.reducedArch hl).n wr)) :=
      { toFun := fun REST =>
          ( fun E => REST.1 ⟨a.incReducedToOrig hl E.1, a.incReducedToOrig_ne hl E.2⟩,
            finCongr (a.reducedArch_n_eq_u hl wr hwu).symm
              (finProdFinEquiv (finCongr hnu REST.2, REST.1 ⟨leafI, hleafI_ne⟩)) )
        invFun := fun RED =>
          ( fun F => if hF : F.1.1 = s(v, u)
              then finCongr (congrArg a.r hF.symm)
                (finProdFinEquiv.symm (finCongr (a.reducedArch_n_eq_u hl wr hwu) RED.2)).2
              else finCongr (congrArg a.r (Sym2.attachWith_map_subtypeVal (a.inc_notMem_v hl F.1 hF)))
                (RED.1 ⟨a.origIncToReduced hl F.1 (a.inc_notMem_v hl F.1 hF),
                  fun hc => F.2 ((a.origIncToReduced_eq_iff hl _ e').mp hc)⟩),
            finCongr hnu.symm (finProdFinEquiv.symm (finCongr (a.reducedArch_n_eq_u hl wr hwu) RED.2)).1 )
        left_inv := by
          intro REST
          have hfold : finProdFinEquiv.symm (finCongr (a.reducedArch_n_eq_u hl wr hwu)
              (finCongr (a.reducedArch_n_eq_u hl wr hwu).symm
                (finProdFinEquiv (finCongr hnu REST.2, REST.1 ⟨leafI, hleafI_ne⟩))))
              = (finCongr hnu REST.2, REST.1 ⟨leafI, hleafI_ne⟩) := by
            rw [finCongr_finCongr_symm, Equiv.symm_apply_apply]
          apply Prod.ext
          · funext F
            by_cases hF : F.1.1 = s(v, u)
            · simp only [dif_pos hF, hfold]
              apply Fin.ext
              simp only [finCongr_apply, Fin.val_cast]
              exact congrArg (fun x : {G // G ≠ a.incReducedToOrig hl e'} => (REST.1 x).val)
                (Subtype.ext (Subtype.ext hF).symm :
                  (⟨leafI, hleafI_ne⟩ : {G // G ≠ a.incReducedToOrig hl e'}) = F)
            · simp only [dif_neg hF]
              apply Fin.ext
              simp only [finCongr_apply, Fin.val_cast]
              exact congrArg (fun x : {G // G ≠ a.incReducedToOrig hl e'} => (REST.1 x).val)
                (Subtype.ext (a.incReducedToOrig_origIncToReduced hl F.1 (a.inc_notMem_v hl F.1 hF)) :
                  (⟨a.incReducedToOrig hl (a.origIncToReduced hl F.1 (a.inc_notMem_v hl F.1 hF)),
                      a.incReducedToOrig_ne hl (fun hc => F.2 ((a.origIncToReduced_eq_iff hl _ e').mp hc))⟩
                    : {G // G ≠ a.incReducedToOrig hl e'}) = F)
          · simp only [hfold]
            apply Fin.ext
            simp only [finCongr_apply, Fin.val_cast]
        right_inv := by
          intro RED
          apply Prod.ext
          · funext E
            simp only [dif_neg (a.incReducedToOrig_ne_leaf hl E.1)]
            apply Fin.ext
            simp only [finCongr_apply, Fin.val_cast]
            refine congrArg (fun x : {D // D ≠ e'} => (RED.1 x).val) ?_
            exact Subtype.ext (a.origIncToReduced_incReducedToOrig hl E.1 _)
          · have hc : (leafI).1 = s(v, u) := rfl
            have hleaf_eq : finCongr (congrArg a.r hc.symm)
                  (finProdFinEquiv.symm (finCongr (a.reducedArch_n_eq_u hl wr hwu) RED.2)).2
                = (finProdFinEquiv.symm (finCongr (a.reducedArch_n_eq_u hl wr hwu) RED.2)).2 := by
              apply Fin.ext; simp only [finCongr_apply, Fin.val_cast]
            dsimp only
            rw [dif_pos hc, finCongr_finCongr_symm, hleaf_eq, Prod.mk.eta,
              Equiv.apply_symm_apply, finCongr_symm_finCongr] }
    have hsub : a.matE wr.1 (a.incReducedToOrig hl e') (θ wr.1)
        = ((a.reducedArch hl).matE wr e' (a.reducedParam hl θ wr)).submatrix (Equiv.refl _) en := by
      ext K REST
      simp only [Matrix.submatrix_apply, Equiv.refl_apply, matE, reducedParam, dif_pos hwu]
      have hfold : finProdFinEquiv.symm (finCongr (a.reducedArch_n_eq_u hl wr hwu) (en REST).2)
          = (finCongr hnu REST.2, REST.1 ⟨leafI, hleafI_ne⟩) := by
        show finProdFinEquiv.symm (finCongr (a.reducedArch_n_eq_u hl wr hwu)
            (finCongr (a.reducedArch_n_eq_u hl wr hwu).symm
              (finProdFinEquiv (finCongr hnu REST.2, REST.1 ⟨leafI, hleafI_ne⟩)))) = _
        rw [finCongr_finCongr_symm, Equiv.symm_apply_apply]
      simp only [hfold]
      refine congr_arg₂ _ ?_ ?_
      · funext e''
        by_cases he : e''.1 = s(v, u)
        · rw [dif_pos he]
          have he_ne : e'' ≠ a.incReducedToOrig hl e' :=
            fun hc => a.incReducedToOrig_ne_leaf hl e' ((congrArg Subtype.val hc).symm.trans he)
          rw [Equiv.piSplitAt_symm_apply, dif_neg he_ne]
          apply Fin.ext
          simp only [finCongr_apply, Fin.val_cast]
          exact congrArg (fun x : {F // F ≠ a.incReducedToOrig hl e'} => (REST.1 x).val)
            (Subtype.ext (Subtype.ext he : e'' = leafI))
        · rw [dif_neg he]
          rw [Equiv.piSplitAt_symm_apply, Equiv.piSplitAt_symm_apply]
          by_cases hE : e'' = a.incReducedToOrig hl e'
          · rw [dif_pos hE, dif_pos ((a.origIncToReduced_eq_iff hl _ e').mpr hE)]
            apply Fin.ext
            simp only [finCongr_apply, Fin.val_cast]
            exact (val_eqRec (g := fun x : a.Inc wr.1 => a.r x.1) hE K).trans
              (val_eqRec (g := fun E : (a.reducedArch hl).Inc wr => (a.reducedArch hl).r E.1)
                ((a.origIncToReduced_eq_iff hl _ e').mpr hE) K).symm
          · have hp'' : ∀ y ∈ e''.1, y ∈ ({v}ᶜ : Set a.V) := a.inc_notMem_v hl e'' he
            have hne'' : a.origIncToReduced hl e'' hp'' ≠ e' :=
              fun hc => hE ((a.origIncToReduced_eq_iff hl _ e').mp hc)
            rw [dif_neg hE, dif_neg hne'']
            have heq : (⟨a.incReducedToOrig hl (a.origIncToReduced hl e'' hp''),
                  a.incReducedToOrig_ne hl hne''⟩ : {F // F ≠ a.incReducedToOrig hl e'})
                = ⟨e'', hE⟩ := Subtype.ext (a.incReducedToOrig_origIncToReduced hl e'' hp'')
            apply Fin.ext
            simp only [finCongr_apply, Fin.val_cast]
            exact (congrArg (fun x : {F // F ≠ a.incReducedToOrig hl e'} => (REST.1 x).val) heq).symm
      · apply Fin.ext
        simp only [finCongr_apply, Fin.val_cast]
    rw [hsub]
    exact (Matrix.rank_submatrix _ (Equiv.refl _) en).symm
  · -- case wr.1 ≠ u
    -- full incidence bijection at `wr.1` (no leaf edge is incident to `wr.1 ≠ u`)
    let fullIEq : (a.reducedArch hl).Inc wr ≃ a.Inc wr.1 :=
      { toFun := fun E => a.incReducedToOrig hl E
        invFun := fun F => a.origIncToReduced hl F (a.inc_notMem_v hl F (a.inc_ne_leaf hl hwu F))
        left_inv := fun E => a.origIncToReduced_incReducedToOrig hl E _
        right_inv := fun F => a.incReducedToOrig_origIncToReduced hl F _ }
    let iEq : {E : (a.reducedArch hl).Inc wr // E ≠ e'}
        ≃ {F : a.Inc wr.1 // F ≠ a.incReducedToOrig hl e'} :=
      fullIEq.subtypeEquiv (fun E => (fullIEq.injective.ne_iff).symm)
    let en :
        (((F : {F : a.Inc wr.1 // F ≠ a.incReducedToOrig hl e'}) → Fin (a.r F.1.1))
            × Fin (a.n wr.1))
          ≃ (((E : {E : (a.reducedArch hl).Inc wr // E ≠ e'}) → Fin ((a.reducedArch hl).r E.1.1))
            × Fin ((a.reducedArch hl).n wr)) :=
      Equiv.prodCongr
        (Equiv.piCongrLeft (fun F => Fin (a.r F.1.1)) iEq).symm
        (finCongr (a.reducedArch_n_eq_ne hl wr hwu).symm)
    have hsub : a.matE wr.1 (a.incReducedToOrig hl e') (θ wr.1)
        = ((a.reducedArch hl).matE wr e' (a.reducedParam hl θ wr)).submatrix (Equiv.refl _) en := by
      ext K REST
      simp only [Matrix.submatrix_apply, Equiv.refl_apply, matE, en, Equiv.prodCongr_apply,
        Prod.map, reducedParam, dif_neg hwu]
      refine congr_arg₂ _ ?_ ?_
      · funext e''
        rw [Equiv.piSplitAt_symm_apply, Equiv.piSplitAt_symm_apply]
        dsimp only
        by_cases hE : e'' = a.incReducedToOrig hl e'
        · rw [dif_pos hE, dif_pos ((a.origIncToReduced_eq_iff hl _ e').mpr hE)]
          apply Fin.ext
          simp only [finCongr_apply, Fin.val_cast]
          exact (val_eqRec (g := fun x : a.Inc wr.1 => a.r x.1) hE K).trans
            (val_eqRec (g := fun E : (a.reducedArch hl).Inc wr => (a.reducedArch hl).r E.1)
              ((a.origIncToReduced_eq_iff hl _ e').mpr hE) K).symm
        · have hp'' : ∀ y ∈ e''.1, y ∈ ({v}ᶜ : Set a.V) :=
            a.inc_notMem_v hl e'' (a.inc_ne_leaf hl hwu e'')
          have hne'' : a.origIncToReduced hl e'' hp'' ≠ e' :=
            fun hc => hE ((a.origIncToReduced_eq_iff hl _ e').mp hc)
          rw [dif_neg hE, dif_neg hne'']
          have heq : iEq ⟨a.origIncToReduced hl e'' hp'', hne''⟩
              = (⟨e'', hE⟩ : {F // F ≠ a.incReducedToOrig hl e'}) :=
            Subtype.ext (a.incReducedToOrig_origIncToReduced hl e'' hp'')
          apply Fin.ext
          simp only [finCongr_apply, Fin.val_cast]
          exact (congrArg (fun x : {F // F ≠ a.incReducedToOrig hl e'} => (REST.1 x).val) heq).symm
      · apply Fin.ext
        simp only [finCongr_apply, Fin.val_cast]
    rw [hsub]
    exact (Matrix.rank_submatrix _ (Equiv.refl _) en).symm

/-- **A tree with more than two vertices has a leaf away from a given leaf edge.** If `v` is a leaf
with neighbour `u` and `|V| > 2`, there is another leaf `v'` distinct from both `v` and `u` (whose
neighbour `u'` is therefore also `≠ v`). The `u`-side of the leaf cut hence always contains a leaf we
can peel, which drives the induction. Proof: handshake (`∑ deg = 2·#edges = 2(|V|−1)` on a tree) forces
`≥ 2` degree-one vertices; and `u` has degree `≥ 2` (else `{v,u}` would be the whole tree). -/
theorem exists_leaf_ne (b : Arch) {v u : b.V} (hl : b.IsLeafWith v u)
    (hcard : 2 < Fintype.card b.V) :
    ∃ v' u', b.IsLeafWith v' u' ∧ v' ≠ v ∧ v' ≠ u := by
  have hdv : b.G.degree v = 1 :=
    SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr ⟨u, hl.1, hl.2⟩
  have hdu : b.G.degree u ≠ 1 := by
    intro hdu1
    obtain ⟨w, hadjw, huniqw⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdu1
    have huv : ∀ y, b.G.Adj u y → y = v := by
      intro y hy; rw [huniqw y hy, huniqw v hl.1.symm]
    have closed : ∀ {x y : b.V}, b.G.Walk x y → (x = v ∨ x = u) → (y = v ∨ y = u) := by
      intro x y w
      induction w with
      | nil => exact id
      | cons hadj _ ih =>
        intro hx; apply ih
        rcases hx with rfl | rfl
        · exact Or.inr (hl.2 _ hadj)
        · exact Or.inl (huv _ hadj)
    have hall : ∀ x, x = v ∨ x = u := fun x => by
      obtain ⟨w⟩ := b.hT.connected.preconnected v x; exact closed w (Or.inl rfl)
    have hsub : (Finset.univ : Finset b.V) ⊆ {v, u} := fun x _ => by
      simp only [Finset.mem_insert, Finset.mem_singleton]; exact hall x
    have hle : Fintype.card b.V ≤ 2 := by
      have h := Finset.card_le_card hsub
      simp only [Finset.card_univ] at h
      exact h.trans ((Finset.card_insert_le _ _).trans (by simp))
    omega
  have hfilter : 2 ≤ (Finset.univ.filter (fun x => b.G.degree x = 1)).card := by
    have hnt : Nontrivial b.V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hpos : ∀ w, 1 ≤ b.G.degree w := fun w =>
      (b.hT.connected.preconnected.minDegree_pos_of_nontrivial).trans_le (b.G.minDegree_le_degree w)
    have hsum : ∑ w, b.G.degree w = 2 * b.G.edgeFinset.card := b.G.sum_degrees_eq_twice_card_edges
    have hedge : b.G.edgeFinset.card + 1 = Fintype.card b.V := b.hT.card_edgeFinset
    set S := Finset.univ.filter (fun x => b.G.degree x = 1) with hS
    have h1 : ∑ w ∈ S, b.G.degree w = S.card := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_congr rfl (fun w hw => (Finset.mem_filter.mp hw).2)
    have hsplit : ∑ w ∈ S, b.G.degree w + ∑ w ∈ Sᶜ, b.G.degree w = ∑ w, b.G.degree w :=
      Finset.sum_add_sum_compl S (fun w => b.G.degree w)
    have h2 : 2 * Sᶜ.card ≤ ∑ w ∈ Sᶜ, b.G.degree w := by
      have hle : ∑ _w ∈ Sᶜ, 2 ≤ ∑ w ∈ Sᶜ, b.G.degree w := by
        apply Finset.sum_le_sum
        intro w hw
        have hw1 : b.G.degree w ≠ 1 := by
          simp only [hS, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] at hw
          exact hw
        have := hpos w; omega
      simpa [Finset.sum_const, mul_comm] using hle
    have hcompl : S.card + Sᶜ.card = Fintype.card b.V := Finset.card_add_card_compl S
    omega
  have h1lt : 1 < (Finset.univ.filter (fun x => b.G.degree x = 1)).card := by omega
  obtain ⟨v', hv'mem, hv'nev⟩ := Finset.exists_mem_ne h1lt v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv'mem
  obtain ⟨u', hadj', huniq'⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv'mem
  refine ⟨v', u', ⟨hadj', huniq'⟩, hv'nev, ?_⟩
  intro hv'u; rw [hv'u] at hv'mem; exact hdu hv'mem

/-- The given leaf `v` (neighbour `u`) remains a leaf, with the same neighbour, after peeling a
*different* leaf `v'` (`v ≠ v'`, `u ≠ v'`). -/
theorem reduced_isLeafWith (b : Arch) {v u v' u' : b.V} (hl : b.IsLeafWith v u)
    (hl' : b.IsLeafWith v' u') (hvv' : v ≠ v') (huv' : u ≠ v') :
    (b.reducedArch hl').IsLeafWith
      ⟨v, by rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hvv'⟩
      ⟨u, by rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact huv'⟩ := by
  refine ⟨hl.1, ?_⟩
  intro y hy
  exact Subtype.ext (hl.2 y.1 hy)

/-- The reduced bond dimension at the surviving leaf edge equals the original. -/
theorem reduced_r_leaf (b : Arch) {v u v' u' : b.V} (hl' : b.IsLeafWith v' u')
    (hv : v ∈ ({v'}ᶜ : Set b.V)) (hu : u ∈ ({v'}ᶜ : Set b.V)) :
    (b.reducedArch hl').r s((⟨v, hv⟩ : (b.reducedArch hl').V), ⟨u, hu⟩) = b.r s(v, u) := rfl

/-- A node other than the leaf `v` is on the column side of the leaf cut. -/
theorem not_side_of_ne {v u : a.V} (hl : a.IsLeafWith v u) {w : a.V} (hw : w ≠ v) :
    ¬ a.Side hl.1 w := fun h => hw ((a.side_leaf hl w).mp h)

/-- The leaf `v` is distinct from the neighbour `u'` of any *other* leaf `v'`. -/
theorem leaf_ne_neighbor (b : Arch) {v u v' u' : b.V} (hl : b.IsLeafWith v u)
    (hl' : b.IsLeafWith v' u') (huv' : u ≠ v') : v ≠ u' :=
  fun heq => huv'.symm (hl.2 v' (heq.symm ▸ hl'.1.symm))

/-- A reduced column node (off the surviving leaf-`v` cut) has underlying vertex `≠ v`. -/
theorem foldCol_ne_v (b : Arch) {v u v' u' : b.V} (hl : b.IsLeafWith v u)
    (hl' : b.IsLeafWith v' u') (hvv' : v ≠ v') (huv' : u ≠ v')
    (xr : {xr : (b.reducedArch hl').V // ¬ (b.reducedArch hl').Side
      (b.reduced_isLeafWith hl hl' hvv' huv').1 xr}) : xr.1.1 ≠ v :=
  fun h => xr.2 (((b.reducedArch hl').side_leaf (b.reduced_isLeafWith hl hl' hvv' huv') xr.1).mpr
    (Subtype.ext h))

/-- **Column fold.** Given a leaf-`v` cut column index `col` of `b` (a value at every node `≠ v`) and
a bond value `j'` on the peeled edge `s(v',u')`, produce the leaf-`v` cut column index of the reduced
architecture `b ∖ v'`: node `u'` absorbs `j'` into its bumped external mode (via `finProdFinEquiv`),
the peeled leaf `v'` is dropped, every other node passes through. -/
noncomputable def foldCol (b : Arch) {v u v' u' : b.V}
    (hl : b.IsLeafWith v u) (hl' : b.IsLeafWith v' u') (hvv' : v ≠ v') (huv' : u ≠ v')
    (col : b.Col hl.1) (j' : Fin (b.r s(v', u'))) :
    (b.reducedArch hl').Col (b.reduced_isLeafWith hl hl' hvv' huv').1 :=
  fun xr =>
    if hy : xr.1.1 = u' then
      finCongr (b.reducedArch_n_eq_u hl' xr.1 hy).symm
        (finProdFinEquiv (col ⟨u', b.not_side_of_ne hl (b.leaf_ne_neighbor hl hl' huv').symm⟩, j'))
    else
      finCongr (b.reducedArch_n_eq_ne hl' xr.1 hy).symm
        (col ⟨xr.1.1, b.not_side_of_ne hl (b.foldCol_ne_v hl hl' hvv' huv' xr)⟩)

/-- Value of `foldCol` at the absorbing node `u'`. -/
theorem foldCol_apply_u' (b : Arch) {v u v' u' : b.V}
    (hl : b.IsLeafWith v u) (hl' : b.IsLeafWith v' u') (hvv' : v ≠ v') (huv' : u ≠ v')
    (col : b.Col hl.1) (j' : Fin (b.r s(v', u')))
    (xr : {xr : (b.reducedArch hl').V // ¬ (b.reducedArch hl').Side
      (b.reduced_isLeafWith hl hl' hvv' huv').1 xr}) (hy : xr.1.1 = u') :
    b.foldCol hl hl' hvv' huv' col j' xr = finCongr (b.reducedArch_n_eq_u hl' xr.1 hy).symm
      (finProdFinEquiv (col ⟨u', b.not_side_of_ne hl (b.leaf_ne_neighbor hl hl' huv').symm⟩, j')) := by
  simp only [foldCol, dif_pos hy]

/-- Value of `foldCol` at a node other than the absorbing node `u'`. -/
theorem foldCol_apply_ne (b : Arch) {v u v' u' : b.V}
    (hl : b.IsLeafWith v u) (hl' : b.IsLeafWith v' u') (hvv' : v ≠ v') (huv' : u ≠ v')
    (col : b.Col hl.1) (j' : Fin (b.r s(v', u')))
    (xr : {xr : (b.reducedArch hl').V // ¬ (b.reducedArch hl').Side
      (b.reduced_isLeafWith hl hl' hvv' huv').1 xr}) (hy : xr.1.1 ≠ u') :
    b.foldCol hl hl' hvv' huv' col j' xr = finCongr (b.reducedArch_n_eq_ne hl' xr.1 hy).symm
      (col ⟨xr.1.1, b.not_side_of_ne hl (b.foldCol_ne_v hl hl' hvv' huv' xr)⟩) := by
  simp only [foldCol, dif_neg hy]

/-- A column node of `b` (off the leaf-`v` cut) whose underlying vertex is `≠ v'` is a column node
of the reduced architecture `b ∖ v'`. -/
def colToReducedCol (b : Arch) {v u v' u' : b.V}
    (hl : b.IsLeafWith v u) (hl' : b.IsLeafWith v' u') (hvv' : v ≠ v') (huv' : u ≠ v')
    (w : {w : b.V // ¬ b.Side hl.1 w}) (hw : w.1 ≠ v') :
    {xr : (b.reducedArch hl').V // ¬ (b.reducedArch hl').Side
      (b.reduced_isLeafWith hl hl' hvv' huv').1 xr} :=
  ⟨⟨w.1, by rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hw⟩,
    fun h => w.2 ((b.side_leaf hl w.1).mpr (congrArg Subtype.val
      (((b.reducedArch hl').side_leaf (b.reduced_isLeafWith hl hl' hvv' huv') ⟨w.1, _⟩).mp h)))⟩

/-- **The leaf fold for `H_e`.** The surviving-leaf factor `H_{s(v,u)}` of the original network is a
`Wleaf(v')`-weighted sum over the peeled bond of the reduced network's `H_{s(v,u)}` factor. -/
theorem Hfun_fold (b : Arch) {v u v' u' : b.V}
    (hl : b.IsLeafWith v u) (hl' : b.IsLeafWith v' u') (hvv' : v ≠ v') (huv' : u ≠ v')
    (θ : b.Param) (hftr : b.FullTuckerRank θ) (col : b.Col hl.1) (k : Fin (b.r s(v, u))) :
    b.Hfun hl.1 θ col k
      = ∑ j' : Fin (b.r s(v', u')),
          b.Wleaf hl' θ (col ⟨v', b.not_side_of_ne hl hvv'.symm⟩) j'
            * (b.reducedArch hl').Hfun (b.reduced_isLeafWith hl hl' hvv' huv').1
                (b.reducedParam hl' θ) (b.foldCol hl hl' hvv' huv' col j') k := by
  classical
  set hlr := b.reduced_isLeafWith hl hl' hvv' huv' with hhlr
  have hWinj : Function.Injective (b.Wleaf hl θ).mulVec :=
    Matrix.mulVec_injective_of_rank_eq_card (b.Wleaf hl θ)
      (by rw [b.Wleaf_full_col_rank hl hftr, Fintype.card_fin])
  suffices h : (fun k => b.Hfun hl.1 θ col k)
      = (fun k => ∑ j', b.Wleaf hl' θ (col ⟨v', b.not_side_of_ne hl hvv'.symm⟩) j'
          * (b.reducedArch hl').Hfun hlr.1 (b.reducedParam hl' θ)
              (b.foldCol hl hl' hvv' huv' col j') k) by
    exact congrFun h k
  apply hWinj
  funext r₀
  set x := (b.extSplit hl.1).symm (b.rowOf hl r₀, col) with hx
  -- `x` reads back `col` on every column node.
  have hxcol : ∀ (w : b.V) (hw : ¬ b.Side hl.1 w), x w = col ⟨w, hw⟩ := by
    intro w hw; rw [hx]; exact b.extSplit_symm_col hl.1 (b.rowOf hl r₀) col ⟨w, hw⟩
  -- (F6) The reduced network's value at `pack x j'`, split by its own leaf-`v` factorisation.
  have hF6 : ∀ j', (b.reducedArch hl').represented (b.reducedParam hl' θ) (b.pack hl' x j')
      = ∑ k, b.Wleaf hl θ r₀ k
          * (b.reducedArch hl').Hfun hlr.1 (b.reducedParam hl' θ)
              (b.foldCol hl hl' hvv' huv' col j') k := by
    intro j'
    set y := b.pack hl' x j' with hy
    set rowr := ((b.reducedArch hl').extSplit hlr.1 y).1 with hrowr
    -- The column part of `pack x j'` is exactly `foldCol col j'`.
    have hcolpart : ((b.reducedArch hl').extSplit hlr.1 y).2 = b.foldCol hl hl' hvv' huv' col j' := by
      funext xr
      show y xr.1 = b.foldCol hl hl' hvv' huv' col j' xr
      rw [hy]
      by_cases hxu : xr.1.1 = u'
      · rw [b.foldCol_apply_u' hl hl' hvv' huv' col j' xr hxu, pack, dif_pos hxu,
          hxcol u' (b.not_side_of_ne hl (b.leaf_ne_neighbor hl hl' huv').symm)]
      · rw [b.foldCol_apply_ne hl hl' hvv' huv' col j' xr hxu, pack, dif_neg hxu,
          hxcol xr.1.1 (b.not_side_of_ne hl (b.foldCol_ne_v hl hl' hvv' huv' xr))]
    -- Hence `represented θr (pack x j')` is the matricization entry at `(rowr, foldCol)`.
    have h2 : (b.reducedArch hl').represented (b.reducedParam hl' θ) y
        = (b.reducedArch hl').matricize hlr.1 (b.reducedParam hl' θ) rowr
            (b.foldCol hl hl' hvv' huv' col j') := by
      rw [← hcolpart, hrowr]
      show (b.reducedArch hl').represented (b.reducedParam hl' θ) y
         = (b.reducedArch hl').represented (b.reducedParam hl' θ)
             (((b.reducedArch hl').extSplit hlr.1).symm
               (((b.reducedArch hl').extSplit hlr.1 y).1, ((b.reducedArch hl').extSplit hlr.1 y).2))
      rw [Prod.mk.eta, Equiv.symm_apply_apply]
    -- The reduced leaf factor at `rowr` reproduces the surviving leaf tensor at `r₀`.
    have hWeq : (b.reducedArch hl').Ffun hlr.1 (b.reducedParam hl' θ) rowr = b.Wleaf hl θ r₀ := by
      have hvu' : v ≠ u' := b.leaf_ne_neighbor hl hl' huv'
      have hxv0 : x v = r₀ := by
        rw [hx, b.extSplit_symm_row hl.1 (b.rowOf hl r₀) col ⟨v, (b.side_leaf hl v).mpr rfl⟩]
        apply Fin.ext; simp [rowOf]
      funext kk
      rw [(b.reducedArch hl').Ffun_leaf hlr (b.reducedParam hl' θ) rowr kk]
      simp only [reducedParam]
      rw [dif_neg hvu', Wleaf]
      refine congr_arg₂ (θ v) ?_ ?_
      · funext e''
        apply Fin.ext
        simp [leafBondIdx, finCongr]
      · have hpi : ((b.reducedArch hl').extSplit hlr.1 y).1
            = fun z : {p : (b.reducedArch hl').V // (b.reducedArch hl').Side hlr.1 p} => y z.1 := rfl
        apply Fin.ext
        simp only [hrowr, hpi]
        simp [hy, pack, dif_neg hvu', finCongr, hxv0]
    rw [h2, (b.reducedArch hl').matricize_FH hlr.1 (b.reducedParam hl' θ), Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun kk _ => ?_)
    rw [Matrix.transpose_apply, hWeq]
  -- (F1) The left side is a matricization entry, hence `represented θ x`.
  have hrv : b.rowOf hl r₀ ⟨v, (b.side_leaf hl v).mpr rfl⟩ = r₀ := by
    apply Fin.ext; simp [rowOf]
  have hLHS : (∑ k, b.Wleaf hl θ r₀ k * b.Hfun hl.1 θ col k) = b.represented θ x := by
    have h1 : b.represented θ x = b.matricize hl.1 θ (b.rowOf hl r₀) col := rfl
    rw [b.matricize_FH hl.1 θ, Matrix.mul_apply] at h1
    rw [h1]
    refine Finset.sum_congr rfl (fun kk _ => ?_)
    rw [Matrix.transpose_apply, b.Ffun_leaf hl θ (b.rowOf hl r₀) kk, hrv]
    rfl
  -- The leaf-`v'` split of `represented θ x` (reusing `represented_liftParam`).
  have hxv' : x v' = col ⟨v', b.not_side_of_ne hl hvv'.symm⟩ := by
    rw [hx]; exact b.extSplit_symm_col hl.1 (b.rowOf hl r₀) col ⟨v', b.not_side_of_ne hl hvv'.symm⟩
  have hrepfold : b.represented θ x
      = ∑ j', b.Wleaf hl' θ (col ⟨v', b.not_side_of_ne hl hvv'.symm⟩) j'
          * (b.reducedArch hl').represented (b.reducedParam hl' θ) (b.pack hl' x j') := by
    conv_lhs => rw [← b.liftParam_reducedParam hl' θ]
    rw [b.represented_liftParam hl' (fun j xv => b.Wleaf hl' θ xv j) (b.reducedParam hl' θ) x]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    rw [hxv']
  show (∑ k, b.Wleaf hl θ r₀ k * b.Hfun hl.1 θ col k)
     = ∑ k, b.Wleaf hl θ r₀ k * (∑ j', b.Wleaf hl' θ (col ⟨v', b.not_side_of_ne hl hvv'.symm⟩) j'
        * (b.reducedArch hl').Hfun hlr.1 (b.reducedParam hl' θ)
            (b.foldCol hl hl' hvv' huv' col j') k)
  rw [hLHS, hrepfold, Finset.sum_congr rfl (fun j' _ => by rw [hF6 j'])]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun kk _ => Finset.sum_congr rfl (fun j' _ => by ring))

/-- **The leaf-removal transfer (heart of the induction).** Peeling a second leaf `v'` (off the
`v`-cut, so on the `u`-side) can only *drop* the rank of the surviving leaf factor `H_{s(v,u)}`:
the original factor is a `Wleaf(v')`-fold of the reduced one, and `Wleaf(v')` has full column rank,
so its kernel is contained. Proved by `mulVec` kernel containment (cf. `reduced_rankBound`). -/
theorem Hfun_rank_reduced_le (b : Arch) {v u v' u' : b.V}
    (hl : b.IsLeafWith v u) (hl' : b.IsLeafWith v' u') (hvv' : v ≠ v') (huv' : u ≠ v')
    {θ : b.Param} (hftr : b.FullTuckerRank θ) :
    ((b.reducedArch hl').Hfun (b.reduced_isLeafWith hl hl' hvv' huv').1
        (b.reducedParam hl' θ)).rank ≤ (b.Hfun hl.1 θ).rank := by
  classical
  set hlr := b.reduced_isLeafWith hl hl' hvv' huv' with hhlr
  set θr := b.reducedParam hl' θ with hθr
  have hWinj : Function.Injective (b.Wleaf hl' θ).mulVec :=
    Matrix.mulVec_injective_of_rank_eq_card (b.Wleaf hl' θ)
      (by rw [b.Wleaf_full_col_rank hl' hftr, Fintype.card_fin])
  refine Matrix.rank_le_rank_of_ker_le (b.Hfun hl.1 θ) ((b.reducedArch hl').Hfun hlr.1 θr) ?_
  intro x hx
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  funext colr
  -- The absorbing node `u'` as a reduced column node, and the unpacking of `colr` there.
  have hu'nev' : u' ≠ v' := hl'.1.ne'
  set u'red : (b.reducedArch hl').V :=
    ⟨u', by rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hu'nev'⟩ with hu'red
  have hu'col : ¬ (b.reducedArch hl').Side hlr.1 u'red :=
    (b.reducedArch hl').not_side_of_ne hlr
      (fun h => b.leaf_ne_neighbor hl hl' huv' (congrArg Subtype.val h).symm)
  set u'coln : {xr // ¬ (b.reducedArch hl').Side hlr.1 xr} := ⟨u'red, hu'col⟩ with hu'coln
  set cj := finProdFinEquiv.symm
    (finCongr (b.reducedArch_n_eq_u hl' u'red rfl) (colr u'coln)) with hcj
  -- Reconstructed column of `b`, parameterised by the leaf-`v'` value `s`.
  set col_s : Fin (b.n v') → b.Col hl.1 := fun s w =>
    if hwu : w.1 = u' then finCongr (congrArg b.n hwu.symm) cj.1
    else if hwv : w.1 = v' then finCongr (congrArg b.n hwv.symm) s
    else finCongr (b.reducedArch_n_eq_ne hl' ⟨w.1, hwv⟩ hwu)
      (colr (b.colToReducedCol hl hl' hvv' huv' w hwv)) with hcol_s
  set s₀ : Fin (b.n v') := ⟨0, b.hn v'⟩ with hs₀
  set G : Fin (b.r s(v', u')) → ℝ := fun j' =>
    ∑ k, (b.reducedArch hl').Hfun hlr.1 θr (b.foldCol hl hl' hvv' huv' (col_s s₀) j') k * x k
    with hG
  -- (P1) `col_s s` reads back `s` at the leaf `v'`.
  have hP1 : ∀ s, col_s s ⟨v', b.not_side_of_ne hl hvv'.symm⟩ = s := by
    intro s
    simp only [hcol_s]
    split_ifs with h1
    · exact absurd h1 (fun h => hu'nev' h.symm)
    · apply Fin.ext; simp [finCongr]
  -- Column values away from `v'` do not depend on `s`.
  have hcol_indep : ∀ (s s' : Fin (b.n v')) (w : {w // ¬ b.Side hl.1 w}),
      w.1 ≠ v' → col_s s w = col_s s' w := by
    intro s s' w hwv'
    simp only [hcol_s]
    by_cases hwu : w.1 = u'
    · rw [dif_pos hwu, dif_pos hwu]
    · rw [dif_neg hwu, dif_neg hwu, dif_neg hwv', dif_neg hwv']
  -- Hence `foldCol` (which never reads the `v'` entry) is independent of `s`.
  have hfoldindep : ∀ (s : Fin (b.n v')) (j' : Fin (b.r s(v', u'))),
      b.foldCol hl hl' hvv' huv' (col_s s) j' = b.foldCol hl hl' hvv' huv' (col_s s₀) j' := by
    intro s j'
    funext xr
    by_cases hxu : xr.1.1 = u'
    · rw [b.foldCol_apply_u' hl hl' hvv' huv' (col_s s) j' xr hxu,
          b.foldCol_apply_u' hl hl' hvv' huv' (col_s s₀) j' xr hxu,
          hcol_indep s s₀ _ hu'nev']
    · rw [b.foldCol_apply_ne hl hl' hvv' huv' (col_s s) j' xr hxu,
          b.foldCol_apply_ne hl hl' hvv' huv' (col_s s₀) j' xr hxu,
          hcol_indep s s₀ _ (fun h => xr.1.2 (Set.mem_singleton_iff.mpr h))]
  -- At the bond value `cj.2`, the fold reproduces `colr`.
  have hcolr : b.foldCol hl hl' hvv' huv' (col_s s₀) cj.2 = colr := by
    funext xr
    by_cases hxu : xr.1.1 = u'
    · rw [b.foldCol_apply_u' hl hl' hvv' huv' (col_s s₀) cj.2 xr hxu]
      have hcolu' : col_s s₀ ⟨u', b.not_side_of_ne hl (b.leaf_ne_neighbor hl hl' huv').symm⟩
          = cj.1 := by
        apply Fin.ext; simp [hcol_s, finCongr]
      have hxru : xr = u'coln := Subtype.ext (Subtype.ext hxu)
      have hpack : finProdFinEquiv (cj.1, cj.2)
          = finCongr (b.reducedArch_n_eq_u hl' u'red rfl) (colr u'coln) := by
        rw [hcj, Prod.mk.eta, Equiv.apply_symm_apply]
      rw [hcolu', hpack]
      apply Fin.ext
      simp only [finCongr_apply, Fin.val_cast]
      rw [hxru]
    · rw [b.foldCol_apply_ne hl hl' hvv' huv' (col_s s₀) cj.2 xr hxu]
      have hxv' : xr.1.1 ≠ v' := fun h => xr.1.2 (Set.mem_singleton_iff.mpr h)
      simp only [hcol_s, dif_neg hxu, dif_neg hxv']
      apply Fin.ext
      simp only [finCongr_apply, Fin.val_cast]
      exact congrArg (fun z => (colr z).val) (Subtype.ext (Subtype.ext rfl))
  -- `Wleaf(v') *ᵥ G = 0` from criticality (`hx`) and the fold identity.
  have hWG : (b.Wleaf hl' θ) *ᵥ G = 0 := by
    funext s
    have hxs : (∑ k, b.Hfun hl.1 θ (col_s s) k * x k) = 0 := congrFun hx (col_s s)
    have step : ∀ k, b.Hfun hl.1 θ (col_s s) k * x k
        = ∑ j', b.Wleaf hl' θ s j'
            * ((b.reducedArch hl').Hfun hlr.1 θr
                (b.foldCol hl hl' hvv' huv' (col_s s₀) j') k * x k) := by
      intro k
      rw [b.Hfun_fold hl hl' hvv' huv' θ hftr (col_s s) k, hP1 s, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      rw [hfoldindep s j', mul_assoc]
    show (∑ j', b.Wleaf hl' θ s j' * G j') = 0
    rw [← hxs, Finset.sum_congr rfl (fun k _ => step k), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    simp only [hG]
    exact Finset.mul_sum _ _ _
  have hG0 : G = 0 := hWinj (by rw [hWG, Matrix.mulVec_zero])
  have hGcj : G cj.2 = 0 := congrFun hG0 cj.2
  simp only [hG] at hGcj
  rw [hcolr] at hGcj
  exact hGcj

/-- **Base case (`|V| = 2`).** The only `Col` node is `u`, itself a leaf, so `H_e` is the `u`-leaf
tensor `Wleaf` (reindexed), which has full column rank `r_e` by `Wleaf_full_col_rank`. -/
theorem Hfun_rank_base (b : Arch) {v u : b.V} (hl : b.IsLeafWith v u)
    (hcard2 : Fintype.card b.V = 2) {θ : b.Param} (hftr : b.FullTuckerRank θ) :
    b.r s(v, u) ≤ (b.Hfun hl.1 θ).rank := by
  classical
  have hvu : v ≠ u := hl.1.ne
  have hall : ∀ x : b.V, x = v ∨ x = u := by
    have hsub : ({v, u} : Finset b.V) = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [Finset.card_pair hvu, hcard2])
    intro x
    have hx : x ∈ ({v, u} : Finset b.V) := hsub ▸ Finset.mem_univ x
    simpa [Finset.mem_insert, Finset.mem_singleton] using hx
  have hlu : b.IsLeafWith u v := by
    refine ⟨hl.1.symm, fun y hy => ?_⟩
    rcases hall y with h | h
    · exact h
    · exact absurd (h ▸ hy) (by simp)
  have hunotv : ¬ b.Side hl.1 u := fun h => hvu ((b.side_leaf hl u).mp h).symm
  -- the `Col` index of the leaf-`v` cut is exactly `{u}`
  haveI hss : Subsingleton {x : b.V // ¬ b.Side hl.1 x} := by
    refine ⟨fun x y => Subtype.ext ?_⟩
    have hx : x.1 = u := (hall x.1).resolve_left (fun h => x.2 ((b.side_leaf hl x.1).mpr h))
    have hy : y.1 = u := (hall y.1).resolve_left (fun h => y.2 ((b.side_leaf hl y.1).mpr h))
    rw [hx, hy]
  haveI huniq : Unique {x : b.V // ¬ b.Side hl.1 x} :=
    ⟨⟨⟨u, hunotv⟩⟩, fun x => Subsingleton.elim _ _⟩
  -- there are no non-cut edges, so the column-bond index is trivial
  haveI hbcemp : IsEmpty {e : b.G.edgeSet // e ≠ b.cutEdge hl.1 ∧ ¬ b.EdgeSide hl.1 e} := by
    refine ⟨fun e => e.2.1 ?_⟩
    obtain ⟨⟨e, he⟩, _, _⟩ := e
    induction e using Sym2.ind with
    | _ p q =>
      apply Subtype.ext
      rw [SimpleGraph.mem_edgeSet] at he
      have hp : p = v ∨ p = u := hall p
      have hq : q = v ∨ q = u := hall q
      show s(p, q) = s(v, u)
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
        first
        | exact absurd rfl he.ne
        | rfl
        | rw [Sym2.eq_swap]
  haveI hbcss : Subsingleton (b.BondCol hl.1) := by unfold BondCol; infer_instance
  have hr : b.r s(v, u) = b.r s(u, v) := by rw [Sym2.eq_swap]
  have hxu : ∀ x : {x : b.V // ¬ b.Side hl.1 x}, x.1 = u := fun x =>
    (hall x.1).resolve_left (fun h => x.2 ((b.side_leaf hl x.1).mpr h))
  -- `Col hl.1 ≃ Fin (n u)` (evaluation at the unique node `u`)
  let eCol : b.Col hl.1 ≃ Fin (b.n u) :=
    { toFun := fun col => col ⟨u, hunotv⟩
      invFun := fun t x => finCongr (congrArg b.n (hxu x).symm) t
      left_inv := fun col => by
        funext x
        have hx : (⟨u, hunotv⟩ : {x : b.V // ¬ b.Side hl.1 x}) = x := Subsingleton.elim _ _
        subst hx
        apply Fin.ext; simp [finCongr]
      right_inv := fun t => by apply Fin.ext; simp [finCongr] }
  have heq : b.Hfun hl.1 θ = (b.Wleaf hlu θ).submatrix eCol (finCongr hr) := by
    ext col k
    simp only [Matrix.submatrix_apply, Hfun]
    rw [Fintype.sum_subsingleton _ (b.colDefault hl.1),
        Fintype.prod_subsingleton _ (⟨u, hunotv⟩ : {x // ¬ b.Side hl.1 x})]
    show θ u (Bond.restrict (b.bondInvFun hl.1 (k, b.sideDefault hl.1, b.colDefault hl.1)) u)
        (col ⟨u, hunotv⟩) = b.Wleaf hlu θ (eCol col) (finCongr hr k)
    have hecol : eCol col = col ⟨u, hunotv⟩ := rfl
    rw [hecol]
    simp only [Wleaf]
    congr 1
    funext e'
    have he1 : e'.1 = s(u, v) := leaf_inc_eq hlu e'
    simp only [Bond.restrict, leafBondIdx]
    have hcut : (⟨e'.1, e'.2.1⟩ : b.G.edgeSet) = b.cutEdge hl.1 := by
      apply Subtype.ext; rw [he1]; exact Sym2.eq_swap
    rw [bondInvFun, dif_pos hcut]
    apply Fin.ext
    simp only [finCongr_apply, Fin.val_cast]
    exact val_eqRec (g := fun e => b.r e.1) hcut k
  rw [heq, Matrix.rank_submatrix, b.Wleaf_full_col_rank hlu hftr]
  exact le_of_eq hr

/-- Strong-induction core of the leaf environment-rank lemma: for every architecture, at every leaf edge,
the right cut factor `H_e` has rank at least `r_e` (full column rank), by induction on `|V|` via
removal of a *second* leaf on the `u`-side of the cut. Combined with the trivial `rank ≤ r_e`
this gives the exact rank in `Hfun_full_col_rank`. -/
theorem Hfun_rank_ge_aux : ∀ (N : ℕ) (b : Arch), Fintype.card b.V = N →
    ∀ (v u : b.V) (hl : b.IsLeafWith v u) (θ : b.Param), b.FullTuckerRank θ →
      b.r s(v, u) ≤ (b.Hfun hl.1 θ).rank := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro b hcard v u hl θ hftr
    by_cases hbig : 2 < Fintype.card b.V
    · -- Inductive step: peel a second leaf `v'` on the `u`-side and transfer.
      obtain ⟨v', u', hl', hv'v, hv'u⟩ := b.exists_leaf_ne hl hbig
      have hvv' : v ≠ v' := Ne.symm hv'v
      have huv' : u ≠ v' := Ne.symm hv'u
      have hlr := b.reduced_isLeafWith hl hl' hvv' huv'
      have hcard' : Fintype.card (b.reducedArch hl').V = N - 1 := by
        show Fintype.card ↥({v'}ᶜ : Set b.V) = N - 1
        rw [Fintype.card_compl_set, hcard]; simp
      have hNlt : N - 1 < N := by omega
      have hIH := ih (N - 1) hNlt (b.reducedArch hl') hcard' _ _ hlr (b.reducedParam hl' θ)
        (b.reduced_fullRank hl' hftr)
      calc b.r s(v, u)
          = (b.reducedArch hl').r
              s((⟨v, by rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hvv'⟩ :
                  (b.reducedArch hl').V), ⟨u, by rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact huv'⟩) :=
            (b.reduced_r_leaf hl' _ _).symm
        _ ≤ ((b.reducedArch hl').Hfun hlr.1 (b.reducedParam hl' θ)).rank := hIH
        _ ≤ (b.Hfun hl.1 θ).rank := b.Hfun_rank_reduced_le hl hl' hvv' huv' hftr
    · -- Base case: `|V| = 2`, so `u` is the only `Col` node and `Hfun` is `Wleaf` at `u`.
      have h2 : 1 < Fintype.card b.V := Fintype.one_lt_card_iff_nontrivial.mpr ⟨v, u, hl.1.ne⟩
      exact b.Hfun_rank_base hl (by omega) hftr

/-- **Full cut-factorization rank, leaf case only.** Under full Tucker rank, the right
cut factor `H_e` at a **leaf** edge has full column rank `r_e`. The paper's general statement is stronger —
any edge and either factor (`F_e` or `H_e`), but the leaf-`H_e` case is all that the
leaf-removal induction consumes; the general form is not stated here. -/
theorem Hfun_full_col_rank {v u : a.V} (hl : a.IsLeafWith v u) {θ : a.Param}
    (hftr : a.FullTuckerRank θ) : (a.Hfun hl.1 θ).rank = a.r s(v, u) := by
  refine le_antisymm ?_ (Hfun_rank_ge_aux (Fintype.card a.V) a rfl v u hl θ hftr)
  calc (a.Hfun hl.1 θ).rank ≤ Fintype.card (Fin (a.r s(v, u))) := Matrix.rank_le_card_width _
    _ = a.r s(v, u) := Fintype.card_fin _


/-! ### The leaf reduction (bundles the reduction to a smaller tree)

Packages Theorem 5.2 Steps 0–2 for one leaf: gauge to orthonormal leaf, pin the column space,
build the reduced tree/target, and transfer all hypotheses. The strong induction consumes it. -/

/-- The leaf edge `s(v,u)` packaged as an incidence of the neighbour `u`. Reducible so that
`(leafIncU hl).1` unfolds to the syntactic `s(v,u)` during unification. -/
@[reducible] def leafIncU {v u : a.V} (hl : a.IsLeafWith v u) : a.Inc u :=
  ⟨s(v, u), by rw [SimpleGraph.mem_edgeSet]; exact hl.1, Sym2.mem_mk_right v u⟩

/-- The gauge action on the neighbour tensor `W_u`: contract the leaf-edge bond mode against `N`
(used with `N = M⁻¹`). -/
noncomputable def gaugeU {v u : a.V} (hl : a.IsLeafWith v u)
    (N : Matrix (Fin (a.r s(v, u))) (Fin (a.r s(v, u))) ℝ) (W : a.NodeTensor u) : a.NodeTensor u :=
  fun bi xu => ∑ m : Fin (a.r s(v, u)),
    W (Function.update bi (a.leafIncU hl) m) xu * N (bi (a.leafIncU hl)) m

/-- The gauge action on the leaf tensor `W_v`: contract the (unique) bond mode against `N` (used
with `N = M`). -/
noncomputable def gaugeV {v u : a.V} (hl : a.IsLeafWith v u)
    (N : Matrix (Fin (a.r s(v, u))) (Fin (a.r s(v, u))) ℝ) (W : a.NodeTensor v) : a.NodeTensor v :=
  fun bi xv => ∑ l : Fin (a.r s(v, u)), W (a.leafBondIdx hl l) xv * N l (bi (a.leafInc hl))

/-- The **leaf gauge** of a parameter point: apply `gaugeV M` at the leaf `v`, `gaugeU M⁻¹` at the
neighbour `u`, and leave every other node unchanged (mirrors the `dite w = v / w = u / else`
shape of `liftParam`). -/
noncomputable def gaugeLeaf {v u : a.V} (hl : a.IsLeafWith v u)
    (M : Matrix (Fin (a.r s(v, u))) (Fin (a.r s(v, u))) ℝ) (θ : a.Param) : a.Param :=
  fun w bi xw =>
    if hwv : w = v then
      a.gaugeV hl M (θ v) (hwv ▸ bi) (finCongr (congrArg a.n hwv) xw)
    else if hwu : w = u then
      a.gaugeU hl M⁻¹ (θ u) (hwu ▸ bi) (finCongr (congrArg a.n hwu) xw)
    else θ w bi xw

/-- `gaugeLeaf` at the leaf node is `gaugeV M`. -/
theorem gaugeLeaf_v {v u : a.V} (hl : a.IsLeafWith v u)
    (M : Matrix (Fin (a.r s(v, u))) (Fin (a.r s(v, u))) ℝ) (θ : a.Param) :
    a.gaugeLeaf hl M θ v = a.gaugeV hl M (θ v) := by
  funext bi xv
  simp only [gaugeLeaf, dif_pos, finCongr_refl, Equiv.refl_apply]

/-- `gaugeLeaf` at the neighbour node is `gaugeU M⁻¹`. -/
theorem gaugeLeaf_u {v u : a.V} (hl : a.IsLeafWith v u)
    (M : Matrix (Fin (a.r s(v, u))) (Fin (a.r s(v, u))) ℝ) (θ : a.Param) :
    a.gaugeLeaf hl M θ u = a.gaugeU hl M⁻¹ (θ u) := by
  funext bi xu
  have huv : u ≠ v := a.reduced_uNeV hl
  simp only [gaugeLeaf, dif_neg huv, dif_pos, finCongr_refl, Equiv.refl_apply]

/-- `gaugeLeaf` leaves every non-`{v,u}` node unchanged. -/
theorem gaugeLeaf_other {v u : a.V} (hl : a.IsLeafWith v u)
    (M : Matrix (Fin (a.r s(v, u))) (Fin (a.r s(v, u))) ℝ) (θ : a.Param)
    {w : a.V} (hwv : w ≠ v) (hwu : w ≠ u) : a.gaugeLeaf hl M θ w = θ w := by
  funext bi xw
  simp only [gaugeLeaf, dif_neg hwv, dif_neg hwu]

/-- The leaf bond multi-index evaluated at the leaf incidence is the identity. -/
theorem leafBondIdx_leafInc {v u : a.V} (hl : a.IsLeafWith v u) (l : Fin (a.r s(v, u))) :
    a.leafBondIdx hl l (a.leafInc hl) = l := by
  apply Fin.ext
  simp only [leafBondIdx, finCongr_apply, Fin.val_cast]

/-- Every leaf bond multi-index is `leafBondIdx` of its leaf value (as `Inc v` is a subsingleton). -/
theorem leafBondIdx_self {v u : a.V} (hl : a.IsLeafWith v u) (bi : a.BondIdx v) :
    a.leafBondIdx hl (bi (a.leafInc hl)) = bi := by
  haveI hss : Subsingleton (a.Inc v) :=
    ⟨fun e1 e2 => Subtype.ext ((leaf_inc_eq hl e1).trans (leaf_inc_eq hl e2).symm)⟩
  funext e'
  rw [Subsingleton.elim e' (a.leafInc hl), leafBondIdx_leafInc]

/-- Two applications of `gaugeU` compose the matrices: `gaugeU N₂ ∘ gaugeU N₁ = id` when
`N₂ * N₁ = 1`. -/
theorem gaugeU_gaugeU {v u : a.V} (hl : a.IsLeafWith v u)
    {N₁ N₂ : Matrix (Fin (a.r s(v, u))) (Fin (a.r s(v, u))) ℝ} (h : N₂ * N₁ = 1)
    (W : a.NodeTensor u) : a.gaugeU hl N₂ (a.gaugeU hl N₁ W) = W := by
  funext bi xu
  simp only [gaugeU, Function.update_self, Function.update_idem, Finset.sum_mul]
  rw [Finset.sum_comm]
  have key : ∀ p : Fin (a.r s(v, u)),
      (∑ m, W (Function.update bi (a.leafIncU hl) p) xu * N₁ m p
        * N₂ (bi (a.leafIncU hl)) m)
      = W (Function.update bi (a.leafIncU hl) p) xu * (N₂ * N₁) (bi (a.leafIncU hl)) p := by
    intro p
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  rw [Finset.sum_congr rfl (fun p _ => key p), h]
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_ite_eq, Function.update_eq_self]

/-- Two applications of `gaugeV` compose the matrices: `gaugeV N₂ ∘ gaugeV N₁ = id` when
`N₁ * N₂ = 1`. -/
theorem gaugeV_gaugeV {v u : a.V} (hl : a.IsLeafWith v u)
    {N₁ N₂ : Matrix (Fin (a.r s(v, u))) (Fin (a.r s(v, u))) ℝ} (h : N₁ * N₂ = 1)
    (W : a.NodeTensor v) : a.gaugeV hl N₂ (a.gaugeV hl N₁ W) = W := by
  funext bi xv
  simp only [gaugeV, leafBondIdx_leafInc, Finset.sum_mul]
  rw [Finset.sum_comm]
  have key : ∀ p : Fin (a.r s(v, u)),
      (∑ l, W (a.leafBondIdx hl p) xv * N₁ p l * N₂ l (bi (a.leafInc hl)))
      = W (a.leafBondIdx hl p) xv * (N₁ * N₂) p (bi (a.leafInc hl)) := by
    intro p
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [Finset.sum_congr rfl (fun p _ => key p), h]
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_ite_eq', leafBondIdx_self]

/-- Updating the split coordinate of `piSplitAt.symm` just changes the first component. -/
theorem piSplitAt_symm_update_self {ι : Type*} [DecidableEq ι] {β : ι → Type*} (i : ι)
    (k m : β i) (rc : (j : {j // j ≠ i}) → β j) :
    Function.update ((Equiv.piSplitAt i β).symm (k, rc)) i m
      = (Equiv.piSplitAt i β).symm (m, rc) := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, Equiv.piSplitAt_symm_apply, dif_pos rfl]
  · rw [Function.update_of_ne hj, Equiv.piSplitAt_symm_apply, Equiv.piSplitAt_symm_apply,
      dif_neg hj, dif_neg hj]

/-- Updating a non-split coordinate of `piSplitAt.symm` updates the second component there. -/
theorem piSplitAt_symm_update_ne {ι : Type*} [DecidableEq ι] {β : ι → Type*} {i i' : ι}
    (hii' : i' ≠ i) (k : β i) (m : β i') (rc : (j : {j // j ≠ i}) → β j) :
    Function.update ((Equiv.piSplitAt i β).symm (k, rc)) i' m
      = (Equiv.piSplitAt i β).symm (k, Function.update rc ⟨i', hii'⟩ m) := by
  funext j
  rcases eq_or_ne j i' with hji' | hji'
  · subst hji'
    rw [Function.update_self, Equiv.piSplitAt_symm_apply, dif_neg hii']
    show m = Function.update rc ⟨j, hii'⟩ m ⟨j, hii'⟩
    rw [Function.update_self]
  · rw [Function.update_of_ne hji']
    rcases eq_or_ne j i with hj | hj
    · subst hj
      rw [Equiv.piSplitAt_symm_apply, Equiv.piSplitAt_symm_apply, dif_pos rfl, dif_pos rfl]
    · rw [Equiv.piSplitAt_symm_apply, Equiv.piSplitAt_symm_apply, dif_neg hj, dif_neg hj]
      show rc ⟨j, hj⟩ = Function.update rc ⟨i', hii'⟩ m ⟨j, hj⟩
      rw [Function.update_of_ne (fun hc => hji' (congrArg Subtype.val hc))]

/-- `piSplitAt.symm` evaluated at the split coordinate returns the first component. -/
theorem piSplitAt_symm_apply_self {ι : Type*} [DecidableEq ι] {β : ι → Type*} (i : ι) (k : β i)
    (rc : (j : {j // j ≠ i}) → β j) : (Equiv.piSplitAt i β).symm (k, rc) i = k := by
  simp [Equiv.piSplitAt_symm_apply]

/-- **Fact 4.** The gauged leaf tensor is `W_v · M`. -/
theorem Wleaf_gaugeLeaf {v u : a.V} (hl : a.IsLeafWith v u)
    (M : Matrix (Fin (a.r s(v, u))) (Fin (a.r s(v, u))) ℝ) (θ : a.Param) :
    a.Wleaf hl (a.gaugeLeaf hl M θ) = a.Wleaf hl θ * M := by
  ext xv k
  rw [Matrix.mul_apply]
  show a.gaugeLeaf hl M θ v (a.leafBondIdx hl k) xv = ∑ l, a.Wleaf hl θ xv l * M l k
  rw [a.gaugeLeaf_v]
  simp only [gaugeV, leafBondIdx_leafInc, Wleaf]

/-- **Rank monotonicity for the `u`-gauge.** Contracting the leaf-edge mode of `W_u` against any
matrix `N` cannot increase the rank of any mode-`e` unfolding. (When `e` is the leaf edge this is a
left multiplication by `N`; otherwise a right multiplication by a reindexing matrix.) -/
theorem gaugeU_matE_rank_le {v u : a.V} (hl : a.IsLeafWith v u)
    (N : Matrix (Fin (a.r s(v, u))) (Fin (a.r s(v, u))) ℝ) (W : a.NodeTensor u) (e : a.Inc u) :
    (a.matE u e (a.gaugeU hl N W)).rank ≤ (a.matE u e W).rank := by
  by_cases he : e = a.leafIncU hl
  · subst he
    have hleaf : a.matE u (a.leafIncU hl) (a.gaugeU hl N W)
        = N * a.matE u (a.leafIncU hl) W := by
      ext k rest
      rw [Matrix.mul_apply]
      simp only [matE, gaugeU]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [piSplitAt_symm_update_self, piSplitAt_symm_apply_self, mul_comm]
    rw [hleaf]
    exact Matrix.rank_mul_le_right _ _
  · have hne' : a.leafIncU hl ≠ e := fun h => he h.symm
    have hid : ∃ Q : Matrix
        (((e' : {e' : a.Inc u // e' ≠ e}) → Fin (a.r e'.1.1)) × Fin (a.n u))
        (((e' : {e' : a.Inc u // e' ≠ e}) → Fin (a.r e'.1.1)) × Fin (a.n u)) ℝ,
        a.matE u e (a.gaugeU hl N W) = a.matE u e W * Q := by
      refine ⟨fun col' col => ∑ mm : Fin (a.r s(v, u)),
        if col' = (Function.update col.1 ⟨a.leafIncU hl, hne'⟩ mm, col.2)
        then N (col.1 ⟨a.leafIncU hl, hne'⟩) mm else 0, ?_⟩
      ext k col
      rw [Matrix.mul_apply]
      simp only [matE, gaugeU, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      simp only [mul_ite, mul_zero]
      rw [Fintype.sum_ite_eq', piSplitAt_symm_update_ne hne', Equiv.piSplitAt_symm_apply,
        dif_neg hne']
    obtain ⟨Q, hQ⟩ := hid
    rw [hQ]
    exact Matrix.rank_mul_le_left _ _

/-- **Fact 2.** The gauge preserves full Tucker rank. At the leaf `v` the unfolding is `W_v·M`
(invertible right factor); at the neighbour `u` the leaf-edge gauge is rank-preserving
(`gaugeU_matE_rank_le` both ways); every other node is unchanged. -/
theorem gaugeLeaf_fullRank {v u : a.V} (hl : a.IsLeafWith v u)
    {M : Matrix (Fin (a.r s(v, u))) (Fin (a.r s(v, u))) ℝ} (hMdet : IsUnit M.det)
    {θ : a.Param} (hftr : a.FullTuckerRank θ) : a.FullTuckerRank (a.gaugeLeaf hl M θ) := by
  intro w e
  by_cases hwv : w = v
  · subst hwv
    haveI hss : Subsingleton (a.Inc w) :=
      ⟨fun e1 e2 => Subtype.ext ((leaf_inc_eq hl e1).trans (leaf_inc_eq hl e2).symm)⟩
    obtain rfl : e = a.leafInc hl := Subsingleton.elim _ _
    rw [a.matE_leafInc_rank hl (a.gaugeLeaf hl M θ), a.Wleaf_gaugeLeaf hl M θ,
      Matrix.rank_mul_eq_left_of_isUnit_det _ _ hMdet]
    exact a.Wleaf_full_col_rank hl hftr
  · by_cases hwu : w = u
    · subst hwu
      rw [a.gaugeLeaf_u hl M θ]
      have h1 : (a.matE w e (a.gaugeU hl M⁻¹ (θ w))).rank ≤ (a.matE w e (θ w)).rank :=
        a.gaugeU_matE_rank_le hl M⁻¹ (θ w) e
      have hgg : a.gaugeU hl M (a.gaugeU hl M⁻¹ (θ w)) = θ w :=
        a.gaugeU_gaugeU hl (Matrix.mul_nonsing_inv M hMdet) (θ w)
      have h2 : (a.matE w e (θ w)).rank ≤ (a.matE w e (a.gaugeU hl M⁻¹ (θ w))).rank :=
        calc (a.matE w e (θ w)).rank
            = (a.matE w e (a.gaugeU hl M (a.gaugeU hl M⁻¹ (θ w)))).rank := by rw [hgg]
          _ ≤ (a.matE w e (a.gaugeU hl M⁻¹ (θ w))).rank :=
              a.gaugeU_matE_rank_le hl M (a.gaugeU hl M⁻¹ (θ w)) e
      rw [le_antisymm h1 h2]
      exact hftr w e
    · rw [a.gaugeLeaf_other hl M θ hwv hwu]
      exact hftr w e

/-- **Matrix collapse across the shared bond.** With `M · M⁻¹ = 1`, contracting the `M`-image of one
factor against the `M⁻ᵀ`-image of the other recovers the plain pairing:
`∑ₖ (∑ₗ Aₗ Mₗₖ)(∑ₘ hₘ M⁻¹ₖₘ) = ∑ₖ Aₖ hₖ`. -/
theorem gauge_collapse {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M * M⁻¹ = 1)
    (A h : Fin n → ℝ) :
    (∑ k, (∑ l, A l * M l k) * (∑ m, h m * M⁻¹ k m)) = ∑ k, A k * h k := by
  have hR : ∀ k, (∑ m, h m * M⁻¹ k m) = (M⁻¹ *ᵥ h) k := by
    intro k
    show (∑ m, h m * M⁻¹ k m) = ∑ j, M⁻¹ k j * h j
    exact Finset.sum_congr rfl (fun m _ => mul_comm _ _)
  have hL : ∀ k, (∑ l, A l * M l k) = (A ᵥ* M) k := fun _ => rfl
  simp only [hL, hR]
  show (A ᵥ* M) ⬝ᵥ (M⁻¹ *ᵥ h) = ∑ k, A k * h k
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hM, Matrix.vecMul_one]
  rfl

/-- **Fact 1.** The leaf gauge preserves the represented tensor. Isolating the leaf-bond coordinate
in the global bond sum, the leaf factor `∑ₗ θ_v(l)·M(l,k)` pairs with the neighbour factor
`∑ₘ θ_u(…m…)·M⁻¹(k,m)`, and summing over the leaf bond `k` collapses via `M·M⁻¹ = 1`. -/
theorem gaugeLeaf_represented {v u : a.V} (hl : a.IsLeafWith v u)
    {M : Matrix (Fin (a.r s(v, u))) (Fin (a.r s(v, u))) ℝ} (hMdet : IsUnit M.det) (θ : a.Param) :
    a.represented (a.gaugeLeaf hl M θ) = a.represented θ := by
  classical
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMdet
  have huv : u ≠ v := a.reduced_uNeV hl
  have hr0 : 0 < a.r s(v, u) := a.hr s(v, u) (by rw [SimpleGraph.mem_edgeSet]; exact hl.1)
  funext x
  set e₀ : a.G.edgeSet := ⟨s(v, u), by rw [SimpleGraph.mem_edgeSet]; exact hl.1⟩ with he₀def
  set E : (Fin (a.r ↑e₀) × ((j : {j : a.G.edgeSet // j ≠ e₀}) → Fin (a.r ↑↑j))) ≃ a.Bond :=
    (Equiv.piSplitAt e₀ (fun e => Fin (a.r e.1))).symm with hEdef
  -- leaf-bond values of a split assignment
  have hlv : ∀ (k : Fin (a.r s(v, u))) rest, Bond.restrict (E (k, rest)) v (a.leafInc hl) = k := by
    intro k rest; exact piSplitAt_symm_apply_self (β := fun e => Fin (a.r e.1)) e₀ k rest
  have hlu : ∀ (k : Fin (a.r s(v, u))) rest, Bond.restrict (E (k, rest)) u (a.leafIncU hl) = k := by
    intro k rest; exact piSplitAt_symm_apply_self (β := fun e => Fin (a.r e.1)) e₀ k rest
  have F1a : ∀ (k : Fin (a.r s(v, u))) rest, Bond.restrict (E (k, rest)) v = a.leafBondIdx hl k := by
    intro k rest
    rw [← leafBondIdx_self hl (Bond.restrict (E (k, rest)) v), hlv k rest]
  -- value at a non-leaf edge is `rest`, independent of the leaf bond value
  have hEval_ne : ∀ (k : Fin (a.r s(v, u))) rest (j : a.G.edgeSet) (hj : j ≠ e₀),
      E (k, rest) j = rest ⟨j, hj⟩ := by
    intro k rest j hj
    show (Equiv.piSplitAt e₀ (fun e => Fin (a.r e.1))).symm (k, rest) j = rest ⟨j, hj⟩
    rw [Equiv.piSplitAt_symm_apply, dif_neg hj]
  have hbu : ∀ (k m : Fin (a.r s(v, u))) rest,
      Function.update (Bond.restrict (E (k, rest)) u) (a.leafIncU hl) m
        = Bond.restrict (E (m, rest)) u := by
    intro k m rest
    funext e'
    by_cases he' : e' = a.leafIncU hl
    · subst he'; rw [Function.update_self, hlu m rest]
    · rw [Function.update_of_ne he']
      have hEne : (⟨e'.1, e'.2.1⟩ : a.G.edgeSet) ≠ e₀ := by
        intro hc
        have hsv : e'.1 = s(v, u) := congrArg Subtype.val hc
        exact he' (Subtype.ext hsv)
      show E (k, rest) ⟨e'.1, e'.2.1⟩ = E (m, rest) ⟨e'.1, e'.2.1⟩
      rw [hEval_ne k rest ⟨e'.1, e'.2.1⟩ hEne, hEval_ne m rest ⟨e'.1, e'.2.1⟩ hEne]
  have hPindep : ∀ (k m : Fin (a.r s(v, u))) rest (w : a.V), w ≠ v → w ≠ u →
      Bond.restrict (E (k, rest)) w = Bond.restrict (E (m, rest)) w := by
    intro k m rest w hwv hwu
    funext e'
    have hEne : (⟨e'.1, e'.2.1⟩ : a.G.edgeSet) ≠ e₀ := by
      intro hc
      have hsv : e'.1 = s(v, u) := congrArg Subtype.val hc
      have hw : w ∈ e'.1 := e'.2.2
      rw [hsv, Sym2.mem_iff] at hw
      rcases hw with h | h
      · exact hwv h
      · exact hwu h
    show E (k, rest) ⟨e'.1, e'.2.1⟩ = E (m, rest) ⟨e'.1, e'.2.1⟩
    rw [hEval_ne k rest ⟨e'.1, e'.2.1⟩ hEne, hEval_ne m rest ⟨e'.1, e'.2.1⟩ hEne]
  have hprod3 : ∀ (f : a.V → ℝ),
      ∏ w, f w = f v * (f u * ∏ w ∈ (({v}ᶜ : Finset a.V).erase u), f w) := by
    intro f
    rw [Fintype.prod_eq_mul_prod_compl v f]
    congr 1
    have huc : u ∈ ({v}ᶜ : Finset a.V) := by
      simp only [Finset.mem_compl, Finset.mem_singleton]; exact huv
    rw [← Finset.mul_prod_erase _ f huc]
  -- reindex both bond sums across the leaf edge, then collapse per remaining assignment
  simp only [represented]
  conv_lhs => rw [← Equiv.sum_comp E (fun b => ∏ w, a.gaugeLeaf hl M θ w (Bond.restrict b w) (x w))]
  conv_rhs => rw [← Equiv.sum_comp E (fun b => ∏ w, θ w (Bond.restrict b w) (x w))]
  simp only [Fintype.sum_prod_type]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun rest _ => ?_)
  set PP := ∏ w ∈ (({v}ᶜ : Finset a.V).erase u),
      θ w (Bond.restrict (E ((⟨0, hr0⟩ : Fin (a.r s(v, u))), rest)) w) (x w) with hPPdef
  have hP : ∀ k : Fin (a.r s(v, u)),
      (∏ w ∈ (({v}ᶜ : Finset a.V).erase u), θ w (Bond.restrict (E (k, rest)) w) (x w)) = PP := by
    intro k
    rw [hPPdef]
    refine Finset.prod_congr rfl (fun w hw => ?_)
    obtain ⟨hwu, hwc⟩ := Finset.mem_erase.mp hw
    have hwv : w ≠ v := fun h => (Finset.mem_compl.mp hwc) (Finset.mem_singleton.mpr h)
    rw [hPindep k ⟨0, hr0⟩ rest w hwv hwu]
  have hGval : ∀ k : Fin (a.r s(v, u)),
      (∏ w, a.gaugeLeaf hl M θ w (Bond.restrict (E (k, rest)) w) (x w))
      = (∑ l, θ v (a.leafBondIdx hl l) (x v) * M l k)
        * (∑ m, (θ u (Bond.restrict (E (m, rest)) u) (x u) * PP) * M⁻¹ k m) := by
    intro k
    rw [hprod3 (fun w => a.gaugeLeaf hl M θ w (Bond.restrict (E (k, rest)) w) (x w))]
    congr 1
    · rw [a.gaugeLeaf_v, F1a k rest]
      simp only [gaugeV, leafBondIdx_leafInc]
    · rw [a.gaugeLeaf_u,
        show (∏ w ∈ (({v}ᶜ : Finset a.V).erase u),
            a.gaugeLeaf hl M θ w (Bond.restrict (E (k, rest)) w) (x w)) = PP from ?_]
      · simp only [gaugeU]
        rw [hlu k rest, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [hbu k m rest]; ring
      · rw [← hP k]
        refine Finset.prod_congr rfl (fun w hw => ?_)
        obtain ⟨hwu, hwc⟩ := Finset.mem_erase.mp hw
        have hwv : w ≠ v := fun h => (Finset.mem_compl.mp hwc) (Finset.mem_singleton.mpr h)
        rw [a.gaugeLeaf_other hl M θ hwv hwu]
  have hTval : ∀ k : Fin (a.r s(v, u)),
      (∏ w, θ w (Bond.restrict (E (k, rest)) w) (x w))
      = θ v (a.leafBondIdx hl k) (x v) * (θ u (Bond.restrict (E (k, rest)) u) (x u) * PP) := by
    intro k
    rw [hprod3 (fun w => θ w (Bond.restrict (E (k, rest)) w) (x w))]
    congr 1
    · rw [F1a k rest]
    · rw [hP k]
  rw [Finset.sum_congr rfl (fun k _ => hGval k),
      gauge_collapse hMM (fun l => θ v (a.leafBondIdx hl l) (x v))
        (fun m => θ u (Bond.restrict (E (m, rest)) u) (x u) * PP)]
  exact (Finset.sum_congr rfl (fun k _ => hTval k)).symm

/-- The gauge at a node `w' ≠ w` ignores an update of `θ` at `w` (the gauge value at `w'` depends on
`θ` only at the node `v`/`u`/`w'` selected by `w'`, all `≠ w`). -/
theorem gaugeLeaf_update_ne {v u : a.V} (hl : a.IsLeafWith v u)
    (M : Matrix (Fin (a.r s(v, u))) (Fin (a.r s(v, u))) ℝ) (ρ : a.Param) (w : a.V)
    (η : a.NodeTensor w) {w' : a.V} (hw' : w' ≠ w) :
    a.gaugeLeaf hl M (Function.update ρ w η) w' = a.gaugeLeaf hl M ρ w' := by
  funext bi xw'
  by_cases h1 : w' = v
  · have hvw : v ≠ w := h1 ▸ hw'
    simp only [gaugeLeaf, dif_pos h1, Function.update_of_ne hvw]
  · by_cases h2 : w' = u
    · have huw : u ≠ w := h2 ▸ hw'
      simp only [gaugeLeaf, dif_neg h1, dif_pos h2, Function.update_of_ne huw]
    · simp only [gaugeLeaf, dif_neg h1, dif_neg h2, Function.update_of_ne hw']

/-- **Fact 3.** The gauge preserves criticality. The residual is unchanged (Fact 1), and each
perturbation `η` at a node `w` of the gauged point is the gauge image of a perturbation `η''` of
`θ` (`update (gaugeLeaf M θ) w η = gaugeLeaf M (update θ w η'')`, the per-node gauge being an
invertible linear map), so the variation reduces to `hcrit w η''`. -/
theorem gaugeLeaf_critical {v u : a.V} (hl : a.IsLeafWith v u)
    {M : Matrix (Fin (a.r s(v, u))) (Fin (a.r s(v, u))) ℝ} (hMdet : IsUnit M.det)
    {Tstar : a.Ext → ℝ} {θ : a.Param} (hcrit : a.Critical Tstar θ) :
    a.Critical Tstar (a.gaugeLeaf hl M θ) := by
  have hMMr : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hMdet
  have hres : ∀ x, a.residual Tstar (a.gaugeLeaf hl M θ) x = a.residual Tstar θ x :=
    fun x => by simp only [residual, a.gaugeLeaf_represented hl hMdet θ]
  have crit_step : ∀ (w : a.V) (η : a.NodeTensor w) (η'' : a.NodeTensor w),
      Function.update (a.gaugeLeaf hl M θ) w η = a.gaugeLeaf hl M (Function.update θ w η'') →
      ∑ x, a.residual Tstar (a.gaugeLeaf hl M θ) x
        * a.represented (Function.update (a.gaugeLeaf hl M θ) w η) x = 0 := by
    intro w η η'' hcomm
    have key : ∀ x, a.residual Tstar (a.gaugeLeaf hl M θ) x
        * a.represented (Function.update (a.gaugeLeaf hl M θ) w η) x
        = a.residual Tstar θ x * a.represented (Function.update θ w η'') x := by
      intro x
      rw [hres x, hcomm, a.gaugeLeaf_represented hl hMdet (Function.update θ w η'')]
    rw [Finset.sum_congr rfl (fun x _ => key x)]
    exact hcrit w η''
  intro w η
  by_cases hwv : w = v
  · subst hwv
    refine crit_step w η (a.gaugeV hl M⁻¹ η) ?_
    funext w'
    by_cases hw' : w' = w
    · subst hw'
      rw [Function.update_self, a.gaugeLeaf_v, Function.update_self, a.gaugeV_gaugeV hl hMMr η]
    · rw [Function.update_of_ne hw', a.gaugeLeaf_update_ne hl M θ w _ hw']
  · by_cases hwu : w = u
    · subst hwu
      refine crit_step w η (a.gaugeU hl M η) ?_
      funext w'
      by_cases hw' : w' = w
      · subst hw'
        rw [Function.update_self, a.gaugeLeaf_u, Function.update_self, a.gaugeU_gaugeU hl hMMr η]
      · rw [Function.update_of_ne hw', a.gaugeLeaf_update_ne hl M θ w _ hw']
    · refine crit_step w η η ?_
      funext w'
      by_cases hw' : w' = w
      · subst hw'
        rw [Function.update_self, a.gaugeLeaf_other hl M (Function.update θ w' η) hwv hwu,
          Function.update_self]
      · rw [Function.update_of_ne hw', a.gaugeLeaf_update_ne hl M θ w _ hw']

/-- **Gauge to an orthonormal leaf** (Theorem 5.2, Step 0). Using the QR/orthonormalization factor,
replace `θ` by a `T`-equivalent, still-critical, still-full-rank point whose leaf tensor `W_v` has
orthonormal columns (`W_vᵀ W_v = 1`). -/
theorem exists_gauge {v u : a.V} (hl : a.IsLeafWith v u) {Tstar : a.Ext → ℝ}
    {θ : a.Param} (hcrit : a.Critical Tstar θ) (hftr : a.FullTuckerRank θ) :
    ∃ θ' : a.Param, a.represented θ' = a.represented θ ∧ a.Critical Tstar θ' ∧
      a.FullTuckerRank θ' ∧ (a.Wleaf hl θ')ᵀ * a.Wleaf hl θ' = 1 := by
  obtain ⟨M, hMdet, hMorth⟩ := exists_orthonormalize (a.Wleaf hl θ) (a.Wleaf_full_col_rank hl hftr)
  exact ⟨a.gaugeLeaf hl M θ, a.gaugeLeaf_represented hl hMdet θ,
    a.gaugeLeaf_critical hl hMdet hcrit, a.gaugeLeaf_fullRank hl hMdet hftr,
    by rw [a.Wleaf_gaugeLeaf hl M θ]; exact hMorth⟩


noncomputable def rowLeafEquiv {v u : a.V} (hl : a.IsLeafWith v u) : a.Row hl.1 ≃ Fin (a.n v) where
  toFun row := row ⟨v, (a.side_leaf hl v).mpr rfl⟩
  invFun := a.rowOf hl
  left_inv := a.rowOf_v_value hl
  right_inv xv := by
    apply Fin.ext
    simp only [rowOf, finCongr_apply, Fin.val_cast]

/-- **Leaf column-space pinning** (Theorem 5.2, Step 1). At an orthonormal-leaf full-rank critical
point of a realizable target, the target's leaf matricization factors through the leaf tensor:
`T*⁽ᵉ⁾ = Ffun · Bᵀ`, minimally, so `reduced_rankBound` applies. -/
theorem leaf_target_factor {v u : a.V} (hl : a.IsLeafWith v u) {Tstar : a.Ext → ℝ}
    (hb : a.RankBound Tstar) {θ : a.Param} (hcrit : a.Critical Tstar θ) (hftr : a.FullTuckerRank θ)
    (horth : (a.Wleaf hl θ)ᵀ * a.Wleaf hl θ = 1) :
    ∃ B : Matrix (a.Col hl.1) (Fin (a.r s(v, u))) ℝ,
      a.matricizeOf hl.1 Tstar = a.Ffun hl.1 θ * Bᵀ ∧
      (∀ (l : Fin (a.r s(v, u))), (a.matricizeOf hl.1 Tstar).rank ≤ (l : ℕ) → ∀ j, B j l = 0) ∧
      (∀ (g : Fin (a.r s(v, u)) → ℝ),
        (∀ (l : Fin (a.r s(v, u))), (a.matricizeOf hl.1 Tstar).rank ≤ (l : ℕ) → g l = 0) →
        (∑ l, g l • (fun i => a.Ffun hl.1 θ i l)) = 0 → g = 0) := by
  classical
  -- `(P * Q) i j = (P *ᵥ Q.col j) i`, definitionally.
  have colmul : ∀ (P : Matrix (a.Row hl.1) (a.Row hl.1) ℝ)
      (Q : Matrix (a.Row hl.1) (a.Col hl.1) ℝ) (i : a.Row hl.1) (j : a.Col hl.1),
      (P * Q) i j = (P *ᵥ Q.col j) i := fun _ _ _ _ => rfl
  -- Step 1a: `F = W_v` reindexed by the leaf-row bijection.
  have hFsub : a.Ffun hl.1 θ = (a.Wleaf hl θ).submatrix (a.rowLeafEquiv hl) (Equiv.refl _) := by
    ext row k
    rw [Matrix.submatrix_apply, Equiv.refl_apply, a.Ffun_leaf hl θ row k]
    rfl
  -- Step 1b: `F` has full column rank `ρ`.
  have hFrank : (a.Ffun hl.1 θ).rank = a.r s(v, u) := by
    rw [hFsub, Matrix.rank_submatrix]; exact a.Wleaf_full_col_rank hl hftr
  -- Step 1c: `F` has orthonormal columns.
  have hFtF : (a.Ffun hl.1 θ)ᵀ * a.Ffun hl.1 θ = 1 := by
    rw [hFsub, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, horth]; simp
  -- Step 2: `G := Hᵀ H` is invertible.
  have hHrank : (a.Hfun hl.1 θ).rank = a.r s(v, u) := a.Hfun_full_col_rank hl hftr
  have hGrank : ((a.Hfun hl.1 θ)ᵀ * a.Hfun hl.1 θ).rank = a.r s(v, u) := by
    rw [Matrix.rank_transpose_mul_self]; exact hHrank
  have hGunit : IsUnit ((a.Hfun hl.1 θ)ᵀ * a.Hfun hl.1 θ) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit, linearIndependent_iff_card_eq_finrank_span,
      Fintype.card_fin]
    rw [Matrix.rank_eq_finrank_span_cols] at hGrank
    exact hGrank.symm
  have hGdet : IsUnit ((a.Hfun hl.1 θ)ᵀ * a.Hfun hl.1 θ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hGunit
  -- Step 3: criticality ⇒ `T H = F (Hᵀ H)`.
  have hcl := a.crit_leaf hl hcrit
  have hres : a.matricizeOf hl.1 (a.residual Tstar θ)
      = a.matricize hl.1 θ - a.matricizeOf hl.1 Tstar := by
    ext row col
    simp only [matricizeOf, matricize, residual, Matrix.sub_apply]
  have hcl' : (a.matricize hl.1 θ - a.matricizeOf hl.1 Tstar) * a.Hfun hl.1 θ = 0 := by
    rw [← hres]; exact hcl
  have hTH : a.matricizeOf hl.1 Tstar * a.Hfun hl.1 θ
      = a.Ffun hl.1 θ * ((a.Hfun hl.1 θ)ᵀ * a.Hfun hl.1 θ) := by
    rw [a.matricize_FH hl.1 θ, Matrix.sub_mul, sub_eq_zero, Matrix.mul_assoc] at hcl'
    exact hcl'.symm
  -- Step 4: `F = T (H G⁻¹)`, so `col F ⊆ col T`.
  have hFTK : a.Ffun hl.1 θ
      = a.matricizeOf hl.1 Tstar
        * (a.Hfun hl.1 θ * ((a.Hfun hl.1 θ)ᵀ * a.Hfun hl.1 θ)⁻¹) := by
    rw [← Matrix.mul_assoc, hTH, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGdet, Matrix.mul_one]
  have hFleT : LinearMap.range (a.Ffun hl.1 θ).mulVecLin
      ≤ LinearMap.range (a.matricizeOf hl.1 Tstar).mulVecLin := by
    rw [hFTK, Matrix.mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _
  -- Step 5: rank pinch ⇒ `rank T = ρ` and `col T = col F`.
  have hrankFT : (a.Ffun hl.1 θ).rank ≤ (a.matricizeOf hl.1 Tstar).rank := by
    rw [hFTK]; exact Matrix.rank_mul_le_left _ _
  have hrankT : (a.matricizeOf hl.1 Tstar).rank = a.r s(v, u) :=
    le_antisymm (hb v u hl.1) (hFrank ▸ hrankFT)
  have hsFT : LinearMap.range (a.Ffun hl.1 θ).mulVecLin
      = LinearMap.range (a.matricizeOf hl.1 Tstar).mulVecLin :=
    Submodule.eq_of_le_of_finrank_le hFleT (le_of_eq (hrankT.trans hFrank.symm))
  -- Step 6: `F Fᵀ` fixes the columns of `T` (which lie in `col F = col T`).
  have hcolfix : ∀ j : a.Col hl.1,
      (a.Ffun hl.1 θ * (a.Ffun hl.1 θ)ᵀ) *ᵥ (a.matricizeOf hl.1 Tstar).col j
      = (a.matricizeOf hl.1 Tstar).col j := by
    intro j
    have hmemT : (a.matricizeOf hl.1 Tstar).col j
        ∈ LinearMap.range (a.matricizeOf hl.1 Tstar).mulVecLin :=
      ⟨Pi.single j 1, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]⟩
    rw [← hsFT] at hmemT
    obtain ⟨x, hx⟩ := hmemT
    rw [Matrix.mulVecLin_apply] at hx
    rw [← hx, Matrix.mulVec_mulVec, Matrix.mul_assoc, hFtF, Matrix.mul_one]
  have hproj : (a.Ffun hl.1 θ * (a.Ffun hl.1 θ)ᵀ) * a.matricizeOf hl.1 Tstar
      = a.matricizeOf hl.1 Tstar := by
    ext i j
    rw [colmul]; exact congrFun (hcolfix j) i
  -- Assemble: `B := Tᵀ F`.
  refine ⟨(a.matricizeOf hl.1 Tstar)ᵀ * a.Ffun hl.1 θ, ?_, ?_, ?_⟩
  · -- `T = F Bᵀ`.
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc]
    exact hproj.symm
  · -- Minimality (i): vacuous since `rank T = ρ`.
    intro l hl' j
    rw [hrankT] at hl'
    exact absurd hl' (Nat.not_le.mpr l.isLt)
  · -- Minimality (ii): the columns of `F` are independent.
    intro g _ hgsum
    have hli : LinearIndependent ℝ (a.Ffun hl.1 θ).col := by
      have hF := hFrank
      rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
      rw [Matrix.rank_eq_finrank_span_cols] at hF
      exact hF.symm
    funext l
    exact Fintype.linearIndependent_iff.mp hli g hgsum l

/-- `liftParam` commutes with updating a reduced node: perturbing `θr` at `w'` lifts to perturbing
the assembled `θ` at `w'.1`. -/
theorem liftParam_update {v u : a.V} (hl : a.IsLeafWith v u)
    (Wv : Fin (a.r s(v, u)) → Fin (a.n v) → ℝ) (θr : (a.reducedArch hl).Param)
    (wr : (a.reducedArch hl).V) (δ : (a.reducedArch hl).NodeTensor wr) :
    ∃ δ' : a.NodeTensor wr.1,
      a.liftParam hl Wv (Function.update θr wr δ)
        = Function.update (a.liftParam hl Wv θr) wr.1 δ' := by
  refine ⟨a.liftParam hl Wv (Function.update θr wr δ) wr.1, ?_⟩
  funext w
  by_cases hw : w = wr.1
  · subst hw; rw [Function.update_self]
  · rw [Function.update_of_ne hw]
    funext bi xw
    simp only [liftParam]
    by_cases hwv : w = v
    · simp only [dif_pos hwv]
    · by_cases hwu : w = u
      · simp only [dif_neg hwv, dif_pos hwu]
        rw [show (Function.update θr wr δ) (a.reducedU hl) = θr (a.reducedU hl) from
          Function.update_of_ne (fun h => hw (hwu.trans (congrArg Subtype.val h))) _ _]
      · simp only [dif_neg hwv, dif_neg hwu]
        rw [show (Function.update θr wr δ)
              ⟨w, by rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hwv⟩
            = θr ⟨w, by rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hwv⟩ from
          Function.update_of_ne (fun h => hw (congrArg Subtype.val h)) _ _]

/-- **Reconstruction**: `pack` inverts the `(colExtract, jExtract)` split. If `x`'s column data
already matches that of a reduced index `xr`, then packing `x` with `xr`'s bond value recovers `xr`. -/
theorem pack_colExtract {v u : a.V} (hl : a.IsLeafWith v u) (x : a.Ext)
    (xr : (a.reducedArch hl).Ext) (hx : (a.extSplit hl.1 x).2 = a.colExtract hl xr) :
    a.pack hl x (a.jExtract hl xr) = xr := by
  classical
  funext z
  have hzv : z.1 ≠ v := fun hc => z.2 (Set.mem_singleton_iff.mpr hc)
  by_cases hzu : z.1 = u
  · obtain rfl : z = a.reducedU hl := Subtype.ext hzu
    have huns : ¬ a.Side hl.1 u := fun h => a.reduced_uNeV hl ((a.side_leaf hl u).mp h)
    have hxu : x u = a.colExtract hl xr ⟨u, huns⟩ := congrFun hx ⟨u, huns⟩
    rw [a.pack_reducedU hl x (a.jExtract hl xr), hxu, ← finCongr_symm, Equiv.symm_apply_eq,
      Equiv.apply_eq_iff_eq_symm_apply]
    refine Prod.ext ?_ ?_
    · show a.colExtract hl xr ⟨u, huns⟩
        = (finProdFinEquiv.symm
            (finCongr (a.reducedArch_n_eq_u hl (a.reducedU hl) rfl) (xr (a.reducedU hl)))).1
      simp only [colExtract, dif_pos]
      apply Fin.ext
      simp only [finCongr_apply, Fin.val_cast]
      rfl
    · rfl
  · have huns : ¬ a.Side hl.1 z.1 := fun h => hzv ((a.side_leaf hl z.1).mp h)
    have hxz : x z.1 = a.colExtract hl xr ⟨z.1, huns⟩ := congrFun hx ⟨z.1, huns⟩
    have hpackz : a.pack hl x (a.jExtract hl xr) z
        = finCongr (a.reducedArch_n_eq_ne hl z hzu).symm (x z.1) := by
      simp only [pack, dif_neg hzu]
    rw [hpackz, hxz, ← finCongr_symm, Equiv.symm_apply_eq]
    simp only [colExtract, dif_neg hzu]
    rfl

/-- The reduced external index splits as its `Col` data together with the folded leaf-bond value:
`(colExtract, jExtract)` and `pack` are mutually inverse. -/
noncomputable def extColEquiv {v u : a.V} (hl : a.IsLeafWith v u) :
    (a.reducedArch hl).Ext ≃ a.Col hl.1 × Fin (a.r s(v, u)) where
  toFun xr := (a.colExtract hl xr, a.jExtract hl xr)
  invFun p := a.pack hl ((a.extSplit hl.1).symm (fun w => ⟨0, a.hn w.1⟩, p.1)) p.2
  left_inv xr := a.pack_colExtract hl _ xr (by rw [Equiv.apply_symm_apply])
  right_inv p := by
    refine Prod.ext ?_ ?_
    · show a.colExtract hl (a.pack hl ((a.extSplit hl.1).symm (fun w => ⟨0, a.hn w.1⟩, p.1)) p.2) = p.1
      rw [a.colExtract_pack hl, Equiv.apply_symm_apply]
    · exact a.jExtract_pack hl _ p.2

/-- **Row-independence of `pack`.** `pack x j` depends on `x` only through its `Col` data: replacing
the leaf/`Row` part by any other row gives the same reduced index (namely `extColEquiv.symm`). -/
theorem pack_extSplit_symm {v u : a.V} (hl : a.IsLeafWith v u)
    (row : a.Row hl.1) (col : a.Col hl.1) (j : Fin (a.r s(v, u))) :
    a.pack hl ((a.extSplit hl.1).symm (row, col)) j = (a.extColEquiv hl).symm (col, j) := by
  have h := (a.extColEquiv hl).apply_symm_apply (col, j)
  have hc : a.colExtract hl ((a.extColEquiv hl).symm (col, j)) = col := congrArg Prod.fst h
  have hj : a.jExtract hl ((a.extColEquiv hl).symm (col, j)) = j := congrArg Prod.snd h
  conv_lhs => rw [← hj]
  refine a.pack_colExtract hl _ _ ?_
  rw [Equiv.apply_symm_apply]
  exact hc.symm

/-- **Orthonormality collapse.** Summing the leaf-tensor bilinear pairing over all leaf-external
values collapses via `WᵀW = 1` to the plain pairing of the bond coefficients. -/
theorem Wsum_orth {v u : a.V} (hl : a.IsLeafWith v u) {θ : a.Param}
    (horth : (a.Wleaf hl θ)ᵀ * a.Wleaf hl θ = 1) (P Q : Fin (a.r s(v, u)) → ℝ) :
    (∑ row : a.Row hl.1,
        (∑ j, a.Wleaf hl θ (row ⟨v, (a.side_leaf hl v).mpr rfl⟩) j * P j)
          * (∑ j', a.Wleaf hl θ (row ⟨v, (a.side_leaf hl v).mpr rfl⟩) j' * Q j'))
      = ∑ j, P j * Q j := by
  have hrow : (∑ row : a.Row hl.1,
        (∑ j, a.Wleaf hl θ (row ⟨v, (a.side_leaf hl v).mpr rfl⟩) j * P j)
          * (∑ j', a.Wleaf hl θ (row ⟨v, (a.side_leaf hl v).mpr rfl⟩) j' * Q j'))
      = ∑ xv : Fin (a.n v), (a.Wleaf hl θ *ᵥ P) xv * (a.Wleaf hl θ *ᵥ Q) xv :=
    Fintype.sum_equiv (a.rowLeafEquiv hl) _ _ (fun row => rfl)
  rw [hrow]
  show (a.Wleaf hl θ *ᵥ P) ⬝ᵥ (a.Wleaf hl θ *ᵥ Q) = ∑ j, P j * Q j
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, horth, Matrix.vecMul_one]
  rfl

/-- **Criticality reindexing.** The leaf-weighted double bond-sum over the full external index
collapses (via the leaf `Row × Col` split and orthonormality) to the plain pairing over the reduced
external index. This is the combinatorial heart of transferring criticality to the reduced tree. -/
theorem crit_reindex {v u : a.V} (hl : a.IsLeafWith v u) {θ : a.Param}
    (horth : (a.Wleaf hl θ)ᵀ * a.Wleaf hl θ = 1)
    (F G : (a.reducedArch hl).Ext → ℝ) :
    (∑ x : a.Ext, (∑ j, a.Wleaf hl θ (x v) j * F (a.pack hl x j))
        * (∑ j', a.Wleaf hl θ (x v) j' * G (a.pack hl x j')))
      = ∑ xr, F xr * G xr := by
  conv_lhs => rw [← Equiv.sum_comp (a.extSplit hl.1).symm, Fintype.sum_prod_type]
  conv_rhs => rw [← Equiv.sum_comp (a.extColEquiv hl).symm, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun col _ => ?_)
  rw [← a.Wsum_orth hl horth (fun j => F ((a.extColEquiv hl).symm (col, j)))
        (fun j => G ((a.extColEquiv hl).symm (col, j)))]
  refine Finset.sum_congr rfl (fun row _ => ?_)
  have hrv : (a.extSplit hl.1).symm (row, col) v = row ⟨v, (a.side_leaf hl v).mpr rfl⟩ :=
    a.extSplit_symm_row hl.1 row col ⟨v, (a.side_leaf hl v).mpr rfl⟩
  congr 1 <;>
    refine Finset.sum_congr rfl (fun j _ => ?_) <;>
    rw [hrv, a.pack_extSplit_symm hl row col j]

/-- **Reduced criticality** (Theorem 5.2, Step 2). With an orthonormal leaf and the target factored
`T*⁽ᵉ⁾ = Ffun Bᵀ`, the reduced parameters are a critical point of the reduced loss. -/
theorem reduced_critical {v u : a.V} (hl : a.IsLeafWith v u) {Tstar : a.Ext → ℝ}
    {θ : a.Param} (hcrit : a.Critical Tstar θ) (horth : (a.Wleaf hl θ)ᵀ * a.Wleaf hl θ = 1)
    {B : Matrix (a.Col hl.1) (Fin (a.r s(v, u))) ℝ}
    (hAB : a.matricizeOf hl.1 Tstar = a.Ffun hl.1 θ * Bᵀ) :
    (a.reducedArch hl).Critical (a.Tred hl B) (a.reducedParam hl θ) := by
  classical
  intro wr δ
  -- The reduced perturbation `δ` at `wr` lifts to a perturbation `δ'` of `θ` at `wr.1`.
  obtain ⟨δ', hδ'⟩ :=
    a.liftParam_update hl (fun j xv => a.Wleaf hl θ xv j) (a.reducedParam hl θ) wr δ
  rw [a.liftParam_reducedParam hl θ] at hδ'
  -- The perturbed original network splits over the leaf bond against the perturbed reduced network.
  have hrepUpd : ∀ x : a.Ext,
      a.represented (Function.update θ wr.1 δ') x
        = ∑ j, a.Wleaf hl θ (x v) j
            * (a.reducedArch hl).represented
                (Function.update (a.reducedParam hl θ) wr δ) (a.pack hl x j) := by
    intro x
    rw [← hδ', a.represented_liftParam hl (fun j xv => a.Wleaf hl θ xv j)
      (Function.update (a.reducedParam hl θ) wr δ) x]
  -- The original residual splits over the leaf bond against the reduced residual.
  have hR : ∀ x : a.Ext,
      a.residual Tstar θ x
        = ∑ j, a.Wleaf hl θ (x v) j
            * ((a.reducedArch hl).represented (a.reducedParam hl θ) (a.pack hl x j)
               - a.Tred hl B (a.pack hl x j)) := by
    intro x
    have hrepθ : a.represented θ x
        = ∑ j, a.Wleaf hl θ (x v) j
            * (a.reducedArch hl).represented (a.reducedParam hl θ) (a.pack hl x j) := by
      conv_lhs => rw [← a.liftParam_reducedParam hl θ]
      rw [a.represented_liftParam hl (fun j xv => a.Wleaf hl θ xv j) (a.reducedParam hl θ) x]
    have hTstar : Tstar x
        = ∑ j, a.Wleaf hl θ (x v) j * a.Tred hl B (a.pack hl x j) := by
      rw [a.target_eq_sum hl Tstar (a.Ffun hl.1 θ) B hAB x]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Tred, a.colExtract_pack hl x, a.jExtract_pack hl x]
      congr 1
      rw [a.Ffun_leaf hl θ (a.extSplit hl.1 x).1 j]
      rfl
    simp only [residual]
    rw [hrepθ, hTstar, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  -- Feed the leaf-lifted perturbation into criticality, then reindex.
  have hc := hcrit wr.1 δ'
  simp only [hR, hrepUpd] at hc
  simp only [residual]
  rw [← hc]
  exact (a.crit_reindex hl horth _ _).symm


/-- **Lift** (Theorem 5.2, Step 2, conclusion). If the reduced network represents its reduced target
`Tred B`, then the original network represents `Tstar`. -/
theorem lift_represented {v u : a.V} (hl : a.IsLeafWith v u) {Tstar : a.Ext → ℝ}
    {θ : a.Param} {B : Matrix (a.Col hl.1) (Fin (a.r s(v, u))) ℝ}
    (hAB : a.matricizeOf hl.1 Tstar = a.Ffun hl.1 θ * Bᵀ)
    (hrep : (a.reducedArch hl).represented (a.reducedParam hl θ) = a.Tred hl B) :
    a.represented θ = Tstar := by
  funext x
  -- decompose `θ` and expand via the leaf-split identity
  have hdecomp : a.represented θ x
      = ∑ j, a.Wleaf hl θ (x v) j
          * (a.reducedArch hl).represented (a.reducedParam hl θ) (a.pack hl x j) := by
    conv_lhs => rw [← a.liftParam_reducedParam hl θ]
    rw [a.represented_liftParam hl (fun j xv => a.Wleaf hl θ xv j) (a.reducedParam hl θ) x]
  rw [hdecomp, hrep]
  simp only [Tred, a.colExtract_pack hl x, a.jExtract_pack hl x]
  -- now `∑ j, Wleaf (x v) j * B (extSplit x).2 j`; identify `Wleaf (x v) = Ffun (extSplit x).1`
  rw [a.target_eq_sum hl Tstar (a.Ffun hl.1 θ) B hAB x]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 1
  rw [a.Ffun_leaf hl θ (a.extSplit hl.1 x).1 j]
  rfl

/-- **One leaf-removal step of Theorem 5.2.** At a full-Tucker-rank critical point of a realizable
target, peeling a leaf `v` yields a reduced architecture, reduced parameters `θr`, and a reduced
target `T̃` that again satisfy realizability, criticality, and full Tucker rank — and such that the
reduced network representing `T̃` forces the original network to represent `Tstar`. -/
theorem exists_reduction {v u : a.V} (hl : a.IsLeafWith v u) {Tstar : a.Ext → ℝ}
    (hb : a.RankBound Tstar) {θ : a.Param} (hcrit : a.Critical Tstar θ) (hftr : a.FullTuckerRank θ) :
    ∃ (θr : (a.reducedArch hl).Param) (Ttilde : (a.reducedArch hl).Ext → ℝ),
      (a.reducedArch hl).RankBound Ttilde ∧
      (a.reducedArch hl).Critical Ttilde θr ∧
      (a.reducedArch hl).FullTuckerRank θr ∧
      ((a.reducedArch hl).represented θr = Ttilde → a.represented θ = Tstar) := by
  -- Step 0: gauge to an orthonormal leaf tensor.
  obtain ⟨θ', hrep', hcrit', hftr', horth⟩ := a.exists_gauge hl hcrit hftr
  -- Step 1: factor the target through the leaf tensor.
  obtain ⟨B, hAB, hBz, hAli⟩ := a.leaf_target_factor hl hb hcrit' hftr' horth
  -- Step 2: the reduced data satisfies all hypotheses; the lift closes the goal.
  refine ⟨a.reducedParam hl θ', a.Tred hl B, a.reduced_rankBound hl hb hAB hBz hAli,
    a.reduced_critical hl hcrit' horth hAB, a.reduced_fullRank hl hftr', fun h => ?_⟩
  exact hrep' ▸ a.lift_represented hl hAB h

/-! ### Theorem 5.2: main statements -/

variable (a)

/-- Strong-induction core of Theorem 5.2: a full-Tucker-rank critical point of a target satisfying
the edge-rank bound realizes it, by induction on `|V|` via leaf removal. -/
theorem critical_fullRank_represented_eq_aux :
    ∀ (N : ℕ) (b : Arch), Fintype.card b.V = N → ∀ (T : b.Ext → ℝ), b.RankBound T →
      ∀ (θ : b.Param), b.Critical T θ → b.FullTuckerRank θ → b.represented θ = T := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro b hcard T hb θ hcrit hftr
    by_cases hnt : Nontrivial b.V
    · -- Inductive step: peel a leaf and apply `exists_reduction`.
      obtain ⟨v, hv⟩ := b.hT.exists_vert_degree_one_of_nontrivial
      obtain ⟨u, hadj, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
      have hl : b.IsLeafWith v u := ⟨hadj, huniq⟩
      obtain ⟨θr, Ttilde, hbr, hcritr, hftrr, hlift⟩ := b.exists_reduction hl hb hcrit hftr
      have hNlt : N - 1 < N := by
        have : 1 < Fintype.card b.V := Fintype.one_lt_card_iff_nontrivial.mpr hnt
        omega
      have hcard' : Fintype.card (b.reducedArch hl).V = N - 1 := by
        show Fintype.card ↥({v}ᶜ : Set b.V) = N - 1
        rw [Fintype.card_compl_set, hcard]; simp
      exact hlift (ih (N - 1) hNlt (b.reducedArch hl) hcard' Ttilde hbr θr hcritr hftrr)
    · -- Base case: a single node; criticality with `δ := residual` forces the residual to zero.
      have hsub : Subsingleton b.V := not_nontrivial_iff_subsingleton.mp hnt
      obtain ⟨w₀⟩ := b.hT.connected.nonempty
      haveI : Unique b.Bond := by
        have hbe : IsEmpty ↥b.G.edgeSet := by
          constructor; rintro ⟨e, he⟩
          induction e using Sym2.ind with
          | _ p q => rw [SimpleGraph.mem_edgeSet] at he; exact he.ne (Subsingleton.elim p q)
        exact ⟨⟨fun e => isEmptyElim e⟩, fun _ => funext fun e => isEmptyElim e⟩
      set δ₀ : b.NodeTensor w₀ :=
        fun _ xw => b.residual T θ (fun w' => Fin.cast (congrArg b.n (Subsingleton.elim w₀ w')) xw)
        with hδ₀
      have hrep_upd : ∀ x : b.Ext, b.represented (Function.update θ w₀ δ₀) x = b.residual T θ x := by
        intro x
        simp only [represented]
        rw [Fintype.sum_unique, Fintype.prod_subsingleton _ w₀, Function.update_self]
        show b.residual T θ (fun w' => Fin.cast (congrArg b.n (Subsingleton.elim w₀ w')) (x w₀))
          = b.residual T θ x
        congr 1
        funext w'
        apply Fin.ext
        simp only [Fin.val_cast]
        exact (congrArg (fun w => (x w).val) (Subsingleton.elim w₀ w'))
      have hsq : ∑ x : b.Ext, b.residual T θ x * b.residual T θ x = 0 := by
        have := hcrit w₀ δ₀
        rw [Finset.sum_congr rfl (fun x _ => by rw [hrep_upd x])] at this
        exact this
      funext x
      have hz : b.residual T θ x = 0 := by
        have hnn : ∀ y ∈ (Finset.univ : Finset b.Ext), (0 : ℝ) ≤ b.residual T θ y * b.residual T θ y :=
          fun y _ => mul_self_nonneg _
        have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsq x (Finset.mem_univ x)
        exact (mul_self_eq_zero).mp this
      have : b.represented θ x - T x = 0 := hz
      linarith [this]

/-- **Paper correspondence: Theorem 5.2, zero-residual core conclusion.**
A full-Tucker-rank critical point of a realizable target realizes it
(the residual is zero). -/
theorem critical_fullRank_represented_eq {Tstar : a.Ext → ℝ} (hreal : a.Realizable Tstar)
    {θ : a.Param} (hcrit : a.Critical Tstar θ) (hftr : a.FullTuckerRank θ) :
    a.represented θ = Tstar :=
  critical_fullRank_represented_eq_aux (Fintype.card a.V) a rfl Tstar
    (a.realizable_iff_rank_le.mp hreal) θ hcrit hftr

/-- **Paper correspondence: Theorem 5.2, full-rank critical points are global minima.**
A full-Tucker-rank critical point of a realizable target is
a global minimum of the loss. The realizability hypothesis `hreal` is implicit in the paper's
statement (its proof uses "Realizability gives `rank(T*⁽ᵉ⁾) ≤ r_e`" as a standing assumption);
we make it explicit. `Critical` is bridged to Mathlib's `HasDerivAt` in `TTN/Landscape/Criticality.lean`. -/
theorem critical_fullRank_isGlobalMin {Tstar : a.Ext → ℝ} (hreal : a.Realizable Tstar)
    {θ : a.Param} (hcrit : a.Critical Tstar θ) (hftr : a.FullTuckerRank θ) :
    a.IsGlobalMin Tstar θ := by
  have hrep := a.critical_fullRank_represented_eq hreal hcrit hftr
  intro θ'
  have hzero : a.loss Tstar θ = 0 := by
    simp only [loss, hrep, sub_self]
    simp
  rw [hzero]
  have : (0 : ℝ) ≤ ∑ x : a.Ext, (a.represented θ' x - Tstar x) ^ 2 :=
    Finset.sum_nonneg fun x _ => sq_nonneg _
  simp only [loss]
  positivity

/-- **Paper correspondence: Theorem 5.2, contrapositive formulation.**
A critical point of a realizable target that is
not a global minimum cannot have full Tucker rank. -/
theorem not_fullRank_of_critical_of_not_isGlobalMin {Tstar : a.Ext → ℝ} (hreal : a.Realizable Tstar)
    {θ : a.Param} (hcrit : a.Critical Tstar θ) (hng : ¬ a.IsGlobalMin Tstar θ) :
    ¬ a.FullTuckerRank θ :=
  fun hftr => hng (a.critical_fullRank_isGlobalMin hreal hcrit hftr)

end Arch

end TTN
