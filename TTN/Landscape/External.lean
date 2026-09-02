import TTN.Landscape.Realizability
import TTN.Landscape.RealizabilityConverse

/-!
# Bridge: literal TTNs (individual external edges) ↔ the aggregate encoding

`TTN.Arch` encodes a tree tensor network with the external legs of each node **aggregated** into a
single combined dimension `n_v` (the notation used in this development; see `TTN/Arch.lean`).
Definition 3.1 of the paper instead keeps one *individual* external edge per external mode. This module makes that
aggregation a **theorem**, not just a modeling remark: an `ExtStruct` equips an aggregate `Arch`
with the literal external-edge data (`Xe v` edges at `v`, dimensions `xd v x`, with
`n_v = ∏ xd v x`), defines the literal represented tensor and literal matricizations over the
individual external modes, and proves the literal realizability problem is *equivalent* to the
aggregate one — hence the realizability characterization holds for the literal external-leg object.

The paper's own edge matricization already aggregates external modes per node
(`m_e = ∏_{v ∈ V_e} n_v`), so no information relevant to realizability is lost by the encoding; the
individual external dimensions only reappear as the factorization `n_v = ∏ xd v x`, which is exactly
what `ExtStruct` records. The literal matricization below is proved rank-equivalent to the aggregate
matricization by row and column reindexing.
-/

open scoped Matrix
namespace TTN
namespace Arch

variable {a : Arch}

/-- A **literal external-edge structure** on an aggregate architecture `a`: for each node `v`, a
finite set `Xe v` of external edges with individual positive dimensions `xd v x` whose product is
the aggregate external dimension `a.n v`. This exhibits `a` as the per-node aggregation of a literal
TTN (Definition 3.1) in which each external edge carries its own tensor mode. -/
structure ExtStruct (a : Arch) where
  /-- The external edges incident to each node. -/
  Xe : a.V → Type
  /-- `Xe v` is finite. -/
  fXe : ∀ v, Fintype (Xe v)
  /-- `Xe v` has decidable equality (for the product index). -/
  dXe : ∀ v, DecidableEq (Xe v)
  /-- The individual external-edge dimension `d_e`. -/
  xd : (v : a.V) → Xe v → ℕ
  /-- External dimensions are positive. -/
  hpos : ∀ v x, 0 < xd v x
  /-- The aggregate dimension is the product of the individual external dimensions at `v`. -/
  hagg : ∀ v, a.n v = ∏ x : Xe v, xd v x

attribute [instance] ExtStruct.fXe ExtStruct.dXe

namespace ExtStruct

variable (E : ExtStruct a)

/-- The **literal external index at a node**: one mode per external edge (Definition 3.1's
`⊗_{e external at v} ℝ^{d_e}`, as an index function). -/
def LitExtAt (v : a.V) : Type := (x : E.Xe v) → Fin (E.xd v x)

instance (v : a.V) : Fintype (E.LitExtAt v) := by unfold LitExtAt; infer_instance
instance (v : a.V) : DecidableEq (E.LitExtAt v) := by unfold LitExtAt; infer_instance

/-- The card of the literal node index is the aggregate external dimension. -/
theorem card_LitExtAt (v : a.V) : Fintype.card (E.LitExtAt v) = a.n v := by
  rw [E.hagg v]
  show Fintype.card ((x : E.Xe v) → Fin (E.xd v x)) = ∏ x : E.Xe v, E.xd v x
  rw [Fintype.card_pi]
  simp

/-- Per-node reshape between the aggregate mode `Fin (n_v)` and the literal external modes.

Note this is an **arbitrary enumeration bijection** (`Fintype.equivFinOfCardEq`), not the
canonical lexicographic unfolding of the tensor product. That is deliberate and sufficient:
every statement transported through it (realizability, matricization ranks) is invariant
under *any* bijective reindexing of each node's external mode. Statements that depend on the
multilinear structure of the individual external modes would need the lexicographic
equivalence instead — none of the results bridged here do. -/
noncomputable def nodeEquiv (v : a.V) : Fin (a.n v) ≃ E.LitExtAt v :=
  (Fintype.equivFinOfCardEq (E.card_LitExtAt v)).symm

/-- The **literal external index** of the whole network: one mode per external edge, at every node.
(Definition 3.1's external modes of `T(θ)`.) -/
def LitExt : Type := (v : a.V) → E.LitExtAt v

instance : Fintype E.LitExt := by unfold LitExt; infer_instance
instance : DecidableEq E.LitExt := by unfold LitExt; infer_instance

/-- The reshape of the whole external index: `Ext ≃ LitExt`, node by node. -/
noncomputable def extEquiv : a.Ext ≃ E.LitExt := Equiv.piCongrRight E.nodeEquiv

/-! ### Literal edge matricization -/

/-- Literal row index of an edge matricization: individual external modes on the `Side` of the cut. -/
def LitRow {u w : a.V} (h : a.G.Adj u w) : Type :=
  (v : {x : a.V // a.Side h x}) → E.LitExtAt v

/-- Literal column index of an edge matricization: individual external modes off the `Side` of the cut. -/
def LitCol {u w : a.V} (h : a.G.Adj u w) : Type :=
  (v : {x : a.V // ¬ a.Side h x}) → E.LitExtAt v

instance {u w : a.V} (h : a.G.Adj u w) : Fintype (E.LitRow h) := by
  unfold LitRow; infer_instance

instance {u w : a.V} (h : a.G.Adj u w) : Fintype (E.LitCol h) := by
  unfold LitCol; infer_instance

instance {u w : a.V} (h : a.G.Adj u w) : DecidableEq (E.LitRow h) := by
  unfold LitRow; infer_instance

instance {u w : a.V} (h : a.G.Adj u w) : DecidableEq (E.LitCol h) := by
  unfold LitCol; infer_instance

/-- Reshape a literal external index across a cut. -/
def litExtSplit {u w : a.V} (h : a.G.Adj u w) : E.LitExt ≃ E.LitRow h × E.LitCol h :=
  Equiv.piEquivPiSubtypeProd (a.Side h) (fun v => E.LitExtAt v)

/-- Row reindexing between aggregate and literal row indices. -/
noncomputable def rowEquiv {u w : a.V} (h : a.G.Adj u w) : a.Row h ≃ E.LitRow h :=
  Equiv.piCongrRight (fun v => E.nodeEquiv v)

/-- Column reindexing between aggregate and literal column indices. -/
noncomputable def colEquiv {u w : a.V} (h : a.G.Adj u w) : a.Col h ≃ E.LitCol h :=
  Equiv.piCongrRight (fun v => E.nodeEquiv v)

/-- Reading off a Side literal mode from the reshaped literal index. -/
theorem litExtSplit_symm_row {u w : a.V} (h : a.G.Adj u w) (row : E.LitRow h)
    (col : E.LitCol h) (v : {x // a.Side h x}) :
    (E.litExtSplit h).symm (row, col) v.1 = row v := by
  have hh : (E.litExtSplit h).symm (row, col) v.1
      = if hp : a.Side h v.1 then row ⟨v.1, hp⟩ else col ⟨v.1, hp⟩ := rfl
  rw [hh, dif_pos v.2]

/-- Reading off a Col literal mode from the reshaped literal index. -/
theorem litExtSplit_symm_col {u w : a.V} (h : a.G.Adj u w) (row : E.LitRow h)
    (col : E.LitCol h) (v : {x // ¬ a.Side h x}) :
    (E.litExtSplit h).symm (row, col) v.1 = col v := by
  have hh : (E.litExtSplit h).symm (row, col) v.1
      = if hp : a.Side h v.1 then row ⟨v.1, hp⟩ else col ⟨v.1, hp⟩ := rfl
  rw [hh, dif_neg v.2]

/-- Compatibility of the global external reshape with the aggregate and literal cut splits. -/
theorem extEquiv_extSplit_symm {u w : a.V} (h : a.G.Adj u w)
    (row : E.LitRow h) (col : E.LitCol h) :
    E.extEquiv ((a.extSplit h).symm ((E.rowEquiv h).symm row, (E.colEquiv h).symm col))
      = (E.litExtSplit h).symm (row, col) := by
  funext v
  by_cases hv : a.Side h v
  · calc
      E.extEquiv ((a.extSplit h).symm ((E.rowEquiv h).symm row, (E.colEquiv h).symm col)) v
          = E.nodeEquiv v
              (((a.extSplit h).symm ((E.rowEquiv h).symm row, (E.colEquiv h).symm col)) v) := rfl
      _ = E.nodeEquiv v (((E.rowEquiv h).symm row) ⟨v, hv⟩) := by
            rw [a.extSplit_symm_row h ((E.rowEquiv h).symm row)
              ((E.colEquiv h).symm col) ⟨v, hv⟩]
      _ = row ⟨v, hv⟩ := by
            change (E.nodeEquiv v) ((E.nodeEquiv v).symm (row ⟨v, hv⟩)) = row ⟨v, hv⟩
            exact Equiv.apply_symm_apply (E.nodeEquiv v) (row ⟨v, hv⟩)
      _ = (E.litExtSplit h).symm (row, col) v := by
            rw [E.litExtSplit_symm_row h row col ⟨v, hv⟩]
  · calc
      E.extEquiv ((a.extSplit h).symm ((E.rowEquiv h).symm row, (E.colEquiv h).symm col)) v
          = E.nodeEquiv v
              (((a.extSplit h).symm ((E.rowEquiv h).symm row, (E.colEquiv h).symm col)) v) := rfl
      _ = E.nodeEquiv v (((E.colEquiv h).symm col) ⟨v, hv⟩) := by
            rw [a.extSplit_symm_col h ((E.rowEquiv h).symm row)
              ((E.colEquiv h).symm col) ⟨v, hv⟩]
      _ = col ⟨v, hv⟩ := by
            change (E.nodeEquiv v) ((E.nodeEquiv v).symm (col ⟨v, hv⟩)) = col ⟨v, hv⟩
            exact Equiv.apply_symm_apply (E.nodeEquiv v) (col ⟨v, hv⟩)
      _ = (E.litExtSplit h).symm (row, col) v := by
            rw [E.litExtSplit_symm_col h row col ⟨v, hv⟩]

/-- The literal edge matricization of a literal target tensor. -/
noncomputable def matricizeLit {u w : a.V} (h : a.G.Adj u w) (Tl : E.LitExt → ℝ) :
    Matrix (E.LitRow h) (E.LitCol h) ℝ :=
  fun row col => Tl ((E.litExtSplit h).symm (row, col))

/-- Literal matricization is the aggregate matricization with rows and columns reindexed. -/
theorem matricizeLit_eq_submatrix {u w : a.V} (h : a.G.Adj u w) (Tl : E.LitExt → ℝ) :
    E.matricizeLit h Tl =
      (a.matricizeOf h (fun x => Tl (E.extEquiv x))).submatrix
        (E.rowEquiv h).symm (E.colEquiv h).symm := by
  ext row col
  simp only [matricizeLit, matricizeOf, Matrix.submatrix_apply]
  rw [E.extEquiv_extSplit_symm h row col]

/-- Literal and aggregate edge matricizations have the same rank. -/
theorem rank_matricizeLit_eq {u w : a.V} (h : a.G.Adj u w) (Tl : E.LitExt → ℝ) :
    (E.matricizeLit h Tl).rank =
      (a.matricizeOf h (fun x => Tl (E.extEquiv x))).rank := by
  rw [E.matricizeLit_eq_submatrix h Tl, Matrix.rank_submatrix]

/-- A **literal node tensor**: real array over `v`'s incident bonds and its *individual* external
modes (one mode per external edge). -/
def LitNodeTensor (v : a.V) : Type := a.BondIdx v → E.LitExtAt v → ℝ

/-- **Literal parameters**: a literal node tensor at each node. -/
def LitParam : Type := (v : a.V) → E.LitNodeTensor v

/-- The **literal represented tensor** (Definition 3.1): contract the literal node tensors along the
internal bonds, leaving one mode per external edge open. -/
noncomputable def representedLit (θl : E.LitParam) : E.LitExt → ℝ :=
  fun xl => ∑ b : a.Bond, ∏ v : a.V, θl v (Bond.restrict b v) (xl v)

/-- A literal target is **realizable** if some literal parameter point represents it. -/
def RealizableLit (Tl : E.LitExt → ℝ) : Prop := ∃ θl : E.LitParam, E.representedLit θl = Tl

/-- Transport a literal parameter point to an aggregate one (evaluate through `nodeEquiv`). -/
noncomputable def toAgg (θl : E.LitParam) : a.Param :=
  fun v bi k => θl v bi (E.nodeEquiv v k)

/-- Transport an aggregate parameter point to a literal one (the inverse of `toAgg`). -/
noncomputable def toLit (θ : a.Param) : E.LitParam :=
  fun v bi kl => θ v bi ((E.nodeEquiv v).symm kl)

@[simp] theorem toAgg_toLit (θ : a.Param) : E.toAgg (E.toLit θ) = θ := by
  funext v bi k; simp [toAgg, toLit]

@[simp] theorem toLit_toAgg (θl : E.LitParam) : E.toLit (E.toAgg θl) = θl := by
  funext v bi kl; simp [toAgg, toLit]

/-- **Bridge (represented tensors).** The literal represented tensor, read at the reshaped external
index, equals the aggregate represented tensor of the transported parameters. -/
theorem representedLit_extEquiv (θl : E.LitParam) (x : a.Ext) :
    E.representedLit θl (E.extEquiv x) = a.represented (E.toAgg θl) x :=
  Finset.sum_congr rfl (fun _ _ => Finset.prod_congr rfl (fun _ _ => rfl))

/-- **Bridge (realizability).** A literal target is realizable iff its reshape to the aggregate
external index is realizable by the aggregate network. -/
theorem realizableLit_iff (Tl : E.LitExt → ℝ) :
    E.RealizableLit Tl ↔ a.Realizable (fun x => Tl (E.extEquiv x)) := by
  constructor
  · rintro ⟨θl, rfl⟩
    exact ⟨E.toAgg θl, by funext x; rw [← E.representedLit_extEquiv θl x]⟩
  · rintro ⟨θ, hθ⟩
    refine ⟨E.toLit θ, ?_⟩
    funext yl
    have := E.representedLit_extEquiv (E.toLit θ) (E.extEquiv.symm yl)
    rw [E.toAgg_toLit, Equiv.apply_symm_apply] at this
    rw [this, hθ]
    exact congrArg Tl (E.extEquiv.apply_symm_apply yl)

/-- **Realizability transported to aggregate matricizations.** A literal target `Tl` is realizable by
the TTN with bond dimensions `{r_e}` iff every internal-edge matricization of its aggregate reshape
has rank at most `r_e`. -/
theorem realizableLit_iff_aggregate_rank_le (Tl : E.LitExt → ℝ) :
    E.RealizableLit Tl ↔
      ∀ (u w : a.V) (h : a.G.Adj u w),
        (a.matricizeOf h (fun x => Tl (E.extEquiv x))).rank ≤ a.r s(u, w) := by
  rw [E.realizableLit_iff Tl, a.realizable_iff_rank_le]
  rfl

/-- **Realizability for the literal external modes.** A literal target `Tl` is realizable
iff every internal-edge matricization, with rows and columns indexed by the individual external modes
on each side of the cut, has rank at most the corresponding bond dimension. -/
theorem realizableLit_iff_rank_le (Tl : E.LitExt → ℝ) :
    E.RealizableLit Tl ↔
      ∀ (u w : a.V) (h : a.G.Adj u w), (E.matricizeLit h Tl).rank ≤ a.r s(u, w) := by
  rw [E.realizableLit_iff_aggregate_rank_le Tl]
  constructor
  · intro h u w hadj
    rw [E.rank_matricizeLit_eq hadj Tl]
    exact h u w hadj
  · intro h u w hadj
    rw [← E.rank_matricizeLit_eq hadj Tl]
    exact h u w hadj

end ExtStruct
end Arch
end TTN
