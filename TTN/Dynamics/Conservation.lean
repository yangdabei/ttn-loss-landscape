import TTN.Landscape.Criticality
import TTN.Landscape.Dormant

/-!
# Per-bond conservation law under gradient flow

This module proves the squared-loss specialization of the paper's full matrix conservation
law for the balancedness defect. Its chain instance is the familiar deep-linear-network
identity `d/dt(WᵢᵀWᵢ − Wᵢ₊₁Wᵢ₊₁ᵀ) = 0`.

* `gradNode`: the Euclidean gradient of the loss with respect to one node tensor, in the
  variational vocabulary of `Critical`.
* `pairing_eq_sum_gradNode`, `hasDerivAt_loss_line_gradNode`,
  `critical_iff_gradNode_eq_zero`: `gradNode` is the gradient
  (its pairing computes every line derivative of the loss, via
  `hasDerivAt_loss_line`), and `Critical = (gradNode ≡ 0)`.
* `IsGradFlow` — gradient flow of the loss, entrywise `HasDerivAt` form
  (`θ̇ = −∇L(θ)`; certified-flow style — the flow is a hypothesis, not a construction).
* `represented_update_modeMul_transfer` — the **transfer identity**: inserting a
  square matrix `M` on the `u`-side of bond `e = s(u,w)` equals inserting `Mᵀ` on the
  `w`-side. A pure bond-sum reindex over the shared edge index.
* `bondGramDiff_conserved`: along any
  gradient flow, `Δ_e := matₑ(W_u)matₑ(W_u)ᵀ − matₑ(W_w)matₑ(W_w)ᵀ` is constant.
* `bondGramDiff_eq_zero_of_balanced_init` — the balanced slice `Δ_e ≡ 0` is flow-invariant.
* `bondKernel_iff_of_balanced`: on the balanced slice the two endpoint bond kernels
  coincide at every time.

The bond-mode infrastructure (`adjIncLeft`/`adjIncRight`, `modeMul`, `matE_modeMul`)
lives in `TTN/Landscape/Dormant.lean`.

## The proof does not use acyclicity

The conservation law is the Noether consequence of the per-bond gauge symmetry
`(W_u, W_w) ↦ (W_u ·ₑ g, W_w ·ₑ g⁻ᵀ)` of the represented tensor, which only needs each
bond to have exactly two distinct endpoints, not the tree hypothesis. The statements below
are nevertheless typed over `Arch`, which bundles `G.IsTree`; no theorem for a general
graph is claimed here. No proof in this module invokes `a.hT`.
-/

open scoped Matrix

namespace TTN

namespace Arch

variable {a : Arch}

/-! ### The gradient of the loss at one node -/

open Classical in
/-- **The Euclidean gradient of the loss with respect to the node tensor `W_v`**.
Entry `(bi, xv)` is the first-order variation of `L` against the matching coordinate
tensor: `∑_x R(x) · T(θ with W_v ← e_{(bi,xv)})(x)`, by multilinearity of `T` — the
`δ`-coefficient functional of `Critical` evaluated on the standard basis. -/
noncomputable def gradNode (Tstar : a.Ext → ℝ) (θ : a.Param) (v : a.V) : a.NodeTensor v :=
  fun bi xv => ∑ x : a.Ext, a.residual Tstar θ x *
    a.represented (Function.update θ v (fun bi' xv' => if bi' = bi ∧ xv' = xv then 1 else 0)) x

/-- Splitting the node product of an updated parameter at the updated node.
Helper (same pattern as `hasDerivAt_represented_line`'s product fold). -/
theorem prod_update_eq_mul_erase (θ : a.Param) (v : a.V) (W' : a.NodeTensor v)
    (b : a.Bond) (x : a.Ext) :
    (∏ z, Function.update θ v W' z (Bond.restrict b z) (x z))
      = W' (Bond.restrict b v) (x v)
        * ∏ z ∈ Finset.univ.erase v, θ z (Bond.restrict b z) (x z) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun z hz => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hz)]

open Classical in
/-- Linearity of the represented tensor in one node slot, expanded over the standard
basis of `NodeTensor v`. Helper for `pairing_eq_sum_gradNode`. -/
theorem represented_update_eq_sum_single (θ : a.Param) (v : a.V) (δ : a.NodeTensor v)
    (x : a.Ext) :
    a.represented (Function.update θ v δ) x
      = ∑ bi : a.BondIdx v, ∑ xv : Fin (a.n v), δ bi xv *
          a.represented (Function.update θ v
            (fun bi' xv' => if bi' = bi ∧ xv' = xv then 1 else 0)) x := by
  classical
  have hb : ∀ b : a.Bond,
      δ (Bond.restrict b v) (x v) = ∑ bi : a.BondIdx v, ∑ xv : Fin (a.n v),
        δ bi xv * (if Bond.restrict b v = bi ∧ x v = xv then (1 : ℝ) else 0) := by
    intro b
    simp [ite_and, mul_ite, Finset.sum_ite_eq]
  calc a.represented (Function.update θ v δ) x
      = ∑ b : a.Bond, δ (Bond.restrict b v) (x v)
          * ∏ z ∈ Finset.univ.erase v, θ z (Bond.restrict b z) (x z) := by
        simp only [represented]
        exact Finset.sum_congr rfl fun b _ => a.prod_update_eq_mul_erase θ v δ b x
    _ = ∑ b : a.Bond, ∑ bi : a.BondIdx v, ∑ xv : Fin (a.n v),
          δ bi xv * (if Bond.restrict b v = bi ∧ x v = xv then (1 : ℝ) else 0)
            * ∏ z ∈ Finset.univ.erase v, θ z (Bond.restrict b z) (x z) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hb b, Finset.sum_mul]
        exact Finset.sum_congr rfl fun bi _ => by rw [Finset.sum_mul]
    _ = ∑ bi : a.BondIdx v, ∑ xv : Fin (a.n v), δ bi xv *
          a.represented (Function.update θ v
            (fun bi' xv' => if bi' = bi ∧ xv' = xv then 1 else 0)) x := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun bi _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun xv _ => ?_
        simp only [represented]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [a.prod_update_eq_mul_erase θ v _ b x]
        exact mul_assoc _ _ _

/-- The variational pairing of `Critical` is the entrywise pairing against `gradNode`:
`⟨R, T(θ with W_v ← δ)⟩ = ⟨δ, ∇_{W_v} L⟩` (linearity of `T(update θ v ·)` in the slot). -/
theorem pairing_eq_sum_gradNode (Tstar : a.Ext → ℝ) (θ : a.Param) (v : a.V)
    (δ : a.NodeTensor v) :
    ∑ x : a.Ext, a.residual Tstar θ x * a.represented (Function.update θ v δ) x
      = ∑ bi : a.BondIdx v, ∑ xv : Fin (a.n v), δ bi xv * a.gradNode Tstar θ v bi xv := by
  classical
  simp only [gradNode]
  calc ∑ x : a.Ext, a.residual Tstar θ x * a.represented (Function.update θ v δ) x
      = ∑ x : a.Ext, ∑ bi : a.BondIdx v, ∑ xv : Fin (a.n v),
          δ bi xv * (a.residual Tstar θ x * a.represented (Function.update θ v
            (fun bi' xv' => if bi' = bi ∧ xv' = xv then 1 else 0)) x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [a.represented_update_eq_sum_single θ v δ x, Finset.mul_sum]
        refine Finset.sum_congr rfl fun bi _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun xv _ => by ring
    _ = ∑ bi : a.BondIdx v, ∑ xv : Fin (a.n v), δ bi xv *
          ∑ x : a.Ext, a.residual Tstar θ x * a.represented (Function.update θ v
            (fun bi' xv' => if bi' = bi ∧ xv' = xv then 1 else 0)) x := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun bi _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun xv _ => ?_
        rw [Finset.mul_sum]

/-- **`gradNode` is the gradient**: every line derivative of the loss (computed by
`hasDerivAt_loss_line`) is the pairing of the direction against `gradNode`. -/
theorem hasDerivAt_loss_line_gradNode (Tstar : a.Ext → ℝ) (θ η : a.Param) :
    HasDerivAt (fun t : ℝ => a.loss Tstar (fun v bi xv => θ v bi xv + t * η v bi xv))
      (∑ v, ∑ bi : a.BondIdx v, ∑ xv : Fin (a.n v),
        η v bi xv * a.gradNode Tstar θ v bi xv) 0 := by
  have h := a.hasDerivAt_loss_line Tstar θ η
  rwa [Finset.sum_congr rfl
    (fun v _ => a.pairing_eq_sum_gradNode Tstar θ v (η v))] at h

/-- `Critical` (Theorem 5.2's variational criticality) is exactly `∇L(θ) = 0` entrywise. -/
theorem critical_iff_gradNode_eq_zero (Tstar : a.Ext → ℝ) (θ : a.Param) :
    a.Critical Tstar θ ↔
      ∀ (v : a.V) (bi : a.BondIdx v) (xv : Fin (a.n v)),
        a.gradNode Tstar θ v bi xv = 0 := by
  constructor
  · intro hcrit v bi xv
    exact hcrit v _
  · intro hz v δ
    rw [a.pairing_eq_sum_gradNode Tstar θ v δ]
    exact Finset.sum_eq_zero fun bi _ => Finset.sum_eq_zero fun xv _ => by
      rw [hz v bi xv, mul_zero]

/-! ### Gradient flow -/

/-- **Gradient flow of the loss**, entrywise: each parameter entry is differentiable in
time with derivative the negated matching `gradNode` entry (`θ̇ = −∇L(θ)`). The flow is a
hypothesis (certified-flow style), not a construction; `hasDerivAt_loss_line_gradNode`
discharges the trust that the right-hand side is the gradient. -/
def IsGradFlow (Tstar : a.Ext → ℝ) (θ : ℝ → a.Param) : Prop :=
  ∀ (v : a.V) (bi : a.BondIdx v) (xv : Fin (a.n v)) (t : ℝ),
    HasDerivAt (fun s : ℝ => θ s v bi xv) (-(a.gradNode Tstar (θ t) v bi xv)) t

/-! ### The transfer identity (the crux; no tree property) -/

/-- The edge `s(u, w)` as an element of the edge set. -/
abbrev adjEdge {u w : a.V} (h : a.G.Adj u w) : a.G.edgeSet :=
  ⟨s(u, w), by rw [SimpleGraph.mem_edgeSet]; exact h⟩

/-- Updating a global bond assignment at `s(u, w)` updates the restriction at the left
endpoint `u` at its incidence `adjIncLeft h`. -/
theorem restrict_update_adjLeft {u w : a.V} (h : a.G.Adj u w) (b : a.Bond)
    (k : Fin (a.r s(u, w))) :
    Bond.restrict (Function.update b (adjEdge h) k) u
      = Function.update (Bond.restrict b u) (adjIncLeft h) k := by
  funext e'
  by_cases he : e' = adjIncLeft h
  · subst he
    rw [Function.update_self]
    show Function.update b (adjEdge h) k (adjEdge h) = k
    rw [Function.update_self]
  · rw [Function.update_of_ne he]
    show Function.update b (adjEdge h) k ⟨e'.1, e'.2.1⟩ = b ⟨e'.1, e'.2.1⟩
    rw [Function.update_of_ne]
    intro hc
    have hval : (⟨e'.1, e'.2.1⟩ : a.G.edgeSet).1 = (adjEdge h).1 :=
      congrArg Subtype.val hc
    exact he (Subtype.ext hval)

/-- Updating a global bond assignment at `s(u, w)` updates the restriction at the right
endpoint `w` at its incidence `adjIncRight h`. -/
theorem restrict_update_adjRight {u w : a.V} (h : a.G.Adj u w) (b : a.Bond)
    (k : Fin (a.r s(u, w))) :
    Bond.restrict (Function.update b (adjEdge h) k) w
      = Function.update (Bond.restrict b w) (adjIncRight h) k := by
  funext e'
  by_cases he : e' = adjIncRight h
  · subst he
    rw [Function.update_self]
    show Function.update b (adjEdge h) k (adjEdge h) = k
    rw [Function.update_self]
  · rw [Function.update_of_ne he]
    show Function.update b (adjEdge h) k ⟨e'.1, e'.2.1⟩ = b ⟨e'.1, e'.2.1⟩
    rw [Function.update_of_ne]
    intro hc
    have hval : (⟨e'.1, e'.2.1⟩ : a.G.edgeSet).1 = (adjEdge h).1 :=
      congrArg Subtype.val hc
    exact he (Subtype.ext hval)

/-- Updating a global bond assignment at `s(u, w)` does not change the restriction at any
node `z` outside the edge. -/
theorem restrict_update_of_notMem {u w : a.V} (h : a.G.Adj u w) (b : a.Bond)
    (k : Fin (a.r s(u, w))) {z : a.V} (hzu : z ≠ u) (hzw : z ≠ w) :
    Bond.restrict (Function.update b (adjEdge h) k) z = Bond.restrict b z := by
  funext e'
  show Function.update b (adjEdge h) k ⟨e'.1, e'.2.1⟩ = b ⟨e'.1, e'.2.1⟩
  rw [Function.update_of_ne]
  intro hc
  have hz : z ∈ (adjEdge h).1 := by
    rw [← congrArg Subtype.val hc]; exact e'.2.2
  rcases Sym2.mem_iff.mp hz with hzu' | hzw'
  · exact hzu hzu'
  · exact hzw hzw'

/-- The self-inverse reindexing of `Bond × Fin r_e` that swaps the `e₀`-coordinate of the
bond assignment with the extra index. -/
noncomputable def bondSwap (e₀ : a.G.edgeSet) :
    a.Bond × Fin (a.r e₀.1) ≃ a.Bond × Fin (a.r e₀.1) where
  toFun p := (Function.update p.1 e₀ p.2, p.1 e₀)
  invFun p := (Function.update p.1 e₀ p.2, p.1 e₀)
  left_inv p := by
    refine Prod.ext ?_ ?_
    · show Function.update (Function.update p.1 e₀ p.2) e₀ (p.1 e₀) = p.1
      rw [Function.update_idem, Function.update_eq_self]
    · show Function.update p.1 e₀ p.2 e₀ = p.2
      rw [Function.update_self]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · show Function.update (Function.update p.1 e₀ p.2) e₀ (p.1 e₀) = p.1
      rw [Function.update_idem, Function.update_eq_self]
    · show Function.update p.1 e₀ p.2 e₀ = p.2
      rw [Function.update_self]

/-- Restriction at `u` evaluated at the left incidence is the global value at the edge. -/
theorem restrict_apply_adjLeft {u w : a.V} (h : a.G.Adj u w) (b : a.Bond) :
    Bond.restrict b u (adjIncLeft h) = b (adjEdge h) := rfl

/-- Restriction at `w` evaluated at the right incidence is the global value at the edge. -/
theorem restrict_apply_adjRight {u w : a.V} (h : a.G.Adj u w) (b : a.Bond) :
    Bond.restrict b w (adjIncRight h) = b (adjEdge h) := rfl

/-- **Transfer identity.** Inserting `M` on the `u`-side of the bond `e = s(u, w)` gives
the same represented tensor as inserting `Mᵀ` on the `w`-side: the bond index of `e` is
shared by exactly the two endpoint factors, so both sides are the same reindexed bond
sum. This is the per-bond `GL(r_e)` gauge structure of the contraction
and the only structural input to the conservation law — acyclicity is never used. -/
theorem represented_update_modeMul_transfer {u w : a.V} (h : a.G.Adj u w) (θ : a.Param)
    (M : Matrix (Fin (a.r s(u, w))) (Fin (a.r s(u, w))) ℝ) :
    a.represented (Function.update θ u (a.modeMul u (adjIncLeft h) M (θ u)))
      = a.represented (Function.update θ w (a.modeMul w (adjIncRight h) Mᵀ (θ w))) := by
  funext x
  have hwu : w ∈ Finset.univ.erase u :=
    Finset.mem_erase.mpr ⟨h.ne', Finset.mem_univ w⟩
  have huw : u ∈ Finset.univ.erase w :=
    Finset.mem_erase.mpr ⟨h.ne, Finset.mem_univ u⟩
  have hL : a.represented (Function.update θ u (a.modeMul u (adjIncLeft h) M (θ u))) x
      = ∑ p : a.Bond × Fin (a.r s(u, w)),
          M (p.1 (adjEdge h)) p.2
            * θ u (Bond.restrict (Function.update p.1 (adjEdge h) p.2) u) (x u)
            * (θ w (Bond.restrict p.1 w) (x w)
              * ∏ z ∈ (Finset.univ.erase u).erase w,
                  θ z (Bond.restrict p.1 z) (x z)) := by
    simp only [represented, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [a.prod_update_eq_mul_erase θ u _ b x,
      ← Finset.mul_prod_erase (Finset.univ.erase u) _ hwu]
    show (∑ k, M (Bond.restrict b u (adjIncLeft h)) k
          * θ u (Function.update (Bond.restrict b u) (adjIncLeft h) k) (x u))
        * (θ w (Bond.restrict b w) (x w)
          * ∏ z ∈ (Finset.univ.erase u).erase w, θ z (Bond.restrict b z) (x z)) = _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [restrict_update_adjLeft h b k, restrict_apply_adjLeft h b, mul_assoc]
  have hR : a.represented (Function.update θ w (a.modeMul w (adjIncRight h) Mᵀ (θ w))) x
      = ∑ p : a.Bond × Fin (a.r s(u, w)),
          Mᵀ (p.1 (adjEdge h)) p.2
            * θ w (Bond.restrict (Function.update p.1 (adjEdge h) p.2) w) (x w)
            * (θ u (Bond.restrict p.1 u) (x u)
              * ∏ z ∈ (Finset.univ.erase w).erase u,
                  θ z (Bond.restrict p.1 z) (x z)) := by
    simp only [represented, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [a.prod_update_eq_mul_erase θ w _ b x,
      ← Finset.mul_prod_erase (Finset.univ.erase w) _ huw]
    show (∑ k, Mᵀ (Bond.restrict b w (adjIncRight h)) k
          * θ w (Function.update (Bond.restrict b w) (adjIncRight h) k) (x w))
        * (θ u (Bond.restrict b u) (x u)
          * ∏ z ∈ (Finset.univ.erase w).erase u, θ z (Bond.restrict b z) (x z)) = _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [restrict_update_adjRight h b k, restrict_apply_adjRight h b, mul_assoc]
  rw [hL, hR]
  refine Fintype.sum_equiv (a.bondSwap (adjEdge h)) _ _ fun p => ?_
  simp only [bondSwap, Equiv.coe_fn_mk, Function.update_self, Function.update_idem,
    Function.update_eq_self, Matrix.transpose_apply]
  have hprod : ∏ z ∈ (Finset.univ.erase w).erase u,
      θ z (Bond.restrict (Function.update p.1 (adjEdge h) p.2) z) (x z)
    = ∏ z ∈ (Finset.univ.erase u).erase w, θ z (Bond.restrict p.1 z) (x z) := by
    rw [Finset.erase_right_comm]
    refine Finset.prod_congr rfl fun z hz => ?_
    have hzw : z ≠ w := (Finset.mem_erase.mp hz).1
    have hzu : z ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hz)).1
    rw [restrict_update_of_notMem h p.1 p.2 hzu hzw]
  rw [hprod]
  ring

/-- Gradient-pairing form of the transfer identity: pairing `modeMul M W_u` against
`∇_{W_u} L` equals pairing `modeMul Mᵀ W_w` against `∇_{W_w} L`. -/
theorem gradPair_modeMul_transfer {u w : a.V} (h : a.G.Adj u w) (Tstar : a.Ext → ℝ)
    (θ : a.Param) (M : Matrix (Fin (a.r s(u, w))) (Fin (a.r s(u, w))) ℝ) :
    ∑ bi : a.BondIdx u, ∑ xu : Fin (a.n u),
        a.modeMul u (adjIncLeft h) M (θ u) bi xu * a.gradNode Tstar θ u bi xu
      = ∑ bi : a.BondIdx w, ∑ xw : Fin (a.n w),
        a.modeMul w (adjIncRight h) Mᵀ (θ w) bi xw * a.gradNode Tstar θ w bi xw := by
  rw [← a.pairing_eq_sum_gradNode Tstar θ u (a.modeMul u (adjIncLeft h) M (θ u)),
    ← a.pairing_eq_sum_gradNode Tstar θ w (a.modeMul w (adjIncRight h) Mᵀ (θ w)),
    a.represented_update_modeMul_transfer h θ M]

/-! ### The bond Gram matrices and the conservation law -/

/-- The **bond Gram matrix** of a node tensor at an incident bond: `matₑ(W) matₑ(W)ᵀ`,
an `r_e × r_e` Gram over all non-`e` modes (physics convention `W₍ₑ₎ᵀ W₍ₑ₎`). -/
noncomputable def bondGram (v : a.V) (e : a.Inc v) (W : a.NodeTensor v) :
    Matrix (Fin (a.r e.1)) (Fin (a.r e.1)) ℝ :=
  a.matE v e W * (a.matE v e W)ᵀ

/-- The **conserved bond quantity** `Δ_e`: the difference of the two
endpoint bond Grams of the (oriented) edge `e = s(u, w)`. -/
noncomputable def bondGramDiff {u w : a.V} (h : a.G.Adj u w) (θ : a.Param) :
    Matrix (Fin (a.r s(u, w))) (Fin (a.r s(u, w))) ℝ :=
  a.bondGram u (adjIncLeft h) (θ u) - a.bondGram w (adjIncRight h) (θ w)

/-- Time derivative of one bond-Gram entry along the flow, in `matE` vocabulary
(product rule; the `matE` reindex commutes with `d/dt` entrywise). -/
theorem hasDerivAt_bondGram_entry (Tstar : a.Ext → ℝ) {θ : ℝ → a.Param}
    (hflow : a.IsGradFlow Tstar θ) (v : a.V) (e : a.Inc v) (i j : Fin (a.r e.1)) (t : ℝ) :
    HasDerivAt (fun s => a.bondGram v e (θ s v) i j)
      (-((∑ c, a.matE v e (a.gradNode Tstar (θ t) v) i c * a.matE v e (θ t v) j c)
        + ∑ c, a.matE v e (θ t v) i c * a.matE v e (a.gradNode Tstar (θ t) v) j c)) t := by
  have hentry : ∀ (i' : Fin (a.r e.1))
      (c : ((e' : {e' : a.Inc v // e' ≠ e}) → Fin (a.r e'.1.1)) × Fin (a.n v)),
      HasDerivAt (fun s => a.matE v e (θ s v) i' c)
        (-(a.matE v e (a.gradNode Tstar (θ t) v) i' c)) t := fun i' c =>
    hflow v ((Equiv.piSplitAt e fun e' => Fin (a.r e'.1)).symm (i', c.1)) c.2 t
  have heq : (fun s => a.bondGram v e (θ s v) i j)
      = fun s => ∑ c, a.matE v e (θ s v) i c * a.matE v e (θ s v) j c := by
    funext s
    simp [bondGram, Matrix.mul_apply, Matrix.transpose_apply]
  rw [heq]
  have h1 := HasDerivAt.fun_sum
    (fun c (_ : c ∈ Finset.univ) => (hentry i c).mul (hentry j c))
  have hval : (∑ c, (-(a.matE v e (a.gradNode Tstar (θ t) v) i c)
        * a.matE v e (θ t v) j c
      + a.matE v e (θ t v) i c * -(a.matE v e (a.gradNode Tstar (θ t) v) j c)))
      = -((∑ c, a.matE v e (a.gradNode Tstar (θ t) v) i c * a.matE v e (θ t v) j c)
        + ∑ c, a.matE v e (θ t v) i c * a.matE v e (a.gradNode Tstar (θ t) v) j c) := by
    rw [neg_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [← hval]
  exact h1

/-- Entry sums over a node tensor pair are computed by `matE` (the unfolding is an entry
bijection). -/
theorem sum_entries_eq_sum_matE (v : a.V) (e : a.Inc v) (F K : a.NodeTensor v) :
    ∑ bi : a.BondIdx v, ∑ xv : Fin (a.n v), F bi xv * K bi xv
      = ∑ k, ∑ c, a.matE v e F k c * a.matE v e K k c := by
  have h1 : ∑ bi : a.BondIdx v, ∑ xv : Fin (a.n v), F bi xv * K bi xv
      = ∑ p : Fin (a.r e.1) × ((e' : {e' : a.Inc v // e' ≠ e}) → Fin (a.r e'.1.1)),
          ∑ xv : Fin (a.n v),
            F ((Equiv.piSplitAt e fun e' => Fin (a.r e'.1)).symm p) xv
              * K ((Equiv.piSplitAt e fun e' => Fin (a.r e'.1)).symm p) xv :=
    Fintype.sum_equiv (Equiv.piSplitAt e fun e' => Fin (a.r e'.1)) _ _ fun bi => by
      rw [Equiv.symm_apply_apply]
  rw [h1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_prod_type]
  rfl

open Classical in
/-- Pairing `modeMul` by a single-entry matrix against another tensor picks one cross
term of the `matE` Gram. -/
theorem sum_modeMul_single_pair (v : a.V) (e : a.Inc v) (i j : Fin (a.r e.1))
    (W K : a.NodeTensor v) :
    ∑ bi : a.BondIdx v, ∑ xv : Fin (a.n v),
        a.modeMul v e (Matrix.single i j 1) W bi xv * K bi xv
      = ∑ c, a.matE v e W j c * a.matE v e K i c := by
  rw [a.sum_entries_eq_sum_matE v e _ K, a.matE_modeMul v e (Matrix.single i j 1) W,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_mul, zero_mul, one_mul,
    Finset.sum_ite_eq]

/-- The cross term of the `u`-side Gram derivative equals the `(j, i)` cross term of the
`w`-side Gram derivative (transfer identity at `M` = a single-entry matrix, read through
`matE_modeMul`). -/
theorem matE_cross_transfer {u w : a.V} (h : a.G.Adj u w) (Tstar : a.Ext → ℝ)
    (θ : a.Param) (i j : Fin (a.r s(u, w))) :
    ∑ c, a.matE u (adjIncLeft h) (a.gradNode Tstar θ u) i c
        * a.matE u (adjIncLeft h) (θ u) j c
      = ∑ c, a.matE w (adjIncRight h) (a.gradNode Tstar θ w) j c
          * a.matE w (adjIncRight h) (θ w) i c := by
  have hu := a.sum_modeMul_single_pair u (adjIncLeft h) i j (θ u) (a.gradNode Tstar θ u)
  have hw := a.sum_modeMul_single_pair w (adjIncRight h) j i (θ w) (a.gradNode Tstar θ w)
  have ht := a.gradPair_modeMul_transfer h Tstar θ (Matrix.single i j 1)
  rw [Matrix.transpose_single] at ht
  refine (Finset.sum_congr rfl fun c _ => mul_comm _ _).trans ?_
  rw [← hu, ht, hw]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

/-- **Per-bond conservation law.** Along any gradient flow of the
TTN squared loss, the bond quantity `Δ_e = matₑ(W_u)matₑ(W_u)ᵀ − matₑ(W_w)matₑ(W_w)ᵀ` is
a constant of motion, for every internal bond `e = s(u, w)`. Tree instance of Saxe's
DLN balancedness conservation; the proof uses only the per-bond gauge structure
(`represented_update_modeMul_transfer`), not acyclicity. -/
theorem bondGramDiff_conserved (Tstar : a.Ext → ℝ) {θ : ℝ → a.Param}
    (hflow : a.IsGradFlow Tstar θ) {u w : a.V} (h : a.G.Adj u w) (t : ℝ) :
    a.bondGramDiff h (θ t) = a.bondGramDiff h (θ 0) := by
  ext i j
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s' => a.bondGramDiff h (θ s') i j) 0 s := by
    intro s
    have hu := a.hasDerivAt_bondGram_entry Tstar hflow u (adjIncLeft h) i j s
    have hw := a.hasDerivAt_bondGram_entry Tstar hflow w (adjIncRight h) i j s
    have hsub := hu.sub hw
    have hA : (∑ c, a.matE u (adjIncLeft h) (a.gradNode Tstar (θ s) u) i c
          * a.matE u (adjIncLeft h) (θ s u) j c)
        = ∑ c, a.matE w (adjIncRight h) (θ s w) i c
            * a.matE w (adjIncRight h) (a.gradNode Tstar (θ s) w) j c :=
      (a.matE_cross_transfer h Tstar (θ s) i j).trans
        (Finset.sum_congr rfl fun c _ => mul_comm _ _)
    have hB : (∑ c, a.matE u (adjIncLeft h) (θ s u) i c
          * a.matE u (adjIncLeft h) (a.gradNode Tstar (θ s) u) j c)
        = ∑ c, a.matE w (adjIncRight h) (a.gradNode Tstar (θ s) w) i c
            * a.matE w (adjIncRight h) (θ s w) j c :=
      (Finset.sum_congr rfl fun c _ => mul_comm _ _).trans
        (a.matE_cross_transfer h Tstar (θ s) j i)
    rw [hA, hB, show ∀ x y : ℝ, -(x + y) - -(y + x) = 0 from fun x y => by ring] at hsub
    exact hsub
  exact is_const_of_deriv_eq_zero (fun s => (hderiv s).differentiableAt)
    (fun s => (hderiv s).deriv) t 0

/-- **The balanced slice is flow-invariant**: `Δ_e(0) = 0` propagates to all times
(the tree analogue of the balanced manifold in deep linear networks). -/
theorem bondGramDiff_eq_zero_of_balanced_init (Tstar : a.Ext → ℝ) {θ : ℝ → a.Param}
    (hflow : a.IsGradFlow Tstar θ) {u w : a.V} (h : a.G.Adj u w)
    (hbal : a.bondGramDiff h (θ 0) = 0) (t : ℝ) :
    a.bondGramDiff h (θ t) = 0 := by
  rw [a.bondGramDiff_conserved Tstar hflow h t, hbal]

/-- A vector is in the kernel of `Aᵀ` iff it is isotropic for the Gram matrix `A Aᵀ`
(over `ℝ`). -/
theorem transpose_mulVec_eq_zero_iff {n' m' : Type*} [Fintype n'] [Fintype m']
    (A : Matrix n' m' ℝ) (d : n' → ℝ) :
    Aᵀ *ᵥ d = 0 ↔ d ⬝ᵥ (A * Aᵀ) *ᵥ d = 0 := by
  rw [show d ⬝ᵥ (A * Aᵀ) *ᵥ d = (Aᵀ *ᵥ d) ⬝ᵥ (Aᵀ *ᵥ d) from by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]]
  exact dotProduct_self_eq_zero.symm

/-- **Shared bond kernel on the balanced slice**: under balanced initialisation, at every
time the two endpoint tensors annihilate the same bond directions — the kernels of the
two `e`-mode unfoldings coincide (`matₑ(W)ᵀ *ᵥ d` is the paper's `matₑ(W) · d`; cf. the
dormant-subspace definition). Kernel time-constancy is not claimed here. -/
theorem bondKernel_iff_of_balanced (Tstar : a.Ext → ℝ) {θ : ℝ → a.Param}
    (hflow : a.IsGradFlow Tstar θ) {u w : a.V} (h : a.G.Adj u w)
    (hbal : a.bondGramDiff h (θ 0) = 0) (t : ℝ) (d : Fin (a.r s(u, w)) → ℝ) :
    (a.matE u (adjIncLeft h) (θ t u))ᵀ *ᵥ d = 0 ↔
      (a.matE w (adjIncRight h) (θ t w))ᵀ *ᵥ d = 0 := by
  have hgram : a.bondGram u (adjIncLeft h) (θ t u)
      = a.bondGram w (adjIncRight h) (θ t w) :=
    sub_eq_zero.mp (a.bondGramDiff_eq_zero_of_balanced_init Tstar hflow h hbal t)
  rw [transpose_mulVec_eq_zero_iff (a.matE u (adjIncLeft h) (θ t u)) d,
    transpose_mulVec_eq_zero_iff (a.matE w (adjIncRight h) (θ t w)) d]
  show d ⬝ᵥ a.bondGram u (adjIncLeft h) (θ t u) *ᵥ d = 0 ↔
    d ⬝ᵥ a.bondGram w (adjIncRight h) (θ t w) *ᵥ d = 0
  rw [hgram]

end Arch

end TTN
