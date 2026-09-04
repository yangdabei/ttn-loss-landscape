import TTN.Landscape.Dormant

/-!
# Coordinated dormant perturbations and strict descent

The two main results are stated on an arbitrary architecture whose every internal edge
carries a chosen dormant direction:

* `represented_add_dormant_perturb`: with a unit dormant direction `η_E` on
  every internal edge and an arbitrary external vector `u_v` at every node, the coordinated
  perturbation `W_v ← W_v + t·(⊗_e η_e) ⊗ u_v` moves the represented tensor by exactly
  `t^N · ⊗_v u_v` (`N = |V|`): every mixed term dies because a boundary edge of the perturbed
  set emits a dormant direction into an unperturbed node.
* `exists_loss_lt_of_inner_neg`: if moreover `⟨R, ⊗u⟩ < 0`, the loss strictly
  decreases along the perturbation for all sufficiently small `t > 0`
  (`L(t) − L(0) = t^N⟨R,U⟩ + ½t^{2N}‖U‖²`).

Dormancy here is stated **un-orientedly and cast-free**: `η : (E : G.edgeSet) → Fin (r E) → ℝ`
with `(matE v e (θ v))ᵀ *ᵥ η ⟨e.1, e.2.1⟩ = 0` for every node `v` and incidence `e` — i.e.
every endpoint unfolding kills its edge's direction. At a min-norm point this is equivalent to
`η_E ∈ D_E` by the minimum-norm kernel identities, but the descent results need only this
raw endpoint-annihilation property.

Key infrastructure:
* `prod_inc_eq_prod_edge_sq` — regrouping a product over all incidences as a product over
  edges with multiplicity two (each internal edge has exactly two endpoints).
* `exists_boundary_adj` — a nonempty proper vertex set of a connected graph has a boundary
  edge (drives the mixed-term vanishing).
-/

open scoped Matrix

namespace TTN

namespace Arch

variable {a : Arch}

/-- The coordinated dormant perturbation: at each node, the rank-one tensor
that emits `η_E` on every incident bond and `u_v` on the external mode. -/
noncomputable def dormantPerturb (η : (E : a.G.edgeSet) → Fin (a.r E.1) → ℝ)
    (uvec : (v : a.V) → Fin (a.n v) → ℝ) (v : a.V) : a.NodeTensor v :=
  fun bi xv => (∏ e : a.Inc v, η ⟨e.1, e.2.1⟩ (bi e)) * uvec v xv

/-- **A nonempty proper vertex set of a connected graph has a boundary edge.** -/
theorem exists_boundary_adj {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hconn : G.Connected) (S : Finset V) (hS : S.Nonempty) (hSc : S ≠ Finset.univ) :
    ∃ p q, p ∈ S ∧ q ∉ S ∧ G.Adj p q := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨p₀, hp₀⟩ := hS
  obtain ⟨q₀, hq₀⟩ : ∃ q, q ∉ S := by
    by_contra hall
    push Not at hall
    exact hSc (Finset.eq_univ_iff_forall.mpr hall)
  obtain ⟨W⟩ := hconn.preconnected p₀ q₀
  have hclosed : ∀ {x y : V}, G.Walk x y → x ∈ S → y ∈ S := by
    intro x y W
    induction W with
    | nil => exact id
    | cons hadj _ ih =>
      intro hx
      apply ih
      by_contra hy
      exact hcon _ _ hx hy hadj
  exact hq₀ (hclosed W hp₀)

/-- **Incidence-product regrouping**: a product of an edge-function over all incidences of all
nodes is the product over edges with multiplicity two (each edge of a simple graph has exactly
two endpoints). -/
theorem prod_inc_eq_prod_edge_sq (g : a.G.edgeSet → ℝ) :
    (∏ v : a.V, ∏ e : a.Inc v, g ⟨e.1, e.2.1⟩) = ∏ E : a.G.edgeSet, (g E) ^ 2 := by
  classical
  have hnode : ∀ v : a.V, (∏ e : a.Inc v, g ⟨e.1, e.2.1⟩)
      = ∏ E : a.G.edgeSet, (if v ∈ E.1 then g E else 1) := by
    intro v
    let eqv : a.Inc v ≃ {E : a.G.edgeSet // v ∈ E.1} :=
      { toFun := fun e => ⟨⟨e.1, e.2.1⟩, e.2.2⟩
        invFun := fun E => ⟨E.1.1, E.1.2, E.2⟩
        left_inv := fun e => rfl
        right_inv := fun E => rfl }
    calc (∏ e : a.Inc v, g ⟨e.1, e.2.1⟩)
        = ∏ E : {E : a.G.edgeSet // v ∈ E.1}, g E.1 :=
          Equiv.prod_comp eqv (fun E : {E : a.G.edgeSet // v ∈ E.1} => g E.1)
      _ = ∏ E ∈ Finset.univ.filter (fun E : a.G.edgeSet => v ∈ E.1), g E :=
          (Finset.prod_subtype _ (fun E => by simp) g).symm
      _ = ∏ E : a.G.edgeSet, (if v ∈ E.1 then g E else 1) := Finset.prod_filter _ g
  rw [Finset.prod_congr rfl (fun v _ => hnode v), Finset.prod_comm]
  refine Finset.prod_congr rfl (fun E _ => ?_)
  rw [← Finset.prod_filter, Finset.prod_const]
  congr 1
  obtain ⟨E, hE⟩ := E
  induction E using Sym2.ind with
  | _ p q =>
    rw [SimpleGraph.mem_edgeSet] at hE
    rw [show Finset.univ.filter (fun v : a.V => v ∈ s(p, q)) = {p, q} from by
      ext v
      simp [Sym2.mem_iff]]
    exact Finset.card_pair hE.ne

/-! ### Bond-slot bookkeeping for the `piSplitAt`-split bond sum -/

/-- An incidence of a node away from both endpoints of `s(u, w)` is not the cut edge. -/
theorem inc_ne_cutEdge {u w : a.V} (hpq : a.G.Adj u w) {v : a.V}
    (hvu : v ≠ u) (hvw : v ≠ w) (e' : a.Inc v) :
    (⟨e'.1, e'.2.1⟩ : a.G.edgeSet) ≠ a.cutEdge hpq := by
  intro hc
  have hvin : v ∈ e'.1 := e'.2.2
  rw [show e'.1 = s(u, w) from congrArg Subtype.val hc, Sym2.mem_iff] at hvin
  exact hvin.elim hvu hvw

/-- An incidence of the right endpoint other than the cut incidence is not the cut edge. -/
theorem inc_ne_cutEdge_of_ne_right {u w : a.V} (hpq : a.G.Adj u w) (e' : a.Inc w)
    (hne : e' ≠ adjIncRight hpq) :
    (⟨e'.1, e'.2.1⟩ : a.G.edgeSet) ≠ a.cutEdge hpq := fun hc => by
  have hv := congrArg Subtype.val hc
  exact hne (Subtype.ext hv)

/-- An incidence of the left endpoint other than the cut incidence is not the cut edge. -/
theorem inc_ne_cutEdge_of_ne_left {u w : a.V} (hpq : a.G.Adj u w) (e' : a.Inc u)
    (hne : e' ≠ adjIncLeft hpq) :
    (⟨e'.1, e'.2.1⟩ : a.G.edgeSet) ≠ a.cutEdge hpq := fun hc => by
  have hv := congrArg Subtype.val hc
  exact hne (Subtype.ext hv)

/-- The cut slot of the split bond assignment, read at the left endpoint. -/
theorem restrict_piSplitAt_cut_left {u w : a.V} (hpq : a.G.Adj u w)
    (k : Fin (a.r s(u, w)))
    (rest : (E : {E : a.G.edgeSet // E ≠ a.cutEdge hpq}) → Fin (a.r E.1.1)) :
    Bond.restrict ((Equiv.piSplitAt (a.cutEdge hpq) (fun E => Fin (a.r E.1))).symm (k, rest)) u
      (adjIncLeft hpq) = k := by
  show ((Equiv.piSplitAt (a.cutEdge hpq) (fun E => Fin (a.r E.1))).symm (k, rest))
      (a.cutEdge hpq) = k
  exact piSplitAt_symm_apply_self _ _ _

/-- The cut slot of the split bond assignment, read at the right endpoint. -/
theorem restrict_piSplitAt_cut_right {u w : a.V} (hpq : a.G.Adj u w)
    (k : Fin (a.r s(u, w)))
    (rest : (E : {E : a.G.edgeSet // E ≠ a.cutEdge hpq}) → Fin (a.r E.1.1)) :
    Bond.restrict ((Equiv.piSplitAt (a.cutEdge hpq) (fun E => Fin (a.r E.1))).symm (k, rest)) w
      (adjIncRight hpq) = k := by
  show ((Equiv.piSplitAt (a.cutEdge hpq) (fun E => Fin (a.r E.1))).symm (k, rest))
      (a.cutEdge hpq) = k
  exact piSplitAt_symm_apply_self _ _ _

/-- A non-cut slot of the split bond assignment is independent of the cut value. -/
theorem restrict_piSplitAt_slot_ne {u w : a.V} (hpq : a.G.Adj u w) {v : a.V} (e' : a.Inc v)
    (hne : (⟨e'.1, e'.2.1⟩ : a.G.edgeSet) ≠ a.cutEdge hpq) (k k' : Fin (a.r s(u, w)))
    (rest : (E : {E : a.G.edgeSet // E ≠ a.cutEdge hpq}) → Fin (a.r E.1.1)) :
    Bond.restrict ((Equiv.piSplitAt (a.cutEdge hpq) (fun E => Fin (a.r E.1))).symm (k, rest)) v e'
      = Bond.restrict
          ((Equiv.piSplitAt (a.cutEdge hpq) (fun E => Fin (a.r E.1))).symm (k', rest)) v e' := by
  show ((Equiv.piSplitAt (a.cutEdge hpq) (fun E => Fin (a.r E.1))).symm (k, rest)) ⟨e'.1, e'.2.1⟩
    = ((Equiv.piSplitAt (a.cutEdge hpq) (fun E => Fin (a.r E.1))).symm (k', rest)) ⟨e'.1, e'.2.1⟩
  rw [Equiv.piSplitAt_symm_apply, Equiv.piSplitAt_symm_apply, dif_neg hne, dif_neg hne]

/-- Away from both endpoints, the whole restricted bond assignment is independent of the cut
value. -/
theorem restrict_piSplitAt_k_indep {u w : a.V} (hpq : a.G.Adj u w) {v : a.V}
    (hvu : v ≠ u) (hvw : v ≠ w) (k k' : Fin (a.r s(u, w)))
    (rest : (E : {E : a.G.edgeSet // E ≠ a.cutEdge hpq}) → Fin (a.r E.1.1)) :
    Bond.restrict ((Equiv.piSplitAt (a.cutEdge hpq) (fun E => Fin (a.r E.1))).symm (k, rest)) v
      = Bond.restrict
          ((Equiv.piSplitAt (a.cutEdge hpq) (fun E => Fin (a.r E.1))).symm (k', rest)) v := by
  funext e'
  exact a.restrict_piSplitAt_slot_ne hpq e' (a.inc_ne_cutEdge hpq hvu hvw e') k k' rest

/-- **Bond-sum Fubini**: the sum over all bond assignments of an edgewise product is the
product over edges of the per-edge sums. -/
theorem sum_bond_prod_edge (f : (E : a.G.edgeSet) → Fin (a.r E.1) → ℝ) :
    (∑ b : a.Bond, ∏ E : a.G.edgeSet, f E (b E)) = ∏ E : a.G.edgeSet, ∑ k, f E k := by
  classical
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rfl

/-- **Mixed-term vanishing.** If every internal edge carries a unit direction
`η_E` killed by both endpoint unfoldings, then the coordinated perturbation by
`t · dormantPerturb η u` moves the represented tensor by exactly `t^{|V|} · ⊗_v u_v`. -/
theorem represented_add_dormant_perturb (θ : a.Param)
    (η : (E : a.G.edgeSet) → Fin (a.r E.1) → ℝ)
    (hη : ∀ (v : a.V) (e : a.Inc v), (a.matE v e (θ v))ᵀ *ᵥ η ⟨e.1, e.2.1⟩ = 0)
    (hunit : ∀ E : a.G.edgeSet, η E ⬝ᵥ η E = 1)
    (uvec : (v : a.V) → Fin (a.n v) → ℝ) (t : ℝ) :
    a.represented (fun v bi xv => θ v bi xv + t * a.dormantPerturb η uvec v bi xv)
      = fun x => a.represented θ x + t ^ (Fintype.card a.V) * ∏ v, uvec v (x v) := by
  classical
  haveI : Nonempty a.V := a.hT.connected.nonempty
  funext x
  show (∑ b : a.Bond, ∏ v, (θ v (Bond.restrict b v) (x v)
      + t * a.dormantPerturb η uvec v (Bond.restrict b v) (x v)))
    = a.represented θ x + t ^ (Fintype.card a.V) * ∏ v, uvec v (x v)
  rw [Finset.sum_congr rfl (fun b _ => Finset.prod_add
      (fun v => θ v (Bond.restrict b v) (x v))
      (fun v => t * a.dormantPerturb η uvec v (Bond.restrict b v) (x v)) Finset.univ),
    Finset.sum_comm]
  -- the `S = univ` term is the unperturbed tensor
  have hGuniv : (∑ b : a.Bond,
      (∏ v ∈ Finset.univ, θ v (Bond.restrict b v) (x v))
        * ∏ v ∈ Finset.univ \ Finset.univ,
            t * a.dormantPerturb η uvec v (Bond.restrict b v) (x v))
      = a.represented θ x := by
    simp only [Finset.sdiff_self, Finset.prod_empty, mul_one]
    rfl
  -- the `S = ∅` term is exactly `t^N · ⊗u`
  have hGempty : (∑ b : a.Bond,
      (∏ v ∈ (∅ : Finset a.V), θ v (Bond.restrict b v) (x v))
        * ∏ v ∈ Finset.univ \ (∅ : Finset a.V),
            t * a.dormantPerturb η uvec v (Bond.restrict b v) (x v))
      = t ^ (Fintype.card a.V) * ∏ v, uvec v (x v) := by
    simp only [Finset.prod_empty, one_mul, Finset.sdiff_empty]
    have hone : ∀ b : a.Bond,
        (∏ v, t * a.dormantPerturb η uvec v (Bond.restrict b v) (x v))
        = t ^ (Fintype.card a.V)
          * ((∏ E : a.G.edgeSet, (η E (b E)) ^ 2) * ∏ v, uvec v (x v)) := by
      intro b
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      congr 1
      show (∏ v, (∏ e : a.Inc v, η ⟨e.1, e.2.1⟩ (Bond.restrict b v e)) * uvec v (x v)) = _
      rw [Finset.prod_mul_distrib]
      congr 1
      exact a.prod_inc_eq_prod_edge_sq (fun E => η E (b E))
    rw [Finset.sum_congr rfl (fun b _ => hone b), ← Finset.mul_sum]
    congr 1
    rw [← Finset.sum_mul, a.sum_bond_prod_edge (fun E k => (η E k) ^ 2)]
    rw [show (∏ E : a.G.edgeSet, ∑ k, (η E k) ^ 2) = 1 from ?_, one_mul]
    calc (∏ E : a.G.edgeSet, ∑ k, (η E k) ^ 2)
        = ∏ E : a.G.edgeSet, (1 : ℝ) := by
          refine Finset.prod_congr rfl (fun E _ => ?_)
          rw [← hunit E]
          exact Finset.sum_congr rfl (fun k _ => pow_two (η E k))
      _ = 1 := Finset.prod_const_one
  -- every mixed term vanishes across a boundary edge of the perturbed set
  have hGzero : ∀ S ∈ (Finset.univ : Finset a.V).powerset,
      S ∉ ({Finset.univ, ∅} : Finset (Finset a.V)) →
      (∑ b : a.Bond, (∏ v ∈ S, θ v (Bond.restrict b v) (x v))
        * ∏ v ∈ Finset.univ \ S,
            t * a.dormantPerturb η uvec v (Bond.restrict b v) (x v)) = 0 := by
    intro S _ hSnot
    rw [Finset.mem_insert, Finset.mem_singleton] at hSnot
    push Not at hSnot
    obtain ⟨hSuniv, hSne⟩ := hSnot
    obtain ⟨y, z, hyS, hzS, hyz⟩ := exists_boundary_adj a.hT.connected S hSne hSuniv
    have hzSd : z ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzS⟩
    set k₀ : Fin (a.r s(y, z)) := ⟨0, a.hr s(y, z)
      (by rw [SimpleGraph.mem_edgeSet]; exact hyz)⟩ with hk₀
    -- reindex the bond sum across the boundary edge
    set F : a.Bond → ℝ := fun b => (∏ v ∈ S, θ v (Bond.restrict b v) (x v))
      * ∏ v ∈ Finset.univ \ S,
          t * a.dormantPerturb η uvec v (Bond.restrict b v) (x v) with hF
    have hreindex : (∑ b : a.Bond, F b)
        = ∑ rest : (E : {E : a.G.edgeSet // E ≠ a.cutEdge hyz}) → Fin (a.r E.1.1),
            ∑ k : Fin (a.r s(y, z)),
              F ((Equiv.piSplitAt (a.cutEdge hyz)
                (fun E => Fin (a.r E.1))).symm (k, rest)) := by
      calc (∑ b : a.Bond, F b)
          = ∑ pr : Fin (a.r s(y, z))
              × ((E : {E : a.G.edgeSet // E ≠ a.cutEdge hyz}) → Fin (a.r E.1.1)),
              F ((Equiv.piSplitAt (a.cutEdge hyz)
                (fun E => Fin (a.r E.1))).symm (pr.1, pr.2)) :=
            (Fintype.sum_equiv
              ((Equiv.piSplitAt (a.cutEdge hyz) (fun E => Fin (a.r E.1))).symm)
              _ _ (fun pr => rfl)).symm
        _ = ∑ k : Fin (a.r s(y, z)),
              ∑ rest : (E : {E : a.G.edgeSet // E ≠ a.cutEdge hyz}) → Fin (a.r E.1.1),
              F ((Equiv.piSplitAt (a.cutEdge hyz)
                (fun E => Fin (a.r E.1))).symm (k, rest)) := Fintype.sum_prod_type _
        _ = ∑ rest, ∑ k, F ((Equiv.piSplitAt (a.cutEdge hyz)
                (fun E => Fin (a.r E.1))).symm (k, rest)) := Finset.sum_comm
    rw [hreindex]
    refine Finset.sum_eq_zero (fun rest _ => ?_)
    set bk : Fin (a.r s(y, z)) → a.Bond := fun k =>
      (Equiv.piSplitAt (a.cutEdge hyz) (fun E => Fin (a.r E.1))).symm (k, rest) with hbk
    -- factor the S-product at `y` and the complement product at `z`
    have hSsplit : ∀ k, (∏ v ∈ S, θ v (Bond.restrict (bk k) v) (x v))
        = θ y (Bond.restrict (bk k) y) (x y)
          * ∏ v ∈ S.erase y, θ v (Bond.restrict (bk k₀) v) (x v) := by
      intro k
      rw [← Finset.mul_prod_erase S _ hyS]
      congr 1
      refine Finset.prod_congr rfl (fun v hv => ?_)
      have hvy : v ≠ y := Finset.ne_of_mem_erase hv
      have hvz : v ≠ z := fun hc => hzS (hc ▸ (Finset.mem_of_mem_erase hv))
      rw [hbk]
      rw [a.restrict_piSplitAt_k_indep hyz hvy hvz k k₀ rest]
    have hCsplit : ∀ k, (∏ v ∈ Finset.univ \ S,
          t * a.dormantPerturb η uvec v (Bond.restrict (bk k) v) (x v))
        = (t * a.dormantPerturb η uvec z (Bond.restrict (bk k) z) (x z))
          * ∏ v ∈ (Finset.univ \ S).erase z,
              t * a.dormantPerturb η uvec v (Bond.restrict (bk k₀) v) (x v) := by
      intro k
      rw [← Finset.mul_prod_erase _ _ hzSd]
      congr 1
      refine Finset.prod_congr rfl (fun v hv => ?_)
      have hvz : v ≠ z := Finset.ne_of_mem_erase hv
      have hvy : v ≠ y := fun hc =>
        (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hv)).2 (hc ▸ hyS)
      rw [hbk]
      rw [a.restrict_piSplitAt_k_indep hyz hvy hvz k k₀ rest]
    -- the `z`-factor emits `η` on the cut slot
    have hzfac : ∀ k, a.dormantPerturb η uvec z (Bond.restrict (bk k) z) (x z)
        = η (a.cutEdge hyz) k
          * ((∏ e ∈ (Finset.univ : Finset (a.Inc z)).erase (adjIncRight hyz),
              η ⟨e.1, e.2.1⟩ (Bond.restrict (bk k₀) z e)) * uvec z (x z)) := by
      intro k
      show (∏ e : a.Inc z, η ⟨e.1, e.2.1⟩ (Bond.restrict (bk k) z e)) * uvec z (x z) = _
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (adjIncRight hyz))]
      have hrest' : (∏ e ∈ (Finset.univ : Finset (a.Inc z)).erase (adjIncRight hyz),
            η ⟨e.1, e.2.1⟩ (Bond.restrict (bk k) z e))
          = ∏ e ∈ (Finset.univ : Finset (a.Inc z)).erase (adjIncRight hyz),
              η ⟨e.1, e.2.1⟩ (Bond.restrict (bk k₀) z e) := by
        refine Finset.prod_congr rfl (fun e he => ?_)
        rw [hbk]
        rw [a.restrict_piSplitAt_slot_ne hyz e
          (a.inc_ne_cutEdge_of_ne_right hyz e (Finset.ne_of_mem_erase he)) k k₀ rest]
      have hslot : Bond.restrict (bk k) z (adjIncRight hyz) = k := by
        rw [hbk]
        exact a.restrict_piSplitAt_cut_right hyz k rest
      rw [hrest', hslot]
      ring
    -- assemble: the k-sum is the paired contraction `(matE y)ᵀ η`, which vanishes
    have hfin : (∑ k, F (bk k))
        = (∑ k, θ y (Bond.restrict (bk k) y) (x y) * η (a.cutEdge hyz) k)
          * ((∏ v ∈ S.erase y, θ v (Bond.restrict (bk k₀) v) (x v))
            * ((t * ((∏ e ∈ (Finset.univ : Finset (a.Inc z)).erase (adjIncRight hyz),
                  η ⟨e.1, e.2.1⟩ (Bond.restrict (bk k₀) z e)) * uvec z (x z)))
              * ∏ v ∈ (Finset.univ \ S).erase z,
                  t * a.dormantPerturb η uvec v (Bond.restrict (bk k₀) v) (x v))) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hF]
      show (∏ v ∈ S, θ v (Bond.restrict (bk k) v) (x v))
          * (∏ v ∈ Finset.univ \ S,
              t * a.dormantPerturb η uvec v (Bond.restrict (bk k) v) (x v)) = _
      rw [hSsplit k, hCsplit k, hzfac k]
      ring
    have hker : (∑ k, θ y (Bond.restrict (bk k) y) (x y) * η (a.cutEdge hyz) k) = 0 := by
      have hsplitAtY : ∀ k, Bond.restrict (bk k) y
          = (Equiv.piSplitAt (adjIncLeft hyz) (fun e' => Fin (a.r e'.1))).symm
              (k, fun e' => Bond.restrict (bk k₀) y e'.1) := by
        intro k
        funext e'
        by_cases he' : e' = adjIncLeft hyz
        · subst he'
          rw [piSplitAt_symm_apply_self, hbk]
          exact a.restrict_piSplitAt_cut_left hyz k rest
        · rw [Equiv.piSplitAt_symm_apply, dif_neg he', hbk]
          exact a.restrict_piSplitAt_slot_ne hyz e'
            (a.inc_ne_cutEdge_of_ne_left hyz e' he') k k₀ rest
      have h0 := congrFun (hη y (adjIncLeft hyz))
        ((fun e' => Bond.restrict (bk k₀) y e'.1, x y))
      rw [Pi.zero_apply] at h0
      calc (∑ k, θ y (Bond.restrict (bk k) y) (x y) * η (a.cutEdge hyz) k)
          = ∑ k, a.matE y (adjIncLeft hyz) (θ y) k
              (fun e' => Bond.restrict (bk k₀) y e'.1, x y) * η (a.cutEdge hyz) k := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [hsplitAtY k]
            rfl
        _ = 0 := h0
    show (∑ k, F (bk k)) = 0
    rw [hfin, hker, zero_mul]
  -- put the three cases together
  rw [← Finset.sum_subset
      (show ({Finset.univ, ∅} : Finset (Finset a.V)) ⊆ (Finset.univ : Finset a.V).powerset
        from fun S hS => by
          rw [Finset.mem_insert, Finset.mem_singleton] at hS
          rcases hS with rfl | rfl <;> simp)
      hGzero]
  rw [Finset.sum_insert (by
    simp only [Finset.mem_singleton]
    exact Finset.univ_nonempty.ne_empty), Finset.sum_singleton, hGuniv, hGempty]

/-- Quadratic expansion of the loss along an exact rank-one move of the represented tensor:
if `T(θ') = T(θ) + s·U`, then `L(θ') = L(θ) + s⟨R, U⟩ + ½s²‖U‖²`. -/
theorem loss_of_represented_add (Tstar : a.Ext → ℝ) (θ θp : a.Param) (s : ℝ)
    (Uf : a.Ext → ℝ)
    (hrep : a.represented θp = fun x => a.represented θ x + s * Uf x) :
    a.loss Tstar θp = a.loss Tstar θ + s * (∑ x, a.residual Tstar θ x * Uf x)
      + s ^ 2 * ((1 : ℝ) / 2 * ∑ x, (Uf x) ^ 2) := by
  have hx : ∀ x, (a.represented θp x - Tstar x) ^ 2
      = (a.residual Tstar θ x) ^ 2 + 2 * s * (a.residual Tstar θ x * Uf x)
        + s ^ 2 * (Uf x) ^ 2 := by
    intro x
    have hR : a.represented θ x = a.residual Tstar θ x + Tstar x := by
      show _ = (a.represented θ x - Tstar x) + Tstar x
      ring
    rw [congrFun hrep x, hR]
    ring
  show (1 / 2) * (∑ x, (a.represented θp x - Tstar x) ^ 2)
    = (1 / 2) * (∑ x, (a.represented θ x - Tstar x) ^ 2)
      + s * (∑ x, a.residual Tstar θ x * Uf x)
      + s ^ 2 * ((1 : ℝ) / 2 * ∑ x, (Uf x) ^ 2)
  rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hRR : (∑ x, (a.residual Tstar θ x) ^ 2)
      = ∑ x, (a.represented θ x - Tstar x) ^ 2 := rfl
  rw [hRR]
  ring

/-- **Strict local descent.** If additionally the residual pairs negatively with
`⊗_v u_v`, the loss strictly decreases along the perturbation for all small `t > 0`. -/
theorem exists_loss_lt_of_inner_neg (Tstar : a.Ext → ℝ) (θ : a.Param)
    (η : (E : a.G.edgeSet) → Fin (a.r E.1) → ℝ)
    (hη : ∀ (v : a.V) (e : a.Inc v), (a.matE v e (θ v))ᵀ *ᵥ η ⟨e.1, e.2.1⟩ = 0)
    (hunit : ∀ E : a.G.edgeSet, η E ⬝ᵥ η E = 1)
    (uvec : (v : a.V) → Fin (a.n v) → ℝ)
    (hRU : (∑ x, a.residual Tstar θ x * ∏ v, uvec v (x v)) < 0) :
    ∃ t₀ > (0 : ℝ), ∀ t : ℝ, 0 < t → t < t₀ →
      a.loss Tstar (fun v bi xv => θ v bi xv + t * a.dormantPerturb η uvec v bi xv)
        < a.loss Tstar θ := by
  classical
  haveI : Nonempty a.V := a.hT.connected.nonempty
  set Uf : a.Ext → ℝ := fun x => ∏ v, uvec v (x v) with hUf
  set c : ℝ := ∑ x, a.residual Tstar θ x * Uf x with hc
  set K : ℝ := (1 : ℝ) / 2 * ∑ x, (Uf x) ^ 2 with hK
  have hcneg : c < 0 := hRU
  have hKnn : 0 ≤ K := by
    rw [hK]
    have hnn : (0 : ℝ) ≤ ∑ x, (Uf x) ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
    linarith
  refine ⟨min 1 (-c / (K + 1)),
    lt_min one_pos (div_pos (neg_pos.mpr hcneg) (by linarith)), fun t ht htlt => ?_⟩
  have hN1 : 1 ≤ Fintype.card a.V := Fintype.card_pos
  have hs0 : (0 : ℝ) < t ^ (Fintype.card a.V) := pow_pos ht _
  have ht1 : t < 1 := lt_of_lt_of_le htlt (min_le_left _ _)
  have hsle : t ^ (Fintype.card a.V) ≤ t := by
    calc t ^ (Fintype.card a.V) ≤ t ^ 1 :=
        pow_le_pow_of_le_one (le_of_lt ht) (le_of_lt ht1) hN1
      _ = t := pow_one t
  have hslt : t ^ (Fintype.card a.V) < -c / (K + 1) :=
    lt_of_le_of_lt hsle (lt_of_lt_of_le htlt (min_le_right _ _))
  have hlt := a.loss_of_represented_add Tstar θ
    (fun v bi xv => θ v bi xv + t * a.dormantPerturb η uvec v bi xv)
    (t ^ (Fintype.card a.V)) Uf
    (a.represented_add_dormant_perturb θ η hη hunit uvec t)
  rw [hlt, ← hc, ← hK]
  have hs1 : t ^ (Fintype.card a.V) * (K + 1) < -c :=
    (lt_div_iff₀ (by linarith)).mp hslt
  nlinarith [mul_lt_mul_of_pos_left hs1 hs0, sq_nonneg (t ^ (Fintype.card a.V))]

end Arch

end TTN
