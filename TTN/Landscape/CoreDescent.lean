import TTN.Landscape.Descent
import TTN.Landscape.Criticality

/-!
# Component-supported core descent

Instead of stripping attached subtrees, the descent perturbation is applied **at the original
problem**, supported on the vertex set `S` of the rank-deficient component with dormant
directions `η_E` on the component edges `K`:

* `corePerturb K η G` — at each node the `K`-incident bond slots emit `η`, all remaining
  slots (non-core bonds and the external mode) carry an arbitrary tensor `G v` that is
  independent of the `K`-slots (`hGind`) and vanishes off `S` (`hG0`).
* `represented_add_corePerturb`: the perturbed tensor moves by
  exactly `t^{|S|} · represented (S.piecewise (corePerturb …) θ)`; mixed terms die across a
  `K`-edge leaving the perturbed subset (`hconn`, instantiated later by the connectivity of
  the deficient component).
* `exists_loss_lt_of_pow_move`: any perturbation moving the
  tensor by `t^N·U` with `⟨R, U⟩ < 0` descends for small `t > 0`.
* `not_isLocalMin_of_pow_move` — the descent contradicts `IsLocalMin` along the continuous
  ray `t ↦ θ + t·δ`.
-/

open scoped Matrix

namespace TTN

namespace Arch

variable {a : Arch}

/-- The component-supported coordinated perturbation: on the
`K`-incident bond slots the node emits `η`; everything else is the free tensor `G v`. -/
noncomputable def corePerturb (K : Finset a.G.edgeSet)
    (η : (E : a.G.edgeSet) → Fin (a.r E.1) → ℝ)
    (G : (v : a.V) → a.NodeTensor v) (v : a.V) : a.NodeTensor v :=
  fun bi xv => (∏ e ∈ Finset.univ.filter
      (fun e : a.Inc v => (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ K), η ⟨e.1, e.2.1⟩ (bi e))
    * G v bi xv

/-- **Paper correspondence (stronger): Lemma E.8, mixed terms vanish under a coordinated
core perturbation.** This is the generalized component-supported form. If every
`K`-edge carries a direction `η_E` killed by the unfoldings of `θ` at BOTH endpoints, `G`
vanishes off `S` and ignores the `K`-slots, and every proper nonempty subset of `S` is left
by a `K`-edge (connectivity of the component), then the coordinated perturbation moves the
represented tensor by exactly `t^{|S|}` times the piecewise contraction. -/
theorem represented_add_corePerturb (θ : a.Param) (S : Finset a.V)
    (K : Finset a.G.edgeSet) (η : (E : a.G.edgeSet) → Fin (a.r E.1) → ℝ)
    (G : (v : a.V) → a.NodeTensor v)
    (hη : ∀ (v : a.V) (e : a.Inc v), (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ K →
      (a.matE v e (θ v))ᵀ *ᵥ η ⟨e.1, e.2.1⟩ = 0)
    (hG0 : ∀ v ∉ S, ∀ (bi : a.BondIdx v) (xv : Fin (a.n v)), G v bi xv = 0)
    (hGind : ∀ (v : a.V) (e : a.Inc v), (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ K →
      ∀ (bi : a.BondIdx v) (k : Fin (a.r e.1)) (xv : Fin (a.n v)),
        G v (Function.update bi e k) xv = G v bi xv)
    (hconn : ∀ P ⊆ S, P.Nonempty → P ≠ S →
      ∃ (y z : a.V) (hyz : a.G.Adj y z), y ∉ P ∧ z ∈ P ∧
        (⟨s(y, z), by rw [SimpleGraph.mem_edgeSet]; exact hyz⟩ : a.G.edgeSet) ∈ K)
    (hS : S.Nonempty) (t : ℝ) :
    a.represented (fun v bi xv => θ v bi xv + t * a.corePerturb K η G v bi xv)
      = fun x => a.represented θ x
        + t ^ S.card * a.represented (S.piecewise (a.corePerturb K η G) θ) x := by
  classical
  funext x
  show (∑ b : a.Bond, ∏ v, (θ v (Bond.restrict b v) (x v)
      + t * a.corePerturb K η G v (Bond.restrict b v) (x v)))
    = a.represented θ x
      + t ^ S.card * a.represented (S.piecewise (a.corePerturb K η G) θ) x
  rw [Finset.sum_congr rfl (fun b _ => Finset.prod_add
      (fun v => θ v (Bond.restrict b v) (x v))
      (fun v => t * a.corePerturb K η G v (Bond.restrict b v) (x v)) Finset.univ),
    Finset.sum_comm]
  -- the `Sθ = univ` (unperturbed) term is the represented tensor
  have hGuniv : (∑ b : a.Bond,
      (∏ v ∈ Finset.univ, θ v (Bond.restrict b v) (x v))
        * ∏ v ∈ Finset.univ \ Finset.univ,
            t * a.corePerturb K η G v (Bond.restrict b v) (x v))
      = a.represented θ x := by
    simp only [Finset.sdiff_self, Finset.prod_empty, mul_one]
    rfl
  -- the `Sθ = univ \ S` (fully perturbed on `S`) term is the piecewise leading term
  have hGlead : (∑ b : a.Bond,
      (∏ v ∈ Finset.univ \ S, θ v (Bond.restrict b v) (x v))
        * ∏ v ∈ Finset.univ \ (Finset.univ \ S),
            t * a.corePerturb K η G v (Bond.restrict b v) (x v))
      = t ^ S.card
        * a.represented (S.piecewise (a.corePerturb K η G) θ) x := by
    have hSS : Finset.univ \ (Finset.univ \ S) = S := by
      rw [Finset.sdiff_sdiff_self_left, Finset.univ_inter]
    rw [Finset.sum_congr rfl (fun b _ => by rw [hSS])]
    have hstep : ∀ b : a.Bond,
        (∏ v ∈ Finset.univ \ S, θ v (Bond.restrict b v) (x v))
          * ∏ v ∈ S, t * a.corePerturb K η G v (Bond.restrict b v) (x v)
        = t ^ S.card * ((∏ v ∈ S,
              a.corePerturb K η G v (Bond.restrict b v) (x v))
            * ∏ v ∈ Finset.univ \ S, θ v (Bond.restrict b v) (x v)) := by
      intro b
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      ring
    rw [Finset.sum_congr rfl (fun b _ => hstep b), ← Finset.mul_sum]
    congr 1
    show _ = ∑ b : a.Bond, ∏ v,
        S.piecewise (a.corePerturb K η G) θ v (Bond.restrict b v) (x v)
    refine (Finset.sum_congr rfl (fun b _ => ?_)).symm
    rw [show (∏ v, S.piecewise (a.corePerturb K η G) θ v (Bond.restrict b v) (x v))
        = ∏ v, S.piecewise
            (fun v => a.corePerturb K η G v (Bond.restrict b v) (x v))
            (fun v => θ v (Bond.restrict b v) (x v)) v from
      Finset.prod_congr rfl (fun v _ => by
        by_cases hv : v ∈ S
        · rw [Finset.piecewise_eq_of_mem _ _ _ hv, Finset.piecewise_eq_of_mem _ _ _ hv]
        · rw [Finset.piecewise_eq_of_notMem _ _ _ hv,
            Finset.piecewise_eq_of_notMem _ _ _ hv]),
      Finset.prod_piecewise, Finset.univ_inter]
  -- every other term vanishes
  have hGzero : ∀ Sθ ∈ (Finset.univ : Finset a.V).powerset,
      Sθ ∉ ({Finset.univ, Finset.univ \ S} : Finset (Finset a.V)) →
      (∑ b : a.Bond, (∏ v ∈ Sθ, θ v (Bond.restrict b v) (x v))
        * ∏ v ∈ Finset.univ \ Sθ,
            t * a.corePerturb K η G v (Bond.restrict b v) (x v)) = 0 := by
    intro Sθ _ hSnot
    rw [Finset.mem_insert, Finset.mem_singleton] at hSnot
    push Not at hSnot
    obtain ⟨hSuniv, hSlead⟩ := hSnot
    set P : Finset a.V := Finset.univ \ Sθ with hP
    by_cases hPS : P ⊆ S
    · -- perturbed part inside the component: mixed term, killed across a `K`-edge
      have hPne : P.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h0
        exact hSuniv (Finset.univ_subset_iff.mp
          (Finset.sdiff_eq_empty_iff_subset.mp h0))
      have hPneS : P ≠ S := by
        intro hPS'
        exact hSlead (by rw [← hPS', hP, Finset.sdiff_sdiff_self_left, Finset.univ_inter])
      obtain ⟨y, z, hyz, hyP, hzP, hcutK⟩ := hconn P hPS hPne hPneS
      have hyS : y ∈ Sθ := by
        by_contra hy
        exact hyP (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩)
      have hzSd : z ∈ Finset.univ \ Sθ := hzP
      set k₀ : Fin (a.r s(y, z)) := ⟨0, a.hr s(y, z)
        (by rw [SimpleGraph.mem_edgeSet]; exact hyz)⟩ with hk₀
      set F : a.Bond → ℝ := fun b => (∏ v ∈ Sθ, θ v (Bond.restrict b v) (x v))
        * ∏ v ∈ Finset.univ \ Sθ,
            t * a.corePerturb K η G v (Bond.restrict b v) (x v) with hF
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
      -- the `K`-membership of the two oriented cut incidences
      have hcutKl : (⟨(adjIncLeft hyz).1, (adjIncLeft hyz).2.1⟩ : a.G.edgeSet) ∈ K :=
        hcutK
      have hcutKr : (⟨(adjIncRight hyz).1, (adjIncRight hyz).2.1⟩ : a.G.edgeSet) ∈ K :=
        hcutK
      -- factor the `Sθ`-product at `y` and the complement product at `z`
      have hSsplit : ∀ k, (∏ v ∈ Sθ, θ v (Bond.restrict (bk k) v) (x v))
          = θ y (Bond.restrict (bk k) y) (x y)
            * ∏ v ∈ Sθ.erase y, θ v (Bond.restrict (bk k₀) v) (x v) := by
        intro k
        rw [← Finset.mul_prod_erase Sθ _ hyS]
        congr 1
        refine Finset.prod_congr rfl (fun v hv => ?_)
        have hvy : v ≠ y := Finset.ne_of_mem_erase hv
        have hvz : v ≠ z := fun hc => by
          have hmem := Finset.mem_of_mem_erase hv
          rw [hc] at hmem
          exact (Finset.mem_sdiff.mp hzSd).2 hmem
        rw [hbk]
        rw [a.restrict_piSplitAt_k_indep hyz hvy hvz k k₀ rest]
      have hCsplit : ∀ k, (∏ v ∈ Finset.univ \ Sθ,
            t * a.corePerturb K η G v (Bond.restrict (bk k) v) (x v))
          = (t * a.corePerturb K η G z (Bond.restrict (bk k) z) (x z))
            * ∏ v ∈ (Finset.univ \ Sθ).erase z,
                t * a.corePerturb K η G v (Bond.restrict (bk k₀) v) (x v) := by
        intro k
        rw [← Finset.mul_prod_erase _ _ hzSd]
        congr 1
        refine Finset.prod_congr rfl (fun v hv => ?_)
        have hvz : v ≠ z := Finset.ne_of_mem_erase hv
        have hvy : v ≠ y := fun hc => by
          have hmem := Finset.mem_of_mem_erase hv
          rw [hc] at hmem
          exact (Finset.mem_sdiff.mp hmem).2 hyS
        rw [hbk]
        rw [a.restrict_piSplitAt_k_indep hyz hvy hvz k k₀ rest]
      -- the `z`-restriction is a single-slot update of the `k₀`-restriction
      have hupdate : ∀ k, Bond.restrict (bk k) z
          = Function.update (Bond.restrict (bk k₀) z) (adjIncRight hyz) k := by
        intro k
        funext e
        by_cases he : e = adjIncRight hyz
        · subst he
          rw [Function.update_self, hbk]
          exact a.restrict_piSplitAt_cut_right hyz k rest
        · rw [Function.update_of_ne he, hbk]
          exact a.restrict_piSplitAt_slot_ne hyz e
            (a.inc_ne_cutEdge_of_ne_right hyz e he) k k₀ rest
      -- the `z`-factor emits `η` on the cut slot
      have hzfac : ∀ k, a.corePerturb K η G z (Bond.restrict (bk k) z) (x z)
          = η (a.cutEdge hyz) k
            * ((∏ e ∈ (Finset.univ.filter
                  (fun e : a.Inc z => (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ K)).erase
                  (adjIncRight hyz),
                η ⟨e.1, e.2.1⟩ (Bond.restrict (bk k₀) z e))
              * G z (Bond.restrict (bk k₀) z) (x z)) := by
        intro k
        show (∏ e ∈ Finset.univ.filter
            (fun e : a.Inc z => (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ K),
              η ⟨e.1, e.2.1⟩ (Bond.restrict (bk k) z e))
            * G z (Bond.restrict (bk k) z) (x z) = _
        have hcutmem : adjIncRight hyz ∈ Finset.univ.filter
            (fun e : a.Inc z => (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ K) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcutKr⟩
        rw [← Finset.mul_prod_erase _ _ hcutmem]
        have hrest' : (∏ e ∈ (Finset.univ.filter
              (fun e : a.Inc z => (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ K)).erase
              (adjIncRight hyz),
              η ⟨e.1, e.2.1⟩ (Bond.restrict (bk k) z e))
            = ∏ e ∈ (Finset.univ.filter
              (fun e : a.Inc z => (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ K)).erase
              (adjIncRight hyz),
                η ⟨e.1, e.2.1⟩ (Bond.restrict (bk k₀) z e) := by
          refine Finset.prod_congr rfl (fun e he => ?_)
          rw [hbk]
          rw [a.restrict_piSplitAt_slot_ne hyz e
            (a.inc_ne_cutEdge_of_ne_right hyz e (Finset.ne_of_mem_erase he)) k k₀ rest]
        have hslot : Bond.restrict (bk k) z (adjIncRight hyz) = k := by
          rw [hbk]
          exact a.restrict_piSplitAt_cut_right hyz k rest
        have hGz : G z (Bond.restrict (bk k) z) (x z)
            = G z (Bond.restrict (bk k₀) z) (x z) := by
          rw [hupdate k]
          exact hGind z (adjIncRight hyz) hcutKr (Bond.restrict (bk k₀) z) k (x z)
        rw [hrest', hslot, hGz]
        ring
      -- assemble: the k-sum is the paired contraction `(matE y)ᵀ η`, which vanishes
      have hfin : (∑ k, F (bk k))
          = (∑ k, θ y (Bond.restrict (bk k) y) (x y) * η (a.cutEdge hyz) k)
            * ((∏ v ∈ Sθ.erase y, θ v (Bond.restrict (bk k₀) v) (x v))
              * ((t * ((∏ e ∈ (Finset.univ.filter
                    (fun e : a.Inc z => (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ K)).erase
                    (adjIncRight hyz),
                    η ⟨e.1, e.2.1⟩ (Bond.restrict (bk k₀) z e))
                  * G z (Bond.restrict (bk k₀) z) (x z)))
                * ∏ v ∈ (Finset.univ \ Sθ).erase z,
                    t * a.corePerturb K η G v (Bond.restrict (bk k₀) v) (x v))) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hF]
        show (∏ v ∈ Sθ, θ v (Bond.restrict (bk k) v) (x v))
            * (∏ v ∈ Finset.univ \ Sθ,
                t * a.corePerturb K η G v (Bond.restrict (bk k) v) (x v)) = _
        rw [hSsplit k, hCsplit k, hzfac k]
        ring
      have hker : (∑ k, θ y (Bond.restrict (bk k) y) (x y) * η (a.cutEdge hyz) k)
          = 0 := by
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
        have h0 := congrFun (hη y (adjIncLeft hyz) hcutKl)
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
    · -- perturbed part leaves `S`: a zero factor from the support of `G`
      obtain ⟨v₀, hv₀P, hv₀S⟩ := Finset.not_subset.mp hPS
      refine Finset.sum_eq_zero (fun b _ => ?_)
      refine mul_eq_zero_of_right _ ?_
      refine Finset.prod_eq_zero (i := v₀) hv₀P ?_
      show t * a.corePerturb K η G v₀ (Bond.restrict b v₀) (x v₀) = 0
      have hzero : a.corePerturb K η G v₀ (Bond.restrict b v₀) (x v₀) = 0 := by
        show (∏ e ∈ Finset.univ.filter
            (fun e : a.Inc v₀ => (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ K),
              η ⟨e.1, e.2.1⟩ (Bond.restrict b v₀ e))
            * G v₀ (Bond.restrict b v₀) (x v₀) = 0
        rw [hG0 v₀ hv₀S (Bond.restrict b v₀) (x v₀), mul_zero]
      rw [hzero, mul_zero]
  -- put the three cases together
  rw [← Finset.sum_subset
      (show ({Finset.univ, Finset.univ \ S} : Finset (Finset a.V))
          ⊆ (Finset.univ : Finset a.V).powerset from fun Sθ hSθ => by
        rw [Finset.mem_insert, Finset.mem_singleton] at hSθ
        rcases hSθ with rfl | rfl <;> simp)
      hGzero]
  rw [Finset.sum_insert (by
    simp only [Finset.mem_singleton]
    intro hEq
    obtain ⟨s, hs⟩ := hS
    have hsmem := hEq ▸ Finset.mem_univ s
    exact (Finset.mem_sdiff.mp hsmem).2 hs), Finset.sum_singleton, hGuniv, hGlead]

/-- **Paper correspondence (stronger): Lemma E.9, strict local descent.**
This is the generalized pure-power-move form. Any perturbation direction that moves
the represented tensor by exactly `t^N·U` with `⟨R, U⟩ < 0` strictly decreases the loss for
all small `t > 0`. -/
theorem exists_loss_lt_of_pow_move (Tstar : a.Ext → ℝ) (θ : a.Param)
    (δ : (v : a.V) → a.NodeTensor v) {N : ℕ} (hN : 1 ≤ N) (Uf : a.Ext → ℝ)
    (hrep : ∀ t : ℝ, a.represented (fun v bi xv => θ v bi xv + t * δ v bi xv)
      = fun x => a.represented θ x + t ^ N * Uf x)
    (hRU : (∑ x, a.residual Tstar θ x * Uf x) < 0) :
    ∃ t₀ > (0 : ℝ), ∀ t : ℝ, 0 < t → t < t₀ →
      a.loss Tstar (fun v bi xv => θ v bi xv + t * δ v bi xv)
        < a.loss Tstar θ := by
  classical
  set c : ℝ := ∑ x, a.residual Tstar θ x * Uf x with hc
  set Kq : ℝ := (1 : ℝ) / 2 * ∑ x, (Uf x) ^ 2 with hK
  have hcneg : c < 0 := hRU
  have hKnn : 0 ≤ Kq := by
    rw [hK]
    have hnn : (0 : ℝ) ≤ ∑ x, (Uf x) ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
    linarith
  refine ⟨min 1 (-c / (Kq + 1)),
    lt_min one_pos (div_pos (neg_pos.mpr hcneg) (by linarith)), fun t ht htlt => ?_⟩
  have hs0 : (0 : ℝ) < t ^ N := pow_pos ht _
  have ht1 : t < 1 := lt_of_lt_of_le htlt (min_le_left _ _)
  have hsle : t ^ N ≤ t := by
    calc t ^ N ≤ t ^ 1 := pow_le_pow_of_le_one (le_of_lt ht) (le_of_lt ht1) hN
      _ = t := pow_one t
  have hL := a.loss_of_represented_add Tstar θ
    (fun v bi xv => θ v bi xv + t * δ v bi xv) (t ^ N) Uf (hrep t)
  rw [hL, ← hc, ← hK]
  have hbound : t ^ N * c + (t ^ N) ^ 2 * Kq < 0 := by
    have h2 : (t ^ N) ^ 2 * Kq ≤ t ^ N * (t ^ N * Kq) := by
      rw [pow_two]
      ring_nf
      exact le_refl _
    have h3 : t ^ N * Kq < -c := by
      have htK : t ^ N * Kq ≤ t * Kq := mul_le_mul_of_nonneg_right hsle hKnn
      have h4 : t * Kq < -c := by
        have h5 : t < -c / (Kq + 1) := lt_of_lt_of_le htlt (min_le_right _ _)
        have h6 : t * (Kq + 1) < -c := by
          rw [← lt_div_iff₀ (by linarith : (0 : ℝ) < Kq + 1)]
          exact h5
        nlinarith
      exact lt_of_le_of_lt htK h4
    nlinarith
  linarith

/-- **The descent contradicts local minimality**: no point admitting a `t^N`-move with
negatively paired direction is a local minimum of the loss. -/
theorem not_isLocalMin_of_pow_move (Tstar : a.Ext → ℝ) (θ : a.Param)
    (δ : (v : a.V) → a.NodeTensor v) {N : ℕ} (hN : 1 ≤ N) (Uf : a.Ext → ℝ)
    (hrep : ∀ t : ℝ, a.represented (fun v bi xv => θ v bi xv + t * δ v bi xv)
      = fun x => a.represented θ x + t ^ N * Uf x)
    (hRU : (∑ x, a.residual Tstar θ x * Uf x) < 0)
    (hloc : IsLocalMin (a.loss Tstar) θ) : False := by
  classical
  obtain ⟨t₀, ht₀, hdesc⟩ := a.exists_loss_lt_of_pow_move Tstar θ δ hN Uf hrep hRU
  have hline0 : (fun v bi xv => θ v bi xv + (0 : ℝ) * δ v bi xv : a.Param) = θ := by
    funext v bi xv; ring
  have hlift : IsLocalMin (a.loss Tstar)
      (fun v bi xv => θ v bi xv + (0 : ℝ) * δ v bi xv) := by
    rw [hline0]
    exact hloc
  have hloc' : IsLocalMin (fun t : ℝ => a.loss Tstar
      (fun v bi xv => θ v bi xv + t * δ v bi xv)) 0 :=
    IsLocalMin.comp_continuous (f := a.loss Tstar)
      (g := fun t : ℝ => (fun v bi xv => θ v bi xv + t * δ v bi xv : a.Param)) (b := 0)
      hlift (continuous_paramLine θ δ).continuousAt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hloc'
  set tval : ℝ := min (t₀ / 2) (ε / 2) with htval
  have htpos : 0 < tval := lt_min (by linarith) (by linarith)
  have htlt : tval < t₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htdist : dist tval (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hge := hball htdist
  simp only at hge
  have hf0 : a.loss Tstar (fun v bi xv => θ v bi xv + (0 : ℝ) * δ v bi xv)
      = a.loss Tstar θ := by rw [hline0]
  rw [hf0] at hge
  exact absurd hge (not_le.mpr (hdesc tval htpos htlt))

end Arch

end TTN
