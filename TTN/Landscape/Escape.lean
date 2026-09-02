import TTN.Landscape.LocalMin

/-!
# Escape paths conditional on in-fiber normalization

From any `θ₀` with `T(θ₀) ≠ T*`, `exists_escape_path` constructs a continuous path with
non-increasing loss ending strictly below `L(θ₀)`. The theorem assumes `hfiber` directly:
there is a continuous path in the fiber from `θ₀` to a minimum-norm representative. The
semialgebraic and geometric-invariant-theory arguments used in the paper to obtain this
property are outside the formalized scope.

* `mapParam_line` — `mapParam` is linear, so a reduced-problem ray pulls up to a ray.
* `exists_descent_data`: at any min-norm critical point that
  does not represent the (realizable) target, some direction moves the represented tensor
  by exactly `t^N·U` with `⟨R, U⟩ < 0`. (T* = 0 and full-model-rank cases are vacuous —
  they force `T(θ) = T*` — and the deficient case pulls the reduced data up.)
* `descent_ray_monotone` — the loss along such a ray is `L₀ + c·t^N + K·t^{2N}` with
  `c < 0`, hence MONOTONE non-increasing on an explicit interval with a strict drop.
* `exists_descent_data_of_not_critical`: at a non-critical point the same data with
  `N = 1`, using `represented_add_corePerturb` at `S = {v}` and `K = ∅`.
* `exists_escape_path` — Cor 4.4: concatenate the in-fiber path to the min-norm point
  (constant loss) with the descent ray.
-/

open scoped Matrix

namespace TTN

namespace Arch

variable {a : Arch}

/-- `mapParam` is affine along parameter rays (it is linear in the parameter). -/
theorem mapParam_line {r' : Sym2 a.V → ℕ} {hr' : ∀ e ∈ a.G.edgeSet, 0 < r' e}
    (ι : (E : a.G.edgeSet) → Matrix (Fin (r' E.1)) (Fin (a.r E.1)) ℝ)
    (ψ δ : (a.reDim r' hr').Param) (t : ℝ) :
    mapParam ι (fun v bi xv => ψ v bi xv + t * δ v bi xv)
      = fun v bi xv => mapParam ι ψ v bi xv + t * mapParam (hr' := hr') ι δ v bi xv := by
  funext v bi xv
  show (∑ bi' : (a.reDim r' hr').BondIdx v,
      (∏ e : (a.reDim r' hr').Inc v, ι ⟨e.1, e.2.1⟩ (bi' e) (bi (ofReDimInc e)))
        * (ψ v bi' xv + t * δ v bi' xv))
    = (∑ bi' : (a.reDim r' hr').BondIdx v,
        (∏ e : (a.reDim r' hr').Inc v, ι ⟨e.1, e.2.1⟩ (bi' e) (bi (ofReDimInc e))) * ψ v bi' xv)
      + t * ∑ bi' : (a.reDim r' hr').BondIdx v,
          (∏ e : (a.reDim r' hr').Inc v, ι ⟨e.1, e.2.1⟩ (bi' e) (bi (ofReDimInc e))) * δ v bi' xv
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun bi' _ => ?_)
  ring

/-- **The descent ray is monotone**: if the represented tensor moves by exactly `t^N·U`
with `c := ⟨R, U⟩ < 0`, the loss is non-increasing on an explicit interval `[0, T]` and
strictly lower at `T`. -/
theorem descent_ray_monotone (Tstar : a.Ext → ℝ) (θ : a.Param)
    (δ : (v : a.V) → a.NodeTensor v) {N : ℕ} (hN : 1 ≤ N) (Uf : a.Ext → ℝ)
    (hrep : ∀ t : ℝ, a.represented (fun v bi xv => θ v bi xv + t * δ v bi xv)
      = fun x => a.represented θ x + t ^ N * Uf x)
    (hRU : (∑ x, a.residual Tstar θ x * Uf x) < 0) :
    ∃ T > (0 : ℝ), (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        a.loss Tstar (fun v bi xv => θ v bi xv + t * δ v bi xv)
          ≤ a.loss Tstar (fun v bi xv => θ v bi xv + s * δ v bi xv)) ∧
      a.loss Tstar (fun v bi xv => θ v bi xv + T * δ v bi xv) < a.loss Tstar θ := by
  set c : ℝ := ∑ x, a.residual Tstar θ x * Uf x with hc
  set K : ℝ := (1 : ℝ) / 2 * ∑ x, (Uf x) ^ 2 with hK
  have hcneg : c < 0 := hRU
  have hKnn : 0 ≤ K := by
    have hnn : (0 : ℝ) ≤ ∑ x, (Uf x) ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
    rw [hK]; linarith
  set T : ℝ := min 1 (-c / (2 * (K + 1))) with hTdef
  have hTpos : 0 < T := lt_min one_pos (div_pos (neg_pos.mpr hcneg) (by linarith))
  have hT1 : T ≤ 1 := min_le_left _ _
  have hTdiv : T ≤ -c / (2 * (K + 1)) := min_le_right _ _
  have hTb : T * (2 * (K + 1)) ≤ -c :=
    (le_div_iff₀ (by linarith : (0 : ℝ) < 2 * (K + 1))).mp hTdiv
  have htTN : T ^ N ≤ T := by
    calc T ^ N ≤ T ^ 1 := pow_le_pow_of_le_one hTpos.le hT1 hN
      _ = T := pow_one T
  -- the loss along the ray is the quadratic `L₀ + s^N·c + (s^N)²·K`
  have hLval : ∀ s : ℝ, a.loss Tstar (fun v bi xv => θ v bi xv + s * δ v bi xv)
      = a.loss Tstar θ + s ^ N * c + (s ^ N) ^ 2 * K := by
    intro s
    rw [a.loss_of_represented_add Tstar θ (fun v bi xv => θ v bi xv + s * δ v bi xv)
      (s ^ N) Uf (hrep s), ← hc, ← hK]
  refine ⟨T, hTpos, fun s t hs hst htT => ?_, ?_⟩
  · -- monotone: `L(t) ≤ L(s)`
    rw [hLval t, hLval s]
    have hsN0 : (0 : ℝ) ≤ s ^ N := pow_nonneg hs N
    have hpq : s ^ N ≤ t ^ N := pow_le_pow_left₀ hs hst N
    have htN : t ^ N ≤ T ^ N := pow_le_pow_left₀ (hs.trans hst) htT N
    have htq : t ^ N ≤ T := htN.trans htTN
    have hsq : s ^ N ≤ T := hpq.trans htq
    have hfac : c + (t ^ N + s ^ N) * K ≤ 0 := by
      nlinarith [mul_le_mul_of_nonneg_right (show t ^ N + s ^ N ≤ 2 * T by linarith) hKnn,
        hTb, hTpos]
    have hqp0 : (0 : ℝ) ≤ t ^ N - s ^ N := sub_nonneg.mpr hpq
    have key : (t ^ N - s ^ N) * (c + (t ^ N + s ^ N) * K) ≤ 0 :=
      mul_nonpos_iff.mpr (Or.inl ⟨hqp0, hfac⟩)
    nlinarith [key]
  · -- strict drop at `T`
    rw [hLval T]
    have hTNpos : (0 : ℝ) < T ^ N := pow_pos hTpos N
    have hstrict : c + T ^ N * K < 0 := by
      nlinarith [mul_le_mul_of_nonneg_right htTN hKnn, hTb, hTpos,
        mul_nonneg hTpos.le hKnn]
    nlinarith [mul_pos hTNpos (neg_pos.mpr hstrict)]

/-- A minimum-norm critical point of a realizable target that
does not represent it admits a `t^N`-descent direction. -/
theorem exists_descent_data {Tstar : a.Ext → ℝ} (hreal : a.Realizable Tstar) {θ : a.Param}
    (hmn : a.MinNorm θ) (hcrit : a.Critical Tstar θ)
    (hne : a.represented θ ≠ Tstar) :
    ∃ (δ : (v : a.V) → a.NodeTensor v) (N : ℕ) (_ : 1 ≤ N) (Uf : a.Ext → ℝ),
      (∀ t : ℝ, a.represented (fun v bi xv => θ v bi xv + t * δ v bi xv)
        = fun x => a.represented θ x + t ^ N * Uf x) ∧
      (∑ x, a.residual Tstar θ x * Uf x) < 0 := by
  classical
  by_cases hfull : ∀ (u w : a.V) (h : a.G.Adj u w),
      (a.matricize h θ).rank = a.r s(u, w)
  · -- full model rank everywhere ⇒ Theorem 5.2 ⇒ represents the target, contradicting `hne`
    exact absurd (a.critical_fullRank_represented_eq hreal hcrit
      (a.fullTuckerRank_of_minNorm_of_rank_eq hmn hfull)) hne
  · push Not at hfull
    obtain ⟨u, w, h, hdef⟩ := hfull
    by_cases hT0 : Tstar = 0
    · -- zero target: the funnel identity forces `T(θ) = 0 = T*`, contradicting `hne`
      subst hT0
      have hrep0 : a.represented θ = 0 := by
        have hker := a.ker_matricizeOf_mul_Hfun_eq_dormant hmn hcrit h
        have hzero : a.matricizeOf h (0 : a.Ext → ℝ) * a.Hfun h θ = 0 := by
          have hz : a.matricizeOf h (0 : a.Ext → ℝ) = 0 := rfl
          rw [hz, Matrix.zero_mul]
        rw [hzero] at hker
        have htop : a.dormant h θ = ⊤ := by
          rw [← hker]
          ext d
          simp
        have hcount := a.minNorm_rank_add_finrank_dormant h hmn
        rw [htop, finrank_top] at hcount
        have hpi : Module.finrank ℝ (Fin (a.r s(u, w)) → ℝ) = a.r s(u, w) := by simp
        rw [hpi] at hcount
        have hrank0 : (a.matricize h θ).rank = 0 := by omega
        have hmat0 : a.matricize h θ = 0 := by
          have hr : Module.finrank ℝ (LinearMap.range (a.matricize h θ).mulVecLin) = 0 :=
            hrank0
          have hbot : LinearMap.range (a.matricize h θ).mulVecLin = ⊥ :=
            Submodule.finrank_eq_zero.mp hr
          ext i j
          have hcolz : (a.matricize h θ).col j = 0 := by
            have hmem : (a.matricize h θ).col j
                ∈ LinearMap.range (a.matricize h θ).mulVecLin :=
              ⟨Pi.single j 1, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]⟩
            rw [hbot, Submodule.mem_bot] at hmem
            exact hmem
          have hij := congrFun hcolz i
          simpa [Matrix.col_apply] using hij
        funext x
        have hx : a.represented θ x
            = a.matricize h θ (a.extSplit h x).1 (a.extSplit h x).2 := by
          show _ = a.represented θ ((a.extSplit h).symm ((a.extSplit h x).1, (a.extSplit h x).2))
          rw [Prod.mk.eta, Equiv.symm_apply_apply]
        rw [hx, hmat0]
        rfl
      exact absurd hrep0 hne
    · -- nonzero target with a deficient edge: compress, then pull the reduced data up
      obtain ⟨r', hr', ι, hortho, hsupp, hrealb, hTfullb⟩ :=
        a.exists_compress_reduction hreal hT0 hmn hcrit
      set b := a.reDim r' hr' with hb0
      set ψ := a.compressParam (hr' := hr') ι θ with hψ0
      have hrepb : b.represented ψ = a.represented θ :=
        a.represented_compressParam ι hortho hsupp
      have hmnb : b.MinNorm ψ := a.minNorm_compressParam ι hortho hsupp hmn
      have hcritb : b.Critical Tstar ψ := a.critical_compressParam ι hortho hsupp hcrit
      by_cases hbfull : ∀ (us ws : b.V) (hbe : b.G.Adj us ws),
          (b.matricize hbe ψ).rank = b.r s(us, ws)
      · -- reduced problem full model rank ⇒ Theorem 5.2 ⇒ `T(θ) = T*`, contradicting `hne`
        have hftr := b.fullTuckerRank_of_minNorm_of_rank_eq hmnb hbfull
        have hrepT := b.critical_fullRank_represented_eq hrealb hcritb hftr
        exact absurd (hrepb.symm.trans hrepT) hne
      · -- a deficient reduced edge: component + environment pairing + descent DATA
        push Not at hbfull
        obtain ⟨us, ws, hbe, hdefb'⟩ := hbfull
        have hdefb : (b.matricize hbe ψ).rank < b.r s(us, ws) :=
          lt_of_le_of_ne (b.matricize_rank_le hbe ψ) hdefb'
        obtain ⟨S, K, η, husS, heK, h3, h4, h5, h6, hη, hunit, hconn⟩ :=
          b.exists_deficient_component hmnb hbe hdefb
        have hwsS : ws ∈ S := h3 _ heK ws (Sym2.mem_mk_right us ws)
        have hKiff : ∀ E : b.G.edgeSet, E ∈ K ↔ b.EdgeInside S E :=
          fun E => ⟨fun hE v hv => h3 E hE v hv, h4 E⟩
        obtain ⟨ξ, β, hne'⟩ := b.exists_envPair_ne_zero hmnb hcritb hrealb hTfullb
          S K hKiff h6 hconn hbe husS hwsS hdefb
        set G := b.Gind S ξ β with hGdef
        have hpair := b.pair_residual_Gind Tstar ψ S K η hKiff hunit ξ β
        have hcne : (∑ x, b.residual Tstar ψ x
            * b.represented (S.piecewise (b.corePerturb K η G) ψ) x) ≠ 0 := by
          rw [hGdef, hpair]
          exact hne'
        have hN : 1 ≤ S.card := Finset.card_pos.mpr ⟨us, husS⟩
        have hG0 : ∀ v ∉ S, ∀ (bi : b.BondIdx v) (xv : Fin (b.n v)), G v bi xv = 0 :=
          fun v hv bi xv => b.Gind_apply_of_notMem S ξ β hv bi xv
        have hGind : ∀ (v : b.V) (e : b.Inc v),
            (⟨e.1, e.2.1⟩ : b.G.edgeSet) ∈ K →
            ∀ (bi : b.BondIdx v) (k : Fin (b.r e.1)) (xv : Fin (b.n v)),
              G v (Function.update bi e k) xv = G v bi xv :=
          fun v e heK' bi k xv =>
            b.Gind_update_of_edgeInside S ξ β e ((hKiff ⟨e.1, e.2.1⟩).mp heK') bi k xv
        -- downstairs descent data (independent of sign)
        obtain ⟨δ_b, Uf, hrep_b, hRU_b⟩ :
            ∃ (δ_b : (v : b.V) → b.NodeTensor v) (Uf : b.Ext → ℝ),
              (∀ t : ℝ, b.represented (fun v bi xv => ψ v bi xv + t * δ_b v bi xv)
                = fun x => b.represented ψ x + t ^ S.card * Uf x) ∧
              (∑ x, b.residual Tstar ψ x * Uf x) < 0 := by
          rcases lt_or_gt_of_ne hcne with hneg | hpos
          · exact ⟨b.corePerturb K η G,
              b.represented (S.piecewise (b.corePerturb K η G) ψ),
              fun t => b.represented_add_corePerturb ψ S K η G hη hG0 hGind hconn
                ⟨us, husS⟩ t, hneg⟩
          · set G' := Function.update G us (fun bi xv => - G us bi xv) with hG'def
            have hG0' : ∀ v ∉ S, ∀ (bi : b.BondIdx v) (xv : Fin (b.n v)),
                G' v bi xv = 0 := by
              intro v hv bi xv
              rw [hG'def, Function.update_of_ne (show v ≠ us from fun hc => hv (hc ▸ husS))]
              exact hG0 v hv bi xv
            have hGind' : ∀ (v : b.V) (e : b.Inc v),
                (⟨e.1, e.2.1⟩ : b.G.edgeSet) ∈ K →
                ∀ (bi : b.BondIdx v) (k : Fin (b.r e.1)) (xv : Fin (b.n v)),
                  G' v (Function.update bi e k) xv = G' v bi xv := by
              intro v e heK' bi k xv
              by_cases hv : v = us
              · subst hv
                rw [hG'def, Function.update_self]
                show - G v (Function.update bi e k) xv = - G v bi xv
                exact congrArg Neg.neg (hGind v e heK' bi k xv)
              · rw [hG'def, Function.update_of_ne hv]
                exact hGind v e heK' bi k xv
            have hUf' : b.represented (S.piecewise (b.corePerturb K η G') ψ)
                = fun x => - b.represented (S.piecewise (b.corePerturb K η G) ψ) x := by
              funext x
              rw [hG'def, b.piecewise_corePerturb_update_neg S K η G ψ husS,
                b.represented_update_neg (S.piecewise (b.corePerturb K η G) ψ) us
                  (b.corePerturb K η G us) x]
              congr 2
              funext v
              by_cases hv : v = us
              · subst hv
                rw [Function.update_self, S.piecewise_eq_of_mem _ _ husS]
              · rw [Function.update_of_ne hv]
            have hRU' : (∑ x, b.residual Tstar ψ x
                * b.represented (S.piecewise (b.corePerturb K η G') ψ) x) < 0 := by
              have hflip : (∑ x, b.residual Tstar ψ x
                  * b.represented (S.piecewise (b.corePerturb K η G') ψ) x)
                  = - ∑ x, b.residual Tstar ψ x
                      * b.represented (S.piecewise (b.corePerturb K η G) ψ) x := by
                simp only [hUf', mul_neg, Finset.sum_neg_distrib]
              rw [hflip]
              linarith
            exact ⟨b.corePerturb K η G',
              b.represented (S.piecewise (b.corePerturb K η G') ψ),
              fun t => b.represented_add_corePerturb ψ S K η G' hη hG0' hGind' hconn
                ⟨us, husS⟩ t, hRU'⟩
        -- pull the reduced data up along `mapParam ι`
        have hθ : mapParam (hr' := hr') ι ψ = θ := by
          rw [hψ0]; exact mapParam_compressParam ι hortho hsupp
        refine ⟨mapParam ι δ_b, S.card, hN, Uf, ?_, ?_⟩
        · intro t
          have hround : mapParam (hr' := hr') ι (fun v bi xv => ψ v bi xv + t * δ_b v bi xv)
              = fun v bi xv => θ v bi xv + t * mapParam (hr' := hr') ι δ_b v bi xv := by
            rw [mapParam_line ι ψ δ_b t, hθ]
          have hstep : a.represented (fun v bi xv => θ v bi xv + t * mapParam ι δ_b v bi xv)
              = b.represented (fun v bi xv => ψ v bi xv + t * δ_b v bi xv) := by
            rw [← hround, represented_mapParam ι hortho]
          rw [hstep, hrep_b t]
          funext x
          rw [hrepb]
        · have hres : ∀ x, a.residual Tstar θ x = b.residual Tstar ψ x := by
            intro x
            show a.represented θ x - Tstar x = b.represented ψ x - Tstar x
            rw [hrepb]
          have hsum : (∑ x, a.residual Tstar θ x * Uf x)
              = ∑ x, b.residual Tstar ψ x * Uf x :=
            Finset.sum_congr rfl (fun x _ => by rw [hres x])
          rw [hsum]; exact hRU_b

/-- **The non-critical descent**: a point that is not critical admits a first-order
(`N = 1`) descent direction. -/
theorem exists_descent_data_of_not_critical (Tstar : a.Ext → ℝ) {θ : a.Param}
    (hncrit : ¬ a.Critical Tstar θ) :
    ∃ (δ : (v : a.V) → a.NodeTensor v) (Uf : a.Ext → ℝ),
      (∀ t : ℝ, a.represented (fun v bi xv => θ v bi xv + t * δ v bi xv)
        = fun x => a.represented θ x + t ^ 1 * Uf x) ∧
      (∑ x, a.residual Tstar θ x * Uf x) < 0 := by
  classical
  simp only [Critical, not_forall] at hncrit
  obtain ⟨v, δv, hpair⟩ := hncrit
  -- pick the sign of the perturbation so the pairing is negative
  obtain ⟨w, hRUw⟩ : ∃ w : a.NodeTensor v,
      (∑ x, a.residual Tstar θ x * a.represented (Function.update θ v w) x) < 0 := by
    rcases lt_or_gt_of_ne hpair with hneg | hpos
    · exact ⟨δv, hneg⟩
    · refine ⟨fun bi xv => - δv bi xv, ?_⟩
      have hflip : ∀ x, a.represented (Function.update θ v (fun bi xv => - δv bi xv)) x
          = - a.represented (Function.update θ v δv) x :=
        fun x => a.represented_update_neg θ v δv x
      have hsum : (∑ x, a.residual Tstar θ x
            * a.represented (Function.update θ v (fun bi xv => - δv bi xv)) x)
          = - ∑ x, a.residual Tstar θ x * a.represented (Function.update θ v δv) x := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun x _ => by rw [hflip x]; ring)
      rw [hsum]; linarith
  -- the singleton-supported perturbation (`S = {v}`, `K = ∅`)
  set η0 : (E : a.G.edgeSet) → Fin (a.r E.1) → ℝ := fun _ _ => 0 with hη0
  set G : (z : a.V) → a.NodeTensor z :=
    Function.update (fun z => (fun _ _ => 0 : a.NodeTensor z)) v w with hGdef
  have hη : ∀ (z : a.V) (e : a.Inc z),
      (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ (∅ : Finset a.G.edgeSet) →
      (a.matE z e (θ z))ᵀ *ᵥ η0 ⟨e.1, e.2.1⟩ = 0 :=
    fun z e he => absurd he (Finset.notMem_empty _)
  have hG0 : ∀ z ∉ ({v} : Finset a.V), ∀ (bi : a.BondIdx z) (xv : Fin (a.n z)),
      G z bi xv = 0 := by
    intro z hz bi xv
    rw [hGdef, Function.update_of_ne (Finset.notMem_singleton.mp hz)]
  have hGind : ∀ (z : a.V) (e : a.Inc z),
      (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ (∅ : Finset a.G.edgeSet) →
      ∀ (bi : a.BondIdx z) (k : Fin (a.r e.1)) (xv : Fin (a.n z)),
        G z (Function.update bi e k) xv = G z bi xv :=
    fun z e he => absurd he (Finset.notMem_empty _)
  have hconn : ∀ P ⊆ ({v} : Finset a.V), P.Nonempty → P ≠ {v} →
      ∃ (y z : a.V) (hyz : a.G.Adj y z), y ∉ P ∧ z ∈ P ∧
        (⟨s(y, z), by rw [SimpleGraph.mem_edgeSet]; exact hyz⟩ : a.G.edgeSet)
          ∈ (∅ : Finset a.G.edgeSet) := by
    intro P hP hPne hPne'
    rcases Finset.subset_singleton_iff.mp hP with h | h
    · exact absurd h (Finset.nonempty_iff_ne_empty.mp hPne)
    · exact absurd h hPne'
  have hcp : ∀ (z : a.V) (bi : a.BondIdx z) (xv : Fin (a.n z)),
      a.corePerturb ∅ η0 G z bi xv = G z bi xv := by
    intro z bi xv
    show (∏ e ∈ Finset.univ.filter
        (fun e : a.Inc z => (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ (∅ : Finset a.G.edgeSet)),
          η0 ⟨e.1, e.2.1⟩ (bi e)) * G z bi xv = G z bi xv
    rw [Finset.filter_eq_empty_iff.mpr (fun e _ => Finset.notMem_empty _),
      Finset.prod_empty, one_mul]
  have hUfeq : ({v} : Finset a.V).piecewise (a.corePerturb ∅ η0 G) θ
      = Function.update θ v w := by
    funext z
    by_cases hz : z = v
    · subst hz
      rw [Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_singleton_self z),
        Function.update_self]
      funext bi xv
      rw [hcp z bi xv, hGdef, Function.update_self]
    · rw [Finset.piecewise_eq_of_notMem _ _ _ (Finset.notMem_singleton.mpr hz),
        Function.update_of_ne hz]
  refine ⟨a.corePerturb ∅ η0 G, a.represented (Function.update θ v w), ?_, hRUw⟩
  intro t
  rw [a.represented_add_corePerturb θ {v} ∅ η0 G hη hG0 hGind hconn
    ⟨v, Finset.mem_singleton_self v⟩ t, Finset.card_singleton, hUfeq]

/-- **Paper correspondence (conditional): Corollary 4.4, escape path from a non-solution.**
This version assumes the explicit in-fiber path hypothesis `hfiber`. Given a minimum-norm point
`θm` in `θ₀`'s fiber joined to `θ₀` by a
continuous in-fiber path, there is a continuous path starting at `θ₀` with non-increasing
loss that ends strictly below `L(θ₀)`. -/
theorem exists_escape_path {Tstar : a.Ext → ℝ} (hreal : a.Realizable Tstar)
    (θ₀ : a.Param) (hne : a.represented θ₀ ≠ Tstar)
    (hfiber : ∃ (θm : a.Param) (γ : ℝ → a.Param), Continuous γ ∧ γ 0 = θ₀ ∧ γ 1 = θm ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, a.represented (γ t) = a.represented θ₀) ∧ a.MinNorm θm) :
    ∃ δ : ℝ → a.Param, Continuous δ ∧ δ 0 = θ₀ ∧
      (∀ s t, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → s ≤ t →
        a.loss Tstar (δ t) ≤ a.loss Tstar (δ s)) ∧
      a.loss Tstar (δ 1) < a.loss Tstar θ₀ := by
  obtain ⟨θm, γ, hγc, hγ0, hγ1, hγfib, hmn⟩ := hfiber
  have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, le_refl _⟩
  have hnem : a.represented θm ≠ Tstar := by
    rw [← hγ1, hγfib 1 h1mem]; exact hne
  -- descent data at the min-norm fiber point
  obtain ⟨δd, N, hN, Uf, hrepd, hRU⟩ :
      ∃ (δd : (v : a.V) → a.NodeTensor v) (N : ℕ) (_ : 1 ≤ N) (Uf : a.Ext → ℝ),
        (∀ t : ℝ, a.represented (fun v bi xv => θm v bi xv + t * δd v bi xv)
          = fun x => a.represented θm x + t ^ N * Uf x) ∧
        (∑ x, a.residual Tstar θm x * Uf x) < 0 := by
    by_cases hcritm : a.Critical Tstar θm
    · exact a.exists_descent_data hreal hmn hcritm hnem
    · obtain ⟨δd, Uf, hrepc, hRUc⟩ := a.exists_descent_data_of_not_critical Tstar hcritm
      exact ⟨δd, 1, le_refl 1, Uf, hrepc, hRUc⟩
  obtain ⟨T, hTpos, hmono, hstrict⟩ := a.descent_ray_monotone Tstar θm δd hN Uf hrepd hRU
  -- the two path segments
  set f₁ : ℝ → a.Param := fun t => γ (2 * t) with hf1
  set f₂ : ℝ → a.Param :=
    fun t => (fun v bi xv => θm v bi xv + ((2 * t - 1) * T) * δd v bi xv) with hf2
  set δ : ℝ → a.Param := fun t => if t ≤ 1 / 2 then f₁ t else f₂ t with hδdef
  have hδeval : ∀ t : ℝ, δ t = if t ≤ 1 / 2 then f₁ t else f₂ t := fun t => rfl
  -- continuity
  have hcf1 : Continuous f₁ := by
    rw [hf1]; exact hγc.comp (continuous_const.mul continuous_id)
  have hcf2 : Continuous f₂ := by rw [hf2]; fun_prop
  have hjunc : ∀ t : ℝ, t = 1 / 2 → f₁ t = f₂ t := by
    intro t ht
    subst ht
    simp only [hf1, hf2]
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, hγ1]
    funext v bi xv
    ring
  have hcδ : Continuous δ :=
    Continuous.if_le hcf1 hcf2 continuous_id continuous_const hjunc
  -- constant-loss facts on the fiber segment
  have hlossγ : ∀ u ∈ Set.Icc (0 : ℝ) 1, a.loss Tstar (γ u) = a.loss Tstar θ₀ := by
    intro u hu
    show (1 / 2) * ∑ x, (a.represented (γ u) x - Tstar x) ^ 2
      = (1 / 2) * ∑ x, (a.represented θ₀ x - Tstar x) ^ 2
    rw [hγfib u hu]
  have hlossθm : a.loss Tstar θm = a.loss Tstar θ₀ := by
    rw [← hγ1]; exact hlossγ 1 h1mem
  have hlossleft : ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 2 → a.loss Tstar (δ u) = a.loss Tstar θ₀ := by
    intro u hu0 hu2
    rw [hδeval u, if_pos hu2]
    simp only [hf1]
    exact hlossγ (2 * u) ⟨by linarith, by linarith⟩
  have hlossright : ∀ u : ℝ, 1 / 2 < u → u ≤ 1 →
      a.loss Tstar (δ u) ≤ a.loss Tstar θ₀ := by
    intro u hu2 hu1
    rw [hδeval u, if_neg (not_le.mpr hu2)]
    simp only [hf2]
    have h0 : (0 : ℝ) ≤ (2 * u - 1) * T := mul_nonneg (by linarith) hTpos.le
    have hb : (2 * u - 1) * T ≤ T := mul_le_of_le_one_left hTpos.le (by linarith)
    have hkey := hmono 0 ((2 * u - 1) * T) (le_refl 0) h0 hb
    have hz : (fun v bi xv => θm v bi xv + (0 : ℝ) * δd v bi xv : a.Param) = θm := by
      funext v bi xv; ring
    rw [hz, hlossθm] at hkey
    exact hkey
  refine ⟨δ, hcδ, ?_, ?_, ?_⟩
  · -- `δ 0 = θ₀`
    rw [hδeval 0, if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    simp only [hf1]
    rw [show (2 : ℝ) * 0 = 0 by norm_num, hγ0]
  · -- non-increasing loss
    intro s t hs ht hst
    by_cases ht2 : t ≤ 1 / 2
    · have hs2 : s ≤ 1 / 2 := le_trans hst ht2
      exact le_of_eq (by rw [hlossleft t (hs.1.trans hst) ht2, hlossleft s hs.1 hs2])
    · push Not at ht2
      by_cases hs2 : s ≤ 1 / 2
      · rw [hlossleft s hs.1 hs2]
        exact hlossright t ht2 ht.2
      · push Not at hs2
        have ht1 : t ≤ 1 := ht.2
        rw [hδeval s, hδeval t, if_neg (not_le.mpr hs2), if_neg (not_le.mpr ht2)]
        simp only [hf2]
        have h0s : (0 : ℝ) ≤ (2 * s - 1) * T := mul_nonneg (by linarith) hTpos.le
        have hst' : (2 * s - 1) * T ≤ (2 * t - 1) * T :=
          mul_le_mul_of_nonneg_right (by linarith) hTpos.le
        have ht'T : (2 * t - 1) * T ≤ T := mul_le_of_le_one_left hTpos.le (by linarith)
        exact hmono ((2 * s - 1) * T) ((2 * t - 1) * T) h0s hst' ht'T
  · -- strict drop at `t = 1`
    have hd1 : δ 1 = fun v bi xv => θm v bi xv + T * δd v bi xv := by
      rw [hδeval 1, if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2)]
      simp only [hf2]
      funext v bi xv
      rw [show (2 : ℝ) * 1 - 1 = 1 by norm_num, one_mul]
    rw [hd1, ← hlossθm]
    exact hstrict

end Arch

end TTN
