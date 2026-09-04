import TTN.Landscape.Descent
import TTN.Landscape.Criticality
import TTN.Landscape.EnvRank
import TTN.Landscape.SignFlip

/-!
# No spurious local minima at minimum-norm points

**every local minimum of `L` that is a minimum-norm point is a global minimum with `L = 0`**
(for a realizable target — the paper's standing assumption, made explicit as in Theorem 5.2).

The proof has three cases:
* `T* = 0` branch: min-norm + critical alone force `T(θ) = 0` (the funnel identity gives
  `D_e = ⊤`, so the rank count gives `rank T⁽ᵉ⁾ = 0` at any edge).
* Full-model-rank branch: `IsLocalMin → Critical` (`critical_of_isLocalMin`),
  `fullTuckerRank_of_minNorm_of_rank_eq`, then **Theorem 5.2**.
* Deficient branch: compress to the target cut ranks, choose a connected deficient
  component, prove that its environment pairing is nonzero, choose its sign, and apply the
  component-supported power-law descent from `CoreDescent.lean`.
-/

namespace TTN

namespace Arch

variable {a : Arch}

/-- **Paper correspondence: Theorem 4.3, minimum-norm local minima are global,
zero-residual form.** A minimum-norm local minimum of the loss for a
realizable target represents the target exactly. -/
theorem minNorm_isLocalMin_represented_eq {Tstar : a.Ext → ℝ} (hreal : a.Realizable Tstar)
    {θ : a.Param} (hmn : a.MinNorm θ) (hloc : IsLocalMin (a.loss Tstar) θ) :
    a.represented θ = Tstar := by
  classical
  have hcrit : a.Critical Tstar θ := a.critical_of_isLocalMin hloc
  by_cases hfull : ∀ (u w : a.V) (h : a.G.Adj u w), (a.matricize h θ).rank = a.r s(u, w)
  · -- Branch 1 (incl. the single-node case, where the hypothesis is vacuous):
    -- full model rank everywhere ⇒ full Tucker rank ⇒ Theorem 5.2.
    exact a.critical_fullRank_represented_eq hreal hcrit
      (a.fullTuckerRank_of_minNorm_of_rank_eq hmn hfull)
  · -- some edge is rank-deficient
    push Not at hfull
    obtain ⟨u, w, h, hdef⟩ := hfull
    by_cases hT0 : Tstar = 0
    · -- Branch 0: zero target — the funnel identity forces the model to vanish.
      subst hT0
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
    · -- Nonzero target with a deficient edge: reduce to full target rank, then apply
      -- the component-supported descent.
      obtain ⟨r', hr', ι, hortho, hsupp, hrealb, hTfullb⟩ :=
        a.exists_compress_reduction hreal hT0 hmn hcrit
      set b := a.reDim r' hr' with hb0
      set ψ := a.compressParam (hr' := hr') ι θ with hψ0
      have hrepb : b.represented ψ = a.represented θ :=
        a.represented_compressParam ι hortho hsupp
      have hmnb : b.MinNorm ψ := a.minNorm_compressParam ι hortho hsupp hmn
      have hlocb : IsLocalMin (b.loss Tstar) ψ :=
        a.isLocalMin_compressParam ι hortho hsupp hloc
      have hcritb : b.Critical Tstar ψ := b.critical_of_isLocalMin hlocb
      by_cases hbfull : ∀ (us ws : b.V) (hbe : b.G.Adj us ws),
          (b.matricize hbe ψ).rank = b.r s(us, ws)
      · -- every reduced edge full model rank: Theorem 5.2 at the reduced problem
        have hftr := b.fullTuckerRank_of_minNorm_of_rank_eq hmnb hbfull
        have hrepT := b.critical_fullRank_represented_eq hrealb hcritb hftr
        rw [← hrepb]
        exact hrepT
      · -- a deficient reduced edge: component + environment pairing + descent
        push Not at hbfull
        obtain ⟨us, ws, hbe, hdefb'⟩ := hbfull
        have hdefb : (b.matricize hbe ψ).rank < b.r s(us, ws) :=
          lt_of_le_of_ne (b.matricize_rank_le hbe ψ) hdefb'
        obtain ⟨S, K, η, husS, heK, h3, h4, h5, h6, hη, hunit, hconn⟩ :=
          b.exists_deficient_component hmnb hbe hdefb
        have hwsS : ws ∈ S := h3 _ heK ws (Sym2.mem_mk_right us ws)
        have hKiff : ∀ E : b.G.edgeSet, E ∈ K ↔ b.EdgeInside S E :=
          fun E => ⟨fun hE v hv => h3 E hE v hv, h4 E⟩
        obtain ⟨ξ, β, hne⟩ := b.exists_envPair_ne_zero hmnb hcritb hrealb hTfullb
          S K hKiff h6 hconn hbe husS hwsS hdefb
        set G := b.Gind S ξ β with hGdef
        have hpair := b.pair_residual_Gind Tstar ψ S K η hKiff hunit ξ β
        have hcne : (∑ x, b.residual Tstar ψ x
            * b.represented (S.piecewise (b.corePerturb K η G) ψ) x) ≠ 0 := by
          rw [hGdef, hpair]
          exact hne
        have hN : 1 ≤ S.card := Finset.card_pos.mpr ⟨us, husS⟩
        have hG0 : ∀ v ∉ S, ∀ (bi : b.BondIdx v) (xv : Fin (b.n v)), G v bi xv = 0 :=
          fun v hv bi xv => b.Gind_apply_of_notMem S ξ β hv bi xv
        have hGind : ∀ (v : b.V) (e : b.Inc v),
            (⟨e.1, e.2.1⟩ : b.G.edgeSet) ∈ K →
            ∀ (bi : b.BondIdx v) (k : Fin (b.r e.1)) (xv : Fin (b.n v)),
              G v (Function.update bi e k) xv = G v bi xv :=
          fun v e heK' bi k xv =>
            b.Gind_update_of_edgeInside S ξ β e ((hKiff ⟨e.1, e.2.1⟩).mp heK') bi k xv
        rcases lt_or_gt_of_ne hcne with hneg | hpos
        · -- the pairing is already negative: descend with G
          exact (b.not_isLocalMin_of_pow_move Tstar ψ (b.corePerturb K η G) hN _
            (fun t => b.represented_add_corePerturb ψ S K η G hη hG0 hGind hconn
              ⟨us, husS⟩ t)
            hneg hlocb).elim
        · -- positive pairing: negate the free tensor at `us` and descend
          set G' := Function.update G us (fun bi xv => - G us bi xv) with hG'def
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
          exact (b.not_isLocalMin_of_pow_move Tstar ψ (b.corePerturb K η G') hN _
            (fun t => b.represented_add_corePerturb ψ S K η G' hη hG0' hGind' hconn
              ⟨us, husS⟩ t)
            hRU' hlocb).elim

/-- **Paper correspondence: Theorem 4.3, minimum-norm local minima are global.**
Every minimum-norm local minimum is a global minimum, with zero loss. -/
theorem minNorm_isLocalMin_isGlobalMin {Tstar : a.Ext → ℝ} (hreal : a.Realizable Tstar)
    {θ : a.Param} (hmn : a.MinNorm θ) (hloc : IsLocalMin (a.loss Tstar) θ) :
    a.IsGlobalMin Tstar θ ∧ a.loss Tstar θ = 0 := by
  have hrep := a.minNorm_isLocalMin_represented_eq hreal hmn hloc
  have hzero : a.loss Tstar θ = 0 := by
    simp only [loss, hrep, sub_self]
    simp
  constructor
  · intro θ'
    rw [hzero]
    have hnn : (0 : ℝ) ≤ ∑ x : a.Ext, (a.represented θ' x - Tstar x) ^ 2 :=
      Finset.sum_nonneg fun x _ => sq_nonneg _
    show (0 : ℝ) ≤ (1 / 2) * ∑ x : a.Ext, (a.represented θ' x - Tstar x) ^ 2
    positivity
  · exact hzero

end Arch

end TTN
