import TTN.Landscape.ReDim
import TTN.Landscape.Criticality

/-!
# Compression to the target cut ranks

* `compressParam ι θ` — big → small: every bond mode contracted against `ι_E`.
* `SupportedOn ι θ` — the kernel form of "θ is supported on the chosen subspaces":
  every endpoint unfolding kills `ker ι_E`. At a min-norm point this follows from
  `ker ι_E ≤ D_E` via the minimum-norm kernel identities.
* `proj_mul_eq_of_supported` — the matrix heart: `(ιᵀι)·A = A` when `A`ᵀ kills `ker ι`
  (with `ι ιᵀ = 1`).
* `mapParam_compressParam`: the round-trip `mapParam ι (compressParam ι θ) = θ`
  on supported points (slot-by-slot induction, each step `proj_mul_eq_of_supported`
  applied to the `matE`-columns).
* Transfer results for full target rank (choice of `r'`), loss/norm equality,
  `MinNorm`, `Critical`, `IsLocalMin`.
-/

open scoped Matrix

namespace TTN

namespace Arch

variable {a : Arch} {r' : Sym2 a.V → ℕ} {hr' : ∀ e ∈ a.G.edgeSet, 0 < r' e}

/-- **Parameter compression along per-edge bond maps** (big → small): every bond mode of
every node tensor is contracted against its edge's `ι_E` (big index summed). -/
noncomputable def compressParam
    (ι : (E : a.G.edgeSet) → Matrix (Fin (r' E.1)) (Fin (a.r E.1)) ℝ)
    (θ : a.Param) : (a.reDim r' hr').Param :=
  fun v bi' xv => ∑ bi : a.BondIdx v,
    (∏ e : a.Inc v, ι ⟨e.1, e.2.1⟩ (bi' (toReDimInc e)) (bi e)) * θ v bi xv

/-- **Support, kernel form**: every endpoint unfolding of `θ` kills the kernel of its
edge's `ι`. At a minimum-norm point, this follows from `ker ι_E ≤ dormant` and the
kernel identities. -/
def SupportedOn (ι : (E : a.G.edgeSet) → Matrix (Fin (r' E.1)) (Fin (a.r E.1)) ℝ)
    (θ : a.Param) : Prop :=
  ∀ (v : a.V) (e : a.Inc v) (d : Fin (a.r e.1) → ℝ),
    ι ⟨e.1, e.2.1⟩ *ᵥ d = 0 → (a.matE v e (θ v))ᵀ *ᵥ d = 0

/-- **The projection identity**: if `ι` has orthonormal rows and `Aᵀ` kills `ker ι`, then
`(ιᵀι)·A = A`. -/
theorem proj_mul_eq_of_supported {s r : ℕ} {ι : Matrix (Fin s) (Fin r) ℝ}
    (hortho : ι * ιᵀ = 1) {C : Type*} [Fintype C] {A : Matrix (Fin r) C ℝ}
    (hker : ∀ d, ι *ᵥ d = 0 → Aᵀ *ᵥ d = 0) :
    (ιᵀ * ι) * A = A := by
  set Q : Matrix (Fin r) (Fin r) ℝ := 1 - ιᵀ * ι with hQ
  have hsym : Qᵀ = Q := by
    rw [hQ, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  have hmat : ι * Q = 0 := by
    rw [hQ, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hortho, Matrix.one_mul,
      sub_self]
  have hz : Q * A = 0 := by
    ext k c
    set d : Fin r → ℝ := fun j => Q k j with hd
    have hιd : ι *ᵥ d = 0 := by
      funext i
      calc (ι *ᵥ d) i = ∑ j, ι i j * Q k j := rfl
        _ = ∑ j, ι i j * Q j k := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            congr 1
            calc Q k j = Qᵀ j k := rfl
              _ = Q j k := by rw [hsym]
        _ = (ι * Q) i k := (Matrix.mul_apply).symm
        _ = 0 := by rw [hmat, Matrix.zero_apply]
    have hAd := congrFun (hker d hιd) c
    rw [Pi.zero_apply] at hAd
    calc (Q * A) k c = ∑ j, Q k j * A j c := Matrix.mul_apply
      _ = ∑ j, A j c * d j := Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      _ = (Aᵀ *ᵥ d) c := rfl
      _ = 0 := hAd
  have hexp : (ιᵀ * ι) * A = A - Q * A := by
    rw [hQ, Matrix.sub_mul, Matrix.one_mul, sub_sub_cancel]
  rw [hexp, hz, sub_zero]

/-- **Single-mode projector fix**: if `ι` has orthonormal rows and
the `e`-mode unfolding of `W` kills `ker ι`, then applying `P = ιᵀι` on that mode fixes `W`. -/
theorem modeMul_proj_eq_self {s : ℕ} (v : a.V) (e : a.Inc v)
    {ι : Matrix (Fin s) (Fin (a.r e.1)) ℝ} (hortho : ι * ιᵀ = 1) {W : a.NodeTensor v}
    (hker : ∀ d, ι *ᵥ d = 0 → (a.matE v e W)ᵀ *ᵥ d = 0) :
    a.modeMul v e (ιᵀ * ι) W = W := by
  have hM : a.matE v e (a.modeMul v e (ιᵀ * ι) W) = a.matE v e W := by
    rw [a.matE_modeMul, proj_mul_eq_of_supported hortho hker]
  funext bi x
  have happ : ∀ W' : a.NodeTensor v,
      W' bi x = a.matE v e W' (bi e)
        (((Equiv.piSplitAt e fun e' => Fin (a.r e'.1)) bi).2, x) := by
    intro W'
    show W' bi x = W' ((Equiv.piSplitAt e fun e' => Fin (a.r e'.1)).symm
        ((Equiv.piSplitAt e fun e' => Fin (a.r e'.1)) bi)) x
    rw [Equiv.symm_apply_apply]
  rw [happ (a.modeMul v e (ιᵀ * ι) W), hM, ← happ W]

/-- **Multi-mode projector collapse**: if applying `P e` on mode `e`
fixes `W` for every incidence `e`, then the simultaneous all-modes application fixes `W`
pointwise. Proved by induction over the set of modes already converted from delta to `P`. -/
theorem sum_prod_modeMul_eq_self (v : a.V)
    (P : (e : a.Inc v) → Matrix (Fin (a.r e.1)) (Fin (a.r e.1)) ℝ)
    (W : a.NodeTensor v) (hfix : ∀ e, a.modeMul v e (P e) W = W)
    (bi : a.BondIdx v) (x : Fin (a.n v)) :
    ∑ bi₂ : a.BondIdx v, (∏ e : a.Inc v, P e (bi e) (bi₂ e)) * W bi₂ x = W bi x := by
  classical
  have key : ∀ S : Finset (a.Inc v), ∀ bi : a.BondIdx v,
      ∑ bi₂ : a.BondIdx v,
        (∏ e ∈ S, P e (bi e) (bi₂ e))
          * (∏ e ∈ Sᶜ, if bi₂ e = bi e then (1 : ℝ) else 0) * W bi₂ x
        = W bi x := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro bi
      have hzero : ∀ bi₂ ∈ (Finset.univ : Finset (a.BondIdx v)), bi₂ ≠ bi →
          (∏ e ∈ (∅ : Finset (a.Inc v)), P e (bi e) (bi₂ e))
            * (∏ e ∈ (∅ : Finset (a.Inc v))ᶜ, if bi₂ e = bi e then (1 : ℝ) else 0)
            * W bi₂ x = 0 := by
        intro bi₂ _ hne
        obtain ⟨e, he⟩ : ∃ e, bi₂ e ≠ bi e := by
          by_contra hall
          push Not at hall
          exact hne (funext hall)
        rw [Finset.prod_eq_zero (Finset.mem_compl.mpr (Finset.notMem_empty e)) (if_neg he),
          mul_zero, zero_mul]
      rw [Finset.sum_eq_single bi hzero (fun hbi => absurd (Finset.mem_univ bi) hbi),
        Finset.prod_empty, one_mul, Finset.prod_eq_one (fun e _ => if_pos rfl), one_mul]
    | @insert e₀ S he₀ ih =>
      intro bi
      have hbi₂ : ∀ bi₂ : a.BondIdx v,
          (∑ k : Fin (a.r e₀.1), P e₀ (bi e₀) k *
            ((∏ e ∈ S, P e (Function.update bi e₀ k e) (bi₂ e))
              * (∏ e ∈ Sᶜ, if bi₂ e = Function.update bi e₀ k e then (1 : ℝ) else 0)
              * W bi₂ x))
          = (∏ e ∈ insert e₀ S, P e (bi e) (bi₂ e))
              * (∏ e ∈ (insert e₀ S)ᶜ, if bi₂ e = bi e then (1 : ℝ) else 0)
              * W bi₂ x := by
        intro bi₂
        have hS : ∀ k : Fin (a.r e₀.1),
            (∏ e ∈ S, P e (Function.update bi e₀ k e) (bi₂ e))
              = ∏ e ∈ S, P e (bi e) (bi₂ e) := fun k =>
          Finset.prod_congr rfl fun e heS => by
            rw [Function.update_of_ne (ne_of_mem_of_not_mem heS he₀)]
        have hC : ∀ k : Fin (a.r e₀.1),
            (∏ e ∈ Sᶜ, if bi₂ e = Function.update bi e₀ k e then (1 : ℝ) else 0)
              = (if bi₂ e₀ = k then (1 : ℝ) else 0)
                  * ∏ e ∈ (insert e₀ S)ᶜ, if bi₂ e = bi e then (1 : ℝ) else 0 := by
          intro k
          rw [Finset.compl_insert,
            ← Finset.mul_prod_erase Sᶜ _ (Finset.mem_compl.mpr he₀),
            Function.update_self]
          congr 1
          refine Finset.prod_congr rfl fun e he => ?_
          rw [Function.update_of_ne (Finset.mem_erase.mp he).1]
        calc (∑ k : Fin (a.r e₀.1), P e₀ (bi e₀) k *
              ((∏ e ∈ S, P e (Function.update bi e₀ k e) (bi₂ e))
                * (∏ e ∈ Sᶜ, if bi₂ e = Function.update bi e₀ k e then (1 : ℝ) else 0)
                * W bi₂ x))
            = ∑ k : Fin (a.r e₀.1), (if bi₂ e₀ = k then
                P e₀ (bi e₀) k * ((∏ e ∈ S, P e (bi e) (bi₂ e))
                  * (∏ e ∈ (insert e₀ S)ᶜ, if bi₂ e = bi e then (1 : ℝ) else 0)
                  * W bi₂ x) else 0) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [hS k, hC k]
              by_cases hk : bi₂ e₀ = k
              · rw [if_pos hk, if_pos hk]
                ring
              · rw [if_neg hk, if_neg hk]
                ring
          _ = P e₀ (bi e₀) (bi₂ e₀) * ((∏ e ∈ S, P e (bi e) (bi₂ e))
                * (∏ e ∈ (insert e₀ S)ᶜ, if bi₂ e = bi e then (1 : ℝ) else 0)
                * W bi₂ x) := by
              rw [Finset.sum_ite_eq]
              exact if_pos (Finset.mem_univ _)
          _ = (∏ e ∈ insert e₀ S, P e (bi e) (bi₂ e))
                * (∏ e ∈ (insert e₀ S)ᶜ, if bi₂ e = bi e then (1 : ℝ) else 0)
                * W bi₂ x := by
              rw [Finset.prod_insert he₀]
              ring
      calc ∑ bi₂ : a.BondIdx v,
            (∏ e ∈ insert e₀ S, P e (bi e) (bi₂ e))
              * (∏ e ∈ (insert e₀ S)ᶜ, if bi₂ e = bi e then (1 : ℝ) else 0) * W bi₂ x
          = ∑ bi₂ : a.BondIdx v, ∑ k : Fin (a.r e₀.1), P e₀ (bi e₀) k *
              ((∏ e ∈ S, P e (Function.update bi e₀ k e) (bi₂ e))
                * (∏ e ∈ Sᶜ, if bi₂ e = Function.update bi e₀ k e then (1 : ℝ) else 0)
                * W bi₂ x) :=
            Finset.sum_congr rfl fun bi₂ _ => (hbi₂ bi₂).symm
        _ = ∑ k : Fin (a.r e₀.1), ∑ bi₂ : a.BondIdx v, P e₀ (bi e₀) k *
              ((∏ e ∈ S, P e (Function.update bi e₀ k e) (bi₂ e))
                * (∏ e ∈ Sᶜ, if bi₂ e = Function.update bi e₀ k e then (1 : ℝ) else 0)
                * W bi₂ x) := Finset.sum_comm
        _ = ∑ k : Fin (a.r e₀.1), P e₀ (bi e₀) k * W (Function.update bi e₀ k) x := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← Finset.mul_sum, ih (Function.update bi e₀ k)]
        _ = a.modeMul v e₀ (P e₀) W bi x := rfl
        _ = W bi x := congrFun (congrFun (hfix e₀) bi) x
  have h := key Finset.univ bi
  simp only [Finset.compl_univ, Finset.prod_empty, mul_one] at h
  exact h

/-- The incidences of `a` and of the re-dimensioned architecture coincide. -/
def reDimIncEquiv (v : a.V) : a.Inc v ≃ (a.reDim r' hr').Inc v where
  toFun := toReDimInc
  invFun := ofReDimInc
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Per-node slot-sum Fubini** for the re-dimensioned architecture: the sum over bond
multi-indices of an incidence-wise product is the product of per-incidence sums. -/
private theorem sum_bondIdx_prod_inc {v : a.V}
    (f : (e' : (a.reDim r' hr').Inc v) → Fin (r' e'.1) → ℝ) :
    (∑ bi' : (a.reDim r' hr').BondIdx v, ∏ e' : (a.reDim r' hr').Inc v, f e' (bi' e'))
      = ∏ e' : (a.reDim r' hr').Inc v, ∑ k, f e' k := by
  classical
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rfl

/-- **Paper correspondence (conditional): Lemma E.6(2), recovery after compression.**
On supported points, compression followed by the zero-padding embedding is the identity. -/
theorem mapParam_compressParam
    (ι : (E : a.G.edgeSet) → Matrix (Fin (r' E.1)) (Fin (a.r E.1)) ℝ)
    (hortho : ∀ E, ι E * (ι E)ᵀ = 1) {θ : a.Param} (hsupp : SupportedOn (r' := r') ι θ) :
    mapParam ι (compressParam (hr' := hr') ι θ) = θ := by
  classical
  funext v bi xv
  have hfix : ∀ e : a.Inc v,
      a.modeMul v e ((ι ⟨e.1, e.2.1⟩)ᵀ * ι ⟨e.1, e.2.1⟩) (θ v) = θ v := fun e =>
    a.modeMul_proj_eq_self v e (hortho ⟨e.1, e.2.1⟩) (fun d hd => hsupp v e d hd)
  calc mapParam ι (compressParam (hr' := hr') ι θ) v bi xv
      = ∑ bi' : (a.reDim r' hr').BondIdx v,
          (∏ e' : (a.reDim r' hr').Inc v, ι ⟨e'.1, e'.2.1⟩ (bi' e') (bi (ofReDimInc e')))
            * ∑ bi₂ : a.BondIdx v,
                (∏ e : a.Inc v, ι ⟨e.1, e.2.1⟩ (bi' (toReDimInc e)) (bi₂ e))
                  * θ v bi₂ xv := rfl
    _ = ∑ bi' : (a.reDim r' hr').BondIdx v, ∑ bi₂ : a.BondIdx v,
          (∏ e' : (a.reDim r' hr').Inc v, ι ⟨e'.1, e'.2.1⟩ (bi' e') (bi (ofReDimInc e')))
            * ((∏ e : a.Inc v, ι ⟨e.1, e.2.1⟩ (bi' (toReDimInc e)) (bi₂ e))
                * θ v bi₂ xv) := by
        refine Finset.sum_congr rfl fun bi' _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ bi₂ : a.BondIdx v, ∑ bi' : (a.reDim r' hr').BondIdx v,
          (∏ e' : (a.reDim r' hr').Inc v, ι ⟨e'.1, e'.2.1⟩ (bi' e') (bi (ofReDimInc e')))
            * ((∏ e : a.Inc v, ι ⟨e.1, e.2.1⟩ (bi' (toReDimInc e)) (bi₂ e))
                * θ v bi₂ xv) := Finset.sum_comm
    _ = ∑ bi₂ : a.BondIdx v,
          (∏ e : a.Inc v, ((ι ⟨e.1, e.2.1⟩)ᵀ * ι ⟨e.1, e.2.1⟩) (bi e) (bi₂ e))
            * θ v bi₂ xv := by
        refine Finset.sum_congr rfl fun bi₂ _ => ?_
        have hreidx : ∀ bi' : (a.reDim r' hr').BondIdx v,
            (∏ e : a.Inc v, ι ⟨e.1, e.2.1⟩ (bi' (toReDimInc e)) (bi₂ e))
              = ∏ e' : (a.reDim r' hr').Inc v,
                  ι ⟨e'.1, e'.2.1⟩ (bi' e') (bi₂ (ofReDimInc e')) := fun bi' =>
          Fintype.prod_equiv (a.reDimIncEquiv (r' := r') (hr' := hr') v)
            (fun e => ι ⟨e.1, e.2.1⟩ (bi' (toReDimInc e)) (bi₂ e))
            (fun e' => ι ⟨e'.1, e'.2.1⟩ (bi' e') (bi₂ (ofReDimInc e')))
            (fun e => rfl)
        calc ∑ bi' : (a.reDim r' hr').BondIdx v,
              (∏ e' : (a.reDim r' hr').Inc v, ι ⟨e'.1, e'.2.1⟩ (bi' e') (bi (ofReDimInc e')))
                * ((∏ e : a.Inc v, ι ⟨e.1, e.2.1⟩ (bi' (toReDimInc e)) (bi₂ e))
                    * θ v bi₂ xv)
            = (∑ bi' : (a.reDim r' hr').BondIdx v,
                ∏ e' : (a.reDim r' hr').Inc v,
                  ι ⟨e'.1, e'.2.1⟩ (bi' e') (bi (ofReDimInc e'))
                    * ι ⟨e'.1, e'.2.1⟩ (bi' e') (bi₂ (ofReDimInc e'))) * θ v bi₂ xv := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun bi' _ => ?_
              rw [hreidx bi', ← mul_assoc, ← Finset.prod_mul_distrib]
          _ = (∏ e' : (a.reDim r' hr').Inc v, ∑ k : Fin (r' e'.1),
                ι ⟨e'.1, e'.2.1⟩ k (bi (ofReDimInc e'))
                  * ι ⟨e'.1, e'.2.1⟩ k (bi₂ (ofReDimInc e'))) * θ v bi₂ xv := by
              rw [sum_bondIdx_prod_inc (r' := r') (hr' := hr')
                (fun (e' : (a.reDim r' hr').Inc v) (k : Fin (r' e'.1)) =>
                  ι ⟨e'.1, e'.2.1⟩ k (bi (ofReDimInc e'))
                    * ι ⟨e'.1, e'.2.1⟩ k (bi₂ (ofReDimInc e')))]
          _ = (∏ e : a.Inc v, ((ι ⟨e.1, e.2.1⟩)ᵀ * ι ⟨e.1, e.2.1⟩) (bi e) (bi₂ e))
                * θ v bi₂ xv := by
              congr 1
    _ = θ v bi xv :=
        a.sum_prod_modeMul_eq_self v
          (fun e => (ι ⟨e.1, e.2.1⟩)ᵀ * ι ⟨e.1, e.2.1⟩) (θ v) hfix bi xv

/-- **Paper correspondence (conditional): Lemma E.6(4), represented-tensor transfer.**
On supported points the compression preserves the represented tensor. -/
theorem represented_compressParam
    (ι : (E : a.G.edgeSet) → Matrix (Fin (r' E.1)) (Fin (a.r E.1)) ℝ)
    (hortho : ∀ E, ι E * (ι E)ᵀ = 1) {θ : a.Param} (hsupp : SupportedOn (r' := r') ι θ) :
    (a.reDim r' hr').represented (compressParam (hr' := hr') ι θ) = a.represented θ := by
  rw [← represented_mapParam ι hortho (compressParam (hr' := hr') ι θ),
    mapParam_compressParam ι hortho hsupp]

/-- **Paper correspondence (conditional): Lemma E.6(2), norm preservation at the
compressed point.** On supported points the compression preserves the squared parameter norm. -/
theorem paramNormSq_compressParam
    (ι : (E : a.G.edgeSet) → Matrix (Fin (r' E.1)) (Fin (a.r E.1)) ℝ)
    (hortho : ∀ E, ι E * (ι E)ᵀ = 1) {θ : a.Param} (hsupp : SupportedOn (r' := r') ι θ) :
    (a.reDim r' hr').paramNormSq (compressParam (hr' := hr') ι θ) = a.paramNormSq θ := by
  rw [← paramNormSq_mapParam ι hortho (compressParam (hr' := hr') ι θ),
    mapParam_compressParam ι hortho hsupp]

/-- **Paper correspondence (conditional): Lemma E.6(3), minimum-norm transfer.** -/
theorem minNorm_compressParam
    (ι : (E : a.G.edgeSet) → Matrix (Fin (r' E.1)) (Fin (a.r E.1)) ℝ)
    (hortho : ∀ E, ι E * (ι E)ᵀ = 1) {θ : a.Param} (hsupp : SupportedOn (r' := r') ι θ)
    (hmn : a.MinNorm θ) : (a.reDim r' hr').MinNorm (compressParam (hr' := hr') ι θ) := by
  intro θ' hθ'
  have hbig : a.represented (mapParam ι θ') = a.represented θ := by
    rw [represented_mapParam ι hortho θ', hθ',
      represented_compressParam ι hortho hsupp]
  have h1 := hmn (mapParam ι θ') hbig
  rw [paramNormSq_compressParam ι hortho hsupp,
    ← paramNormSq_mapParam ι hortho θ']
  exact h1

/-- `mapParam` commutes with a single-node update (it acts per node). -/
theorem mapParam_update (ι : (E : a.G.edgeSet) → Matrix (Fin (r' E.1)) (Fin (a.r E.1)) ℝ)
    (θ' : (a.reDim r' hr').Param) (v : a.V) (δ' : (a.reDim r' hr').NodeTensor v) :
    mapParam ι (Function.update θ' v δ')
      = Function.update (mapParam ι θ') v
          (fun bi xv => ∑ bi' : (a.reDim r' hr').BondIdx v,
            (∏ e : (a.reDim r' hr').Inc v, ι ⟨e.1, e.2.1⟩ (bi' e) (bi (ofReDimInc e)))
              * δ' bi' xv) := by
  funext x bi xv
  by_cases hx : x = v
  · subst hx
    simp only [mapParam, Function.update_self]
  · have hstep : (∑ bi' : (a.reDim r' hr').BondIdx x,
        (∏ e : (a.reDim r' hr').Inc x, ι ⟨e.1, e.2.1⟩ (bi' e) (bi (ofReDimInc e)))
          * Function.update θ' v δ' x bi' xv)
      = ∑ bi' : (a.reDim r' hr').BondIdx x,
        (∏ e : (a.reDim r' hr').Inc x, ι ⟨e.1, e.2.1⟩ (bi' e) (bi (ofReDimInc e)))
          * θ' x bi' xv :=
      Finset.sum_congr rfl (fun bi' _ =>
        congrArg (fun W : (a.reDim r' hr').NodeTensor x =>
          (∏ e : (a.reDim r' hr').Inc x, ι ⟨e.1, e.2.1⟩ (bi' e) (bi (ofReDimInc e)))
            * W bi' xv) (Function.update_of_ne hx δ' θ'))
    have hRHS : Function.update (mapParam (hr' := hr') ι θ') v
        (fun bi xv => ∑ bi' : (a.reDim r' hr').BondIdx v,
          (∏ e : (a.reDim r' hr').Inc v, ι ⟨e.1, e.2.1⟩ (bi' e) (bi (ofReDimInc e)))
            * δ' bi' xv) x = mapParam (hr' := hr') ι θ' x :=
      Function.update_of_ne hx _ _
    calc mapParam (hr' := hr') ι (Function.update θ' v δ') x bi xv
        = ∑ bi' : (a.reDim r' hr').BondIdx x,
            (∏ e : (a.reDim r' hr').Inc x, ι ⟨e.1, e.2.1⟩ (bi' e) (bi (ofReDimInc e)))
              * θ' x bi' xv := hstep
      _ = _ := (congrFun (congrFun hRHS bi) xv).symm

/-- **Paper correspondence (conditional): Lemma E.6(3), criticality transfer.**
The compressed point is critical for the same target (the `Ext` spaces coincide definitionally). -/
theorem critical_compressParam
    (ι : (E : a.G.edgeSet) → Matrix (Fin (r' E.1)) (Fin (a.r E.1)) ℝ)
    (hortho : ∀ E, ι E * (ι E)ᵀ = 1) {Tstar : a.Ext → ℝ} {θ : a.Param}
    (hsupp : SupportedOn (r' := r') ι θ) (hcrit : a.Critical Tstar θ) :
    (a.reDim r' hr').Critical Tstar (compressParam (hr' := hr') ι θ) := by
  have hcrit := (a.critical_iff_nodewiseCritical Tstar θ).mp hcrit
  apply ((a.reDim r' hr').critical_iff_nodewiseCritical
    Tstar (compressParam (hr' := hr') ι θ)).mpr
  intro v δ'
  have hpair := hcrit v (fun bi xv => ∑ bi' : (a.reDim r' hr').BondIdx v,
    (∏ e : (a.reDim r' hr').Inc v, ι ⟨e.1, e.2.1⟩ (bi' e) (bi (ofReDimInc e))) * δ' bi' xv)
  have hupd : a.represented (Function.update θ v
      (fun bi xv => ∑ bi' : (a.reDim r' hr').BondIdx v,
        (∏ e : (a.reDim r' hr').Inc v, ι ⟨e.1, e.2.1⟩ (bi' e) (bi (ofReDimInc e)))
          * δ' bi' xv))
      = (a.reDim r' hr').represented (Function.update (compressParam (hr' := hr') ι θ) v δ') := by
    conv_lhs => rw [← mapParam_compressParam (hr' := hr') ι hortho hsupp]
    rw [← mapParam_update ι (compressParam (hr' := hr') ι θ) v δ',
      represented_mapParam ι hortho]
  have hres : ∀ x, a.residual Tstar θ x
      = (a.reDim r' hr').residual Tstar (compressParam (hr' := hr') ι θ) x := by
    intro x
    show a.represented θ x - Tstar x
      = (a.reDim r' hr').represented (compressParam (hr' := hr') ι θ) x - Tstar x
    rw [represented_compressParam ι hortho hsupp]
  rw [← Finset.sum_congr rfl (fun x _ => by rw [← hres x, ← hupd])]
  exact hpair

/-- `mapParam` is continuous, so a local minimum
of the big loss compresses to a local minimum of the reduced loss. -/
theorem continuous_mapParam
    (ι : (E : a.G.edgeSet) → Matrix (Fin (r' E.1)) (Fin (a.r E.1)) ℝ) :
    Continuous (mapParam (hr' := hr') ι) := by
  apply continuous_pi
  intro v
  apply continuous_pi
  intro bi
  apply continuous_pi
  intro xv
  show Continuous fun θ' : (a.reDim r' hr').Param =>
    ∑ bi' : (a.reDim r' hr').BondIdx v,
      (∏ e : (a.reDim r' hr').Inc v, ι ⟨e.1, e.2.1⟩ (bi' e) (bi (ofReDimInc e)))
        * θ' v bi' xv
  apply continuous_finsetSum
  intro bi' _
  exact continuous_const.mul
    ((continuous_apply _).comp ((continuous_apply _).comp (continuous_apply v)))

/-- **Paper correspondence (conditional): Lemma E.6(5), local-minimum transfer.** -/
theorem isLocalMin_compressParam
    (ι : (E : a.G.edgeSet) → Matrix (Fin (r' E.1)) (Fin (a.r E.1)) ℝ)
    (hortho : ∀ E, ι E * (ι E)ᵀ = 1) {Tstar : a.Ext → ℝ} {θ : a.Param}
    (hsupp : SupportedOn (r' := r') ι θ) (hloc : IsLocalMin (a.loss Tstar) θ) :
    IsLocalMin ((a.reDim r' hr').loss Tstar) (compressParam (hr' := hr') ι θ) := by
  have hlosses : (a.reDim r' hr').loss Tstar
      = (a.loss Tstar) ∘ (mapParam (hr' := hr') ι) := by
    funext θ'
    show (1 / 2) * (∑ x, ((a.reDim r' hr').represented θ' x - Tstar x) ^ 2)
      = (1 / 2) * (∑ x, (a.represented (mapParam ι θ') x - Tstar x) ^ 2)
    rw [represented_mapParam ι hortho θ']
    rfl
  rw [hlosses]
  have hbase : IsLocalMin (a.loss Tstar)
      ((mapParam (hr' := hr') ι) (compressParam (hr' := hr') ι θ)) := by
    rw [mapParam_compressParam ι hortho hsupp]
    exact hloc
  exact IsLocalMin.comp_continuous hbase (continuous_mapParam ι).continuousAt

/-- A matrix of rank zero is zero. -/
theorem eq_zero_of_rank_eq_zero {m C : Type*} [Fintype m] [Fintype C] [DecidableEq C]
    {M : Matrix m C ℝ} (hrank : M.rank = 0) : M = 0 := by
  have hr : Module.finrank ℝ (LinearMap.range M.mulVecLin) = 0 := hrank
  have hbot : LinearMap.range M.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hr
  ext i j
  have hcolz : M.col j = 0 := by
    have hmem : M.col j ∈ LinearMap.range M.mulVecLin :=
      ⟨Pi.single j 1, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hmem
  have hij := congrFun hcolz i
  simpa [Matrix.col_apply] using hij

/-- A target with a vanishing cut matricization vanishes (the matricization is a reshape). -/
theorem eq_zero_of_matricizeOf_eq_zero {u w : a.V} (h : a.G.Adj u w) {T : a.Ext → ℝ}
    (h0 : a.matricizeOf h T = 0) : T = 0 := by
  funext x
  have hx : T x = a.matricizeOf h T (a.extSplit h x).1 (a.extSplit h x).2 := by
    show T x = T ((a.extSplit h).symm ((a.extSplit h x).1, (a.extSplit h x).2))
    rw [Prod.mk.eta, Equiv.symm_apply_apply]
  rw [hx, h0]
  rfl

/-- **Paper correspondence (conditional): Lemma E.6(1), reduction to full target cut
rank.** For a realizable nonzero target, this constructs the reduction data used with the
transfer lemmas above. At a minimum-norm critical point of a realizable nonzero
target, the target-rank re-dimensioning `r'_E := rank T*⁽ᴱ⁾` is positive and dominated by
`r`, and admits per-edge orthonormal-row bond maps `ι_E` (kernels inside the dormant
subspaces, hence supported on `θ`); the target stays realizable at the reduced dimensions
and has full matricization rank at every reduced edge. -/
theorem exists_compress_reduction {Tstar : a.Ext → ℝ} (hreal : a.Realizable Tstar)
    (hT0 : Tstar ≠ 0) {θ : a.Param} (hmn : a.MinNorm θ) (hcrit : a.Critical Tstar θ) :
    ∃ (r' : Sym2 a.V → ℕ) (hr' : ∀ e ∈ a.G.edgeSet, 0 < r' e)
      (ι : (E : a.G.edgeSet) → Matrix (Fin (r' E.1)) (Fin (a.r E.1)) ℝ),
      (∀ E, ι E * (ι E)ᵀ = 1) ∧ SupportedOn ι θ ∧
      (a.reDim r' hr').Realizable Tstar ∧
      (∀ (u w : a.V) (h : a.G.Adj u w),
        ((a.reDim r' hr').matricizeOf h Tstar).rank = (a.reDim r' hr').r s(u, w)) := by
  classical
  -- the per-edge target rank, symmetric in the endpoints hence `Sym2`-liftable
  have hfsymm : ∀ u w : a.V,
      (if h : a.G.Adj u w then (a.matricizeOf h Tstar).rank else a.r s(u, w))
        = if h : a.G.Adj w u then (a.matricizeOf h Tstar).rank else a.r s(w, u) := by
    intro u w
    by_cases h : a.G.Adj u w
    · rw [dif_pos h, dif_pos h.symm, a.rank_matricizeOf_symm h Tstar]
    · rw [dif_neg h, dif_neg (fun h' => h h'.symm)]
      exact congrArg a.r Sym2.eq_swap.symm
  set r'' : Sym2 a.V → ℕ :=
    Sym2.lift ⟨fun u w => if h : a.G.Adj u w then (a.matricizeOf h Tstar).rank
      else a.r s(u, w), hfsymm⟩ with hr''def
  have hspec : ∀ (u w : a.V) (h : a.G.Adj u w),
      r'' s(u, w) = (a.matricizeOf h Tstar).rank := by
    intro u w h
    rw [hr''def, Sym2.lift_mk]
    exact dif_pos h
  have hle : ∀ (u w : a.V) (h : a.G.Adj u w), r'' s(u, w) ≤ a.r s(u, w) := by
    intro u w h
    rw [hspec u w h]
    exact a.realizable_iff_rank_le.mp hreal u w h
  have hpos : ∀ e ∈ a.G.edgeSet, 0 < r'' e := by
    intro e
    induction e using Sym2.ind with
    | _ p q =>
      intro hmem
      have hpq : a.G.Adj p q := by rwa [SimpleGraph.mem_edgeSet] at hmem
      rw [hspec p q hpq]
      rcases Nat.eq_zero_or_pos (a.matricizeOf hpq Tstar).rank with h0 | hp
      · exact absurd (a.eq_zero_of_matricizeOf_eq_zero hpq (eq_zero_of_rank_eq_zero h0)) hT0
      · exact hp
  -- per-edge orthonormal-row maps with kernels inside the dormant subspaces
  have hpere : ∀ (Ev : Sym2 a.V) (hEmem : Ev ∈ a.G.edgeSet),
      ∃ ιE : Matrix (Fin (r'' Ev)) (Fin (a.r Ev)) ℝ, ιE * ιEᵀ = 1 ∧
        ∀ (v : a.V) (hv : v ∈ Ev) (d : Fin (a.r Ev) → ℝ), ιE *ᵥ d = 0 →
          (a.matE v ⟨Ev, hEmem, hv⟩ (θ v))ᵀ *ᵥ d = 0 := by
    intro Ev
    induction Ev using Sym2.ind with
    | _ p q =>
      intro hEmem
      have hpq : a.G.Adj p q := by rwa [SimpleGraph.mem_edgeSet] at hEmem
      have hcount := a.minNorm_rank_add_finrank_dormant hpq hmn
      have hlt := a.minNorm_critical_rank_le_target hmn hcrit hpq
      obtain ⟨ιE, horthoE, hkerE⟩ := exists_orthonormal_rows_ker_le
        (hle p q hpq) (a.dormant hpq θ) (by rw [hspec p q hpq]; omega)
      refine ⟨ιE, horthoE, ?_⟩
      intro v hv d hd
      have hdmem : d ∈ a.dormant hpq θ := hkerE (by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        exact hd)
      obtain ⟨hd1, hd2⟩ := Submodule.mem_inf.mp hdmem
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hd1
        exact hd1
      · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hd2
        exact hd2
  choose ι hortho' hker' using fun E : a.G.edgeSet => hpere E.1 E.2
  refine ⟨r'', hpos, ι, hortho', ?_, ?_, ?_⟩
  · intro v e d hd
    exact hker' ⟨e.1, e.2.1⟩ v e.2.2 d hd
  · exact realizable_reDim (fun u w h => le_of_eq (hspec u w h).symm)
  · intro u w h
    exact (hspec u w h).symm

end Arch

end TTN
