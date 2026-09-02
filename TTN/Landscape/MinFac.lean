import TTN.Landscape.Dormant

/-!
# Minimal two-factor factorizations

The setting is
a single bond: `GL(r)` acts on pairs `(A, B) ∈ ℝ^{m×r} × ℝ^{r×n}` by
`g · (A, B) = (A g⁻¹, g B)`, preserving the product `A * B`.

* `IsMinimalFac`: `rank A = rank (A*B)` and `rank B = rank (A*B)`.
* `rank_mul_add_finrank_inf` / `rank_add_finrank_sup`: additive forms of
  the two rank-gap localizations `rank B − rank C = dim(col B ⊓ ker A)` and
  `rank A − rank C = r − dim(col B ⊔ ker A)`).
* `isMinimalFac_iff_isCompl`: `(A, B)` is minimal iff
  `ℝ^r = col B ⊕ ker A` (`IsCompl`).
* `exists_isMinimalFac_mem_closure_orbit`: the orbit closure of `(A, B)`
  contains a minimal factorization of `A*B`.
* `isMinimalFac_orbit`: any two minimal factorizations of the same matrix lie
  in one `GL(r)`-orbit.

Everything is plain matrix algebra over `ℝ` in the `Matrix`-adjacent style of
`TTN/RankFactor.lean`/`TTN/Landscape/Dormant.lean` (column spaces and kernels of `mulVecLin`; no
`EuclideanSpace` wrappers).
-/

open scoped Matrix

namespace TTN

namespace MinFac

variable {m n : Type*} [Fintype m] [Fintype n] {R : ℕ}

/-- **Paper correspondence: Definition G.1, minimal two-factor factorization.**
`(A, B)` is a minimal factorization of
`C := A * B` if both factors have the same rank as the product. -/
def IsMinimalFac (A : Matrix m (Fin R) ℝ) (B : Matrix (Fin R) n ℝ) : Prop :=
  A.rank = (A * B).rank ∧ B.rank = (A * B).rank

/-- The column space of the write factor `B`, inside the bond space `ℝ^r`. -/
noncomputable abbrev colB (B : Matrix (Fin R) n ℝ) : Submodule ℝ (Fin R → ℝ) :=
  LinearMap.range B.mulVecLin

/-- The kernel of the read factor `A`, inside the bond space `ℝ^r`. -/
noncomputable abbrev kerA (A : Matrix m (Fin R) ℝ) : Submodule ℝ (Fin R → ℝ) :=
  LinearMap.ker A.mulVecLin

/-- **First rank-gap localization** (additive form):
`rank (A*B) + dim(col B ⊓ ker A) = rank B`. -/
theorem rank_mul_add_finrank_inf (A : Matrix m (Fin R) ℝ) (B : Matrix (Fin R) n ℝ) :
    (A * B).rank + Module.finrank ℝ (colB B ⊓ kerA A : Submodule ℝ (Fin R → ℝ)) = B.rank := by
  classical
  have hrn := LinearMap.finrank_range_add_finrank_ker (A.mulVecLin.domRestrict (colB B))
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at hrn
  have hcomap : (LinearMap.ker A.mulVecLin).comap (colB B).subtype
      = (colB B ⊓ kerA A : Submodule ℝ (Fin R → ℝ)).comap (colB B).subtype := by
    ext x
    simp only [Submodule.mem_comap, Submodule.mem_inf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  rw [hcomap] at hrn
  have hkerfr := (Submodule.comapSubtypeEquivOfLe
    (inf_le_left : (colB B ⊓ kerA A : Submodule ℝ (Fin R → ℝ)) ≤ colB B)).finrank_eq
  rw [hkerfr] at hrn
  have hmap : (colB B).map A.mulVecLin = LinearMap.range ((A * B).mulVecLin) := by
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
  rw [hmap] at hrn
  have h1 : (A * B).rank = Module.finrank ℝ (LinearMap.range ((A * B).mulVecLin)) := rfl
  have h2 : B.rank = Module.finrank ℝ (colB B : Submodule ℝ (Fin R → ℝ)) := rfl
  omega

/-- **Second rank-gap localization** (additive form):
`rank A + dim(col B ⊔ ker A) = r + rank (A*B)`. -/
theorem rank_add_finrank_sup (A : Matrix m (Fin R) ℝ) (B : Matrix (Fin R) n ℝ) :
    A.rank + Module.finrank ℝ (colB B ⊔ kerA A : Submodule ℝ (Fin R → ℝ))
      = R + (A * B).rank := by
  classical
  have hsupinf := Submodule.finrank_sup_add_finrank_inf_eq (colB B) (kerA A)
  have hA : A.rank + Module.finrank ℝ (kerA A : Submodule ℝ (Fin R → ℝ)) = R := by
    have h := Arch.rank_add_finrank_ker A
    rwa [Fintype.card_fin] at h
  have hi := rank_mul_add_finrank_inf A B
  have h2 : B.rank = Module.finrank ℝ (colB B : Submodule ℝ (Fin R → ℝ)) := rfl
  omega

/-- **Paper correspondence: Lemma G.2(i), direct-sum characterization of minimal
factorizations.** A pair `(A, B)` is a minimal factorization iff the bond space splits as
`ℝ^r = col B ⊕ ker A`. -/
theorem isMinimalFac_iff_isCompl (A : Matrix m (Fin R) ℝ) (B : Matrix (Fin R) n ℝ) :
    IsMinimalFac A B ↔ IsCompl (colB B) (kerA A) := by
  classical
  have hi := rank_mul_add_finrank_inf A B
  have hs := rank_add_finrank_sup A B
  have hRfr : Module.finrank ℝ (Fin R → ℝ) = R := by simp
  constructor
  · rintro ⟨hA, hB⟩
    have hinf0 : Module.finrank ℝ (colB B ⊓ kerA A : Submodule ℝ (Fin R → ℝ)) = 0 := by
      omega
    have hsupR : Module.finrank ℝ (colB B ⊔ kerA A : Submodule ℝ (Fin R → ℝ)) = R := by
      omega
    constructor
    · rw [disjoint_iff]
      exact Submodule.finrank_eq_zero.mp hinf0
    · rw [codisjoint_iff]
      exact Submodule.eq_top_of_finrank_eq (by rw [hsupR, hRfr])
  · intro hcompl
    have hinf : (colB B ⊓ kerA A : Submodule ℝ (Fin R → ℝ)) = ⊥ := disjoint_iff.mp hcompl.1
    have hsup : (colB B ⊔ kerA A : Submodule ℝ (Fin R → ℝ)) = ⊤ := codisjoint_iff.mp hcompl.2
    have hinf0 : Module.finrank ℝ (colB B ⊓ kerA A : Submodule ℝ (Fin R → ℝ)) = 0 := by
      rw [hinf]; exact finrank_bot ℝ _
    have hsupR : Module.finrank ℝ (colB B ⊔ kerA A : Submodule ℝ (Fin R → ℝ)) = R := by
      rw [hsup, finrank_top, hRfr]
    exact ⟨by omega, by omega⟩

/-- Two real matrices agree when their `mulVec` actions agree (injectivity of `toLin'`). -/
private theorem ext_of_mulVec {p q : Type*} [Fintype q] [DecidableEq q]
    {X Y : Matrix p q ℝ} (h : ∀ v, X *ᵥ v = Y *ᵥ v) : X = Y :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h v])

/-- If `(A₁, B₁)` has `col B₁` disjoint from `ker A₁` and factors the same matrix as
`(A₀, B₀)`, then `ker B₀ ≤ ker B₁` (a vector killed by `B₀` is sent by `B₁` into
`col B₁ ⊓ ker A₁ = ⊥`). -/
private theorem ker_mulVecLin_le_of_disjoint {A₀ A₁ : Matrix m (Fin R) ℝ}
    {B₀ B₁ : Matrix (Fin R) n ℝ} (h₁ : Disjoint (colB B₁) (kerA A₁))
    (hC : A₀ * B₀ = A₁ * B₁) :
    LinearMap.ker B₀.mulVecLin ≤ LinearMap.ker B₁.mulVecLin := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have h0 : A₁.mulVecLin (B₁.mulVecLin x) = 0 := by
    have hCx : (A₀ * B₀).mulVecLin x = (A₁ * B₁).mulVecLin x := by rw [hC]
    rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, LinearMap.comp_apply,
      LinearMap.comp_apply, hx, map_zero] at hCx
    exact hCx.symm
  have hmem : B₁.mulVecLin x ∈ colB B₁ ⊓ kerA A₁ := ⟨LinearMap.mem_range_self _ x, h0⟩
  rwa [disjoint_iff.mp h₁, Submodule.mem_bot] at hmem

/-- Inside an ambient subspace `W`, every subspace `U ≤ W` admits a complement-within-`W`
(pull `U` back to the subtype `↥W`, take a complement there, push forward). -/
private theorem exists_inner_compl {U W : Submodule ℝ (Fin R → ℝ)} (hUW : U ≤ W) :
    ∃ V : Submodule ℝ (Fin R → ℝ), V ≤ W ∧ Disjoint U V ∧ U ⊔ V = W := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (U.comap W.subtype)
  refine ⟨q.map W.subtype, Submodule.map_subtype_le _ _, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxU hxq
    obtain ⟨y, hyq, hyx⟩ := Submodule.mem_map.mp hxq
    have hy0 : y ∈ (U.comap W.subtype) ⊓ q :=
      ⟨Submodule.mem_comap.mpr (hyx.symm ▸ hxU), hyq⟩
    rw [disjoint_iff.mp hq.disjoint, Submodule.mem_bot] at hy0
    rw [← hyx, hy0, map_zero]
  · calc U ⊔ q.map W.subtype
        = (U.comap W.subtype).map W.subtype ⊔ q.map W.subtype := by
          rw [Submodule.map_comap_subtype, inf_eq_right.mpr hUW]
      _ = ((U.comap W.subtype) ⊔ q).map W.subtype := by rw [Submodule.map_sup]
      _ = (⊤ : Submodule ℝ W).map W.subtype := by
          rw [codisjoint_iff.mp hq.codisjoint]
      _ = W := Submodule.map_subtype_top W

/-- **Paper correspondence: Lemma G.2(ii), existence in the gauge-orbit closure.**
The `GL(r)`-orbit closure of `(A, B)` contains a minimal factorization of `A * B`. -/
theorem exists_isMinimalFac_mem_closure_orbit (A : Matrix m (Fin R) ℝ)
    (B : Matrix (Fin R) n ℝ) :
    ∃ (A₀ : Matrix m (Fin R) ℝ) (B₀ : Matrix (Fin R) n ℝ),
      A₀ * B₀ = A * B ∧ IsMinimalFac A₀ B₀ ∧
      (A₀, B₀) ∈ closure {p : Matrix m (Fin R) ℝ × Matrix (Fin R) n ℝ |
        ∃ g : GL (Fin R) ℝ, p = (A * ((g⁻¹ : GL (Fin R) ℝ) : Matrix (Fin R) (Fin R) ℝ), ((g : GL (Fin R) ℝ) : Matrix (Fin R) (Fin R) ℝ) * B)} := by
  classical
  -- Step 1: the four-fold splitting ℝ^r = V₁ ⊕ V₂ ⊕ V₄ ⊕ V₅ with
  -- V₁ = col B ⊓ ker A, V₁ ⊕ V₂ = col B, V₁ ⊕ V₄ = ker A, V₅ ⊥ (col B ⊔ ker A).
  obtain ⟨V₂, hV₂col, hd12, hs12⟩ :=
    exists_inner_compl (inf_le_left : colB B ⊓ kerA A ≤ colB B)
  obtain ⟨V₄, hV₄ker, hd14, hs14⟩ :=
    exists_inner_compl (inf_le_right : colB B ⊓ kerA A ≤ kerA A)
  obtain ⟨V₅, hc₅⟩ := Submodule.exists_isCompl (colB B ⊔ kerA A)
  -- Step 2: lattice bookkeeping and the four global complement pairs.
  have hsup4 : colB B ⊔ V₄ = colB B ⊔ kerA A := by
    conv_rhs => rw [← hs14]
    rw [← sup_assoc, sup_eq_left.mpr (inf_le_left : colB B ⊓ kerA A ≤ colB B)]
  have hd_cb4 : Disjoint (colB B) V₄ := by
    rw [Submodule.disjoint_def]
    intro x hxc hx4
    exact Submodule.disjoint_def.mp hd14 x ⟨hxc, hV₄ker hx4⟩ hx4
  have hd_cb45 : Disjoint (colB B) (V₄ ⊔ V₅) :=
    hd_cb4.disjoint_sup_right_of_disjoint_sup_left (by rw [hsup4]; exact hc₅.disjoint)
  have htop45 : colB B ⊔ (V₄ ⊔ V₅) = ⊤ := by
    rw [← sup_assoc, hsup4]
    exact codisjoint_iff.mp hc₅.codisjoint
  have hc₁ : IsCompl (colB B ⊓ kerA A) (V₂ ⊔ (V₄ ⊔ V₅)) := by
    constructor
    · exact hd12.disjoint_sup_right_of_disjoint_sup_left (by rw [hs12]; exact hd_cb45)
    · rw [codisjoint_iff, ← sup_assoc, hs12]
      exact htop45
  have hc₂ : IsCompl V₂ ((colB B ⊓ kerA A) ⊔ (V₄ ⊔ V₅)) := by
    constructor
    · exact hd12.symm.disjoint_sup_right_of_disjoint_sup_left
        (by rw [sup_comm V₂ _, hs12]; exact hd_cb45)
    · rw [codisjoint_iff, ← sup_assoc, sup_comm V₂ _, hs12]
      exact htop45
  have hc₄ : IsCompl V₄ (colB B ⊔ V₅) := by
    constructor
    · exact hd_cb4.symm.disjoint_sup_right_of_disjoint_sup_left
        (by rw [sup_comm V₄ _, hsup4]; exact hc₅.disjoint)
    · rw [codisjoint_iff, ← sup_assoc, sup_comm V₄ _, hsup4]
      exact codisjoint_iff.mp hc₅.codisjoint
  have hc₅s : IsCompl V₅ (colB B ⊔ kerA A) := hc₅.symm
  -- Step 3: the four projections of the splitting and their pointwise algebra.
  set P₁ := (colB B ⊓ kerA A).projection (V₂ ⊔ (V₄ ⊔ V₅)) hc₁ with hP₁def
  set P₂ := V₂.projection ((colB B ⊓ kerA A) ⊔ (V₄ ⊔ V₅)) hc₂ with hP₂def
  set P₄ := V₄.projection (colB B ⊔ V₅) hc₄ with hP₄def
  set P₅ := V₅.projection (colB B ⊔ kerA A) hc₅s with hP₅def
  have mem₁ : ∀ x, P₁ x ∈ colB B ⊓ kerA A := fun x => Submodule.projection_apply_mem hc₁ x
  have mem₂ : ∀ x, P₂ x ∈ V₂ := fun x => Submodule.projection_apply_mem hc₂ x
  have mem₄ : ∀ x, P₄ x ∈ V₄ := fun x => Submodule.projection_apply_mem hc₄ x
  have mem₅ : ∀ x, P₅ x ∈ V₅ := fun x => Submodule.projection_apply_mem hc₅s x
  have id₁ : ∀ x ∈ colB B ⊓ kerA A, P₁ x = x := fun x hx =>
    Submodule.projection_apply_of_mem_left hc₁ hx
  have id₂ : ∀ x ∈ V₂, P₂ x = x := fun x hx => Submodule.projection_apply_of_mem_left hc₂ hx
  have id₄ : ∀ x ∈ V₄, P₄ x = x := fun x hx => Submodule.projection_apply_of_mem_left hc₄ hx
  have id₅ : ∀ x ∈ V₅, P₅ x = x := fun x hx => Submodule.projection_apply_of_mem_left hc₅s hx
  have z₁ : ∀ x ∈ V₂ ⊔ (V₄ ⊔ V₅), P₁ x = 0 := fun x hx =>
    Submodule.projection_apply_of_mem_right hc₁ hx
  have z₂ : ∀ x ∈ (colB B ⊓ kerA A) ⊔ (V₄ ⊔ V₅), P₂ x = 0 := fun x hx =>
    Submodule.projection_apply_of_mem_right hc₂ hx
  have z₄ : ∀ x ∈ colB B ⊔ V₅, P₄ x = 0 := fun x hx =>
    Submodule.projection_apply_of_mem_right hc₄ hx
  have z₅ : ∀ x ∈ colB B ⊔ kerA A, P₅ x = 0 := fun x hx =>
    Submodule.projection_apply_of_mem_right hc₅s hx
  -- resolution of the identity
  have hsum : ∀ x : Fin R → ℝ, P₁ x + P₂ x + P₄ x + P₅ x = x := by
    intro x
    have hx : x ∈ colB B ⊔ (V₄ ⊔ V₅) := by rw [htop45]; exact Submodule.mem_top
    obtain ⟨c, hc, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨x₄, hx₄, x₅, hx₅, rfl⟩ := Submodule.mem_sup.mp hw
    rw [← hs12] at hc
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hc
    simp only [map_add]
    rw [id₁ x₁ hx₁, z₁ x₂ (Submodule.mem_sup_left hx₂),
      z₁ x₄ (Submodule.mem_sup_right (Submodule.mem_sup_left hx₄)),
      z₁ x₅ (Submodule.mem_sup_right (Submodule.mem_sup_right hx₅)),
      z₂ x₁ (Submodule.mem_sup_left hx₁), id₂ x₂ hx₂,
      z₂ x₄ (Submodule.mem_sup_right (Submodule.mem_sup_left hx₄)),
      z₂ x₅ (Submodule.mem_sup_right (Submodule.mem_sup_right hx₅)),
      z₄ x₁ (Submodule.mem_sup_left ((inf_le_left : colB B ⊓ kerA A ≤ colB B) hx₁)),
      z₄ x₂ (Submodule.mem_sup_left (hV₂col hx₂)), id₄ x₄ hx₄,
      z₄ x₅ (Submodule.mem_sup_right hx₅),
      z₅ x₁ (Submodule.mem_sup_left ((inf_le_left : colB B ⊓ kerA A ≤ colB B) hx₁)),
      z₅ x₂ (Submodule.mem_sup_left (hV₂col hx₂)),
      z₅ x₄ (Submodule.mem_sup_right (hV₄ker hx₄)), id₅ x₅ hx₅]
    abel
  -- pair products of the projections
  have p11 : ∀ v, P₁ (P₁ v) = P₁ v := fun v => id₁ _ (mem₁ v)
  have p12 : ∀ v, P₁ (P₂ v) = 0 := fun v => z₁ _ (Submodule.mem_sup_left (mem₂ v))
  have p14 : ∀ v, P₁ (P₄ v) = 0 := fun v =>
    z₁ _ (Submodule.mem_sup_right (Submodule.mem_sup_left (mem₄ v)))
  have p15 : ∀ v, P₁ (P₅ v) = 0 := fun v =>
    z₁ _ (Submodule.mem_sup_right (Submodule.mem_sup_right (mem₅ v)))
  have p21 : ∀ v, P₂ (P₁ v) = 0 := fun v => z₂ _ (Submodule.mem_sup_left (mem₁ v))
  have p22 : ∀ v, P₂ (P₂ v) = P₂ v := fun v => id₂ _ (mem₂ v)
  have p24 : ∀ v, P₂ (P₄ v) = 0 := fun v =>
    z₂ _ (Submodule.mem_sup_right (Submodule.mem_sup_left (mem₄ v)))
  have p25 : ∀ v, P₂ (P₅ v) = 0 := fun v =>
    z₂ _ (Submodule.mem_sup_right (Submodule.mem_sup_right (mem₅ v)))
  have p41 : ∀ v, P₄ (P₁ v) = 0 := fun v =>
    z₄ _ (Submodule.mem_sup_left ((inf_le_left : colB B ⊓ kerA A ≤ colB B) (mem₁ v)))
  have p42 : ∀ v, P₄ (P₂ v) = 0 := fun v => z₄ _ (Submodule.mem_sup_left (hV₂col (mem₂ v)))
  have p44 : ∀ v, P₄ (P₄ v) = P₄ v := fun v => id₄ _ (mem₄ v)
  have p45 : ∀ v, P₄ (P₅ v) = 0 := fun v => z₄ _ (Submodule.mem_sup_right (mem₅ v))
  have p51 : ∀ v, P₅ (P₁ v) = 0 := fun v =>
    z₅ _ (Submodule.mem_sup_left ((inf_le_left : colB B ⊓ kerA A ≤ colB B) (mem₁ v)))
  have p52 : ∀ v, P₅ (P₂ v) = 0 := fun v => z₅ _ (Submodule.mem_sup_left (hV₂col (mem₂ v)))
  have p54 : ∀ v, P₅ (P₄ v) = 0 := fun v => z₅ _ (Submodule.mem_sup_right (hV₄ker (mem₄ v)))
  have p55 : ∀ v, P₅ (P₅ v) = P₅ v := fun v => id₅ _ (mem₅ v)
  -- Step 4: the matrix avatars and the vanishing products.
  set M₁ := LinearMap.toMatrix' P₁ with hM₁def
  set M₂ := LinearMap.toMatrix' P₂ with hM₂def
  set M₄ := LinearMap.toMatrix' P₄ with hM₄def
  set M₅ := LinearMap.toMatrix' P₅ with hM₅def
  have hMv₁ : ∀ v, M₁ *ᵥ v = P₁ v := fun v => LinearMap.toMatrix'_mulVec P₁ v
  have hMv₂ : ∀ v, M₂ *ᵥ v = P₂ v := fun v => LinearMap.toMatrix'_mulVec P₂ v
  have hMv₄ : ∀ v, M₄ *ᵥ v = P₄ v := fun v => LinearMap.toMatrix'_mulVec P₄ v
  have hMv₅ : ∀ v, M₅ *ᵥ v = P₅ v := fun v => LinearMap.toMatrix'_mulVec P₅ v
  have hAM₁ : A * M₁ = 0 := ext_of_mulVec fun v => by
    rw [← Matrix.mulVec_mulVec, hMv₁, Matrix.zero_mulVec]
    exact LinearMap.mem_ker.mp ((inf_le_right : colB B ⊓ kerA A ≤ kerA A) (mem₁ v))
  have hAM₄ : A * M₄ = 0 := ext_of_mulVec fun v => by
    rw [← Matrix.mulVec_mulVec, hMv₄, Matrix.zero_mulVec]
    exact LinearMap.mem_ker.mp (hV₄ker (mem₄ v))
  have hM₄B : M₄ * B = 0 := ext_of_mulVec fun v => by
    rw [← Matrix.mulVec_mulVec, hMv₄, Matrix.zero_mulVec]
    exact z₄ _ (Submodule.mem_sup_left (LinearMap.mem_range_self B.mulVecLin v))
  have hM₅B : M₅ * B = 0 := ext_of_mulVec fun v => by
    rw [← Matrix.mulVec_mulVec, hMv₅, Matrix.zero_mulVec]
    exact z₅ _ (Submodule.mem_sup_left (LinearMap.mem_range_self B.mulVecLin v))
  have hM₂M₂ : M₂ * M₂ = M₂ := ext_of_mulVec fun v => by
    rw [← Matrix.mulVec_mulVec, hMv₂, hMv₂, p22]
  -- `A` does not see the `P₂`-truncation on column vectors of `B`
  have hAP₂ : ∀ y ∈ colB B, A *ᵥ P₂ y = A *ᵥ y := by
    intro y hy
    conv_rhs => rw [← hsum y]
    rw [z₄ y (Submodule.mem_sup_left hy), z₅ y (Submodule.mem_sup_left hy), add_zero,
      add_zero, Matrix.mulVec_add]
    have h1 : A *ᵥ P₁ y = 0 := LinearMap.mem_ker.mp ((inf_le_right : colB B ⊓ kerA A ≤ kerA A) (mem₁ y))
    rw [h1, zero_add]
  -- affine expansion of the gauge action
  have hlin : ∀ (a b : ℝ) (v : Fin R → ℝ),
      (a • M₁ + M₂ + M₄ + b • M₅) *ᵥ v = a • P₁ v + P₂ v + P₄ v + b • P₅ v := by
    intro a b v
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, hMv₁, hMv₂, hMv₄, hMv₅]
  -- the gauges `g_t` are units for `t ≠ 0`
  have hunit : ∀ s u : ℝ, s * u = 1 →
      (s • M₁ + M₂ + M₄ + u • M₅) * (u • M₁ + M₂ + M₄ + s • M₅) = 1 := by
    intro s u hsu
    have hus : u * s = 1 := by rwa [mul_comm] at hsu
    apply ext_of_mulVec
    intro v
    rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hlin, hlin]
    simp only [map_add, map_smul, p11, p12, p14, p15, p21, p22, p24, p25,
      p41, p42, p44, p45, p51, p52, p54, p55, smul_zero, add_zero, zero_add]
    rw [smul_smul, smul_smul, hsu, hus, one_smul, one_smul]
    exact hsum v
  -- Step 5: conclude with `(A₀, B₀) := (A * M₂, M₂ * B)`.
  refine ⟨A * M₂, M₂ * B, ?_, ?_, ?_⟩
  · -- the product is preserved
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc M₂ M₂ B, hM₂M₂]
    apply ext_of_mulVec
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hMv₂, ← Matrix.mulVec_mulVec]
    exact hAP₂ _ (LinearMap.mem_range_self B.mulVecLin v)
  · -- minimality: `col (M₂B) = V₂` and `ker (AM₂) = V₁ ⊔ (V₄ ⊔ V₅)` are complementary
    rw [isMinimalFac_iff_isCompl]
    have hcol0 : colB (M₂ * B) = V₂ := by
      apply le_antisymm
      · intro y hy
        obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hy
        have hPv : (M₂ * B).mulVecLin v = P₂ (B *ᵥ v) := by
          show (M₂ * B) *ᵥ v = P₂ (B *ᵥ v)
          rw [← Matrix.mulVec_mulVec, hMv₂]
        rw [← hv, hPv]
        exact mem₂ _
      · intro y hy
        obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (hV₂col hy)
        apply LinearMap.mem_range.mpr
        refine ⟨v, ?_⟩
        show (M₂ * B) *ᵥ v = y
        rw [← Matrix.mulVec_mulVec, hMv₂]
        show P₂ (B.mulVecLin v) = y
        rw [hv]
        exact id₂ y hy
    have hker0 : kerA (A * M₂) = (colB B ⊓ kerA A) ⊔ (V₄ ⊔ V₅) := by
      apply le_antisymm
      · intro x hx
        have hx' : A.mulVecLin (P₂ x) = 0 := by
          have h := LinearMap.mem_ker.mp hx
          rw [Matrix.mulVecLin_mul, LinearMap.comp_apply] at h
          rwa [show M₂.mulVecLin x = P₂ x from LinearMap.toMatrix'_mulVec P₂ x] at h
        have hz : P₂ x = 0 :=
          Submodule.disjoint_def.mp hd12 _ ⟨hV₂col (mem₂ x), hx'⟩ (mem₂ x)
        have hdecomp := hsum x
        rw [hz, add_zero] at hdecomp
        rw [← hdecomp]
        exact Submodule.add_mem _
          (Submodule.add_mem _ (Submodule.mem_sup_left (mem₁ x))
            (Submodule.mem_sup_right (Submodule.mem_sup_left (mem₄ x))))
          (Submodule.mem_sup_right (Submodule.mem_sup_right (mem₅ x)))
      · intro x hx
        rw [LinearMap.mem_ker, Matrix.mulVecLin_mul, LinearMap.comp_apply,
          show M₂.mulVecLin x = P₂ x from LinearMap.toMatrix'_mulVec P₂ x, z₂ x hx,
          map_zero]
    rw [hcol0, hker0]
    exact hc₂
  · -- the pair is a limit of orbit points along `t → 0`
    have hpath : Filter.Tendsto
        (fun t : ℝ => (A * M₂ + t • (A * M₅), M₂ * B + t • (M₁ * B)))
        (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) (nhds (A * M₂, M₂ * B)) := by
      have hcont : Continuous fun t : ℝ =>
          (A * M₂ + t • (A * M₅), M₂ * B + t • (M₁ * B)) :=
        (continuous_const.add (continuous_id.smul continuous_const)).prodMk
          (continuous_const.add (continuous_id.smul continuous_const))
      have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
      simpa using h
    apply mem_closure_of_tendsto hpath
    filter_upwards [self_mem_nhdsWithin] with t ht
    replace ht : t ≠ 0 := ht
    refine ⟨⟨t • M₁ + M₂ + M₄ + t⁻¹ • M₅, t⁻¹ • M₁ + M₂ + M₄ + t • M₅,
      hunit t t⁻¹ (mul_inv_cancel₀ ht), hunit t⁻¹ t (inv_mul_cancel₀ ht)⟩, ?_⟩
    have hA' : A * (t⁻¹ • M₁ + M₂ + M₄ + t • M₅) = A * M₂ + t • (A * M₅) := by
      rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
        hAM₁, hAM₄, smul_zero, zero_add, add_zero]
    have hB' : (t • M₁ + M₂ + M₄ + t⁻¹ • M₅) * B = M₂ * B + t • (M₁ * B) := by
      rw [Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
        hM₄B, hM₅B, smul_zero, add_zero, add_zero, add_comm]
    exact Prod.ext hA'.symm hB'.symm

/-- **Paper correspondence: Lemma G.2(iii), uniqueness up to gauge.**
Any two minimal factorizations of the same matrix are related by a gauge `g ∈ GL(r)`. -/
theorem isMinimalFac_orbit {A₀ A₁ : Matrix m (Fin R) ℝ} {B₀ B₁ : Matrix (Fin R) n ℝ}
    (h₀ : IsMinimalFac A₀ B₀) (h₁ : IsMinimalFac A₁ B₁) (hC : A₀ * B₀ = A₁ * B₁) :
    ∃ g : GL (Fin R) ℝ, A₁ = A₀ * ((g⁻¹ : GL (Fin R) ℝ) : Matrix (Fin R) (Fin R) ℝ) ∧ B₁ = ((g : GL (Fin R) ℝ) : Matrix (Fin R) (Fin R) ℝ) * B₀ := by
  classical
  have hcompl₀ := (isMinimalFac_iff_isCompl A₀ B₀).mp h₀
  have hcompl₁ := (isMinimalFac_iff_isCompl A₁ B₁).mp h₁
  -- Step 1: the two write factors have the same kernel.
  have hker : LinearMap.ker B₀.mulVecLin = LinearMap.ker B₁.mulVecLin :=
    le_antisymm (ker_mulVecLin_le_of_disjoint hcompl₁.disjoint hC)
      (ker_mulVecLin_le_of_disjoint hcompl₀.disjoint hC.symm)
  -- Step 2: column-space equivalence `φ` with `φ (B₀ x) = B₁ x`.
  set φ : (colB B₀ : Submodule ℝ (Fin R → ℝ)) ≃ₗ[ℝ] (colB B₁ : Submodule ℝ (Fin R → ℝ)) :=
    (B₀.mulVecLin.quotKerEquivRange.symm.trans
      (Submodule.quotEquivOfEq _ _ hker)).trans B₁.mulVecLin.quotKerEquivRange with hφdef
  have hφ : ∀ x : n → ℝ,
      (φ ⟨B₀.mulVecLin x, LinearMap.mem_range_self _ x⟩ : Fin R → ℝ) = B₁.mulVecLin x := by
    intro x
    have h1 : B₀.mulVecLin.quotKerEquivRange.symm
        ⟨B₀.mulVecLin x, LinearMap.mem_range_self _ x⟩ = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext rfl
    rw [hφdef]
    simp only [LinearEquiv.trans_apply]
    rw [h1, Submodule.quotEquivOfEq_mk]
    exact B₁.mulVecLin.quotKerEquivRange_apply_mk x
  -- Step 3: kernel equivalence `κ` (dimensions agree by rank–nullity).
  have hkfr : Module.finrank ℝ (LinearMap.ker A₀.mulVecLin)
      = Module.finrank ℝ (LinearMap.ker A₁.mulVecLin) := by
    have hrk : A₀.rank = A₁.rank := by rw [h₀.1, hC, h₁.1]
    have hn₀ := Arch.rank_add_finrank_ker A₀
    have hn₁ := Arch.rank_add_finrank_ker A₁
    omega
  set κ : (kerA A₀ : Submodule ℝ (Fin R → ℝ)) ≃ₗ[ℝ] (kerA A₁ : Submodule ℝ (Fin R → ℝ)) :=
    LinearEquiv.ofFinrankEq _ _ hkfr with hκdef
  -- Step 4: assemble the gauge as a linear automorphism of the bond space.
  set gLin : (Fin R → ℝ) ≃ₗ[ℝ] (Fin R → ℝ) :=
    ((Submodule.prodEquivOfIsCompl _ _ hcompl₀).symm.trans (φ.prodCongr κ)).trans
      (Submodule.prodEquivOfIsCompl _ _ hcompl₁) with hgLin
  have hg_col : ∀ p : (colB B₀ : Submodule ℝ (Fin R → ℝ)), gLin ↑p = ↑(φ p) := by
    intro p
    rw [hgLin]
    simp only [LinearEquiv.trans_apply]
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    simp
  have hg_ker : ∀ k : (kerA A₀ : Submodule ℝ (Fin R → ℝ)), gLin ↑k = ↑(κ k) := by
    intro k
    rw [hgLin]
    simp only [LinearEquiv.trans_apply]
    rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
    simp
  -- Step 5: the two transport identities, pointwise on `mulVec`.
  have hgB : ∀ x : n → ℝ, gLin (B₀ *ᵥ x) = B₁ *ᵥ x := fun x =>
    (hg_col ⟨B₀.mulVecLin x, LinearMap.mem_range_self _ x⟩).trans (hφ x)
  have hAφ : ∀ p : (colB B₀ : Submodule ℝ (Fin R → ℝ)), A₁ *ᵥ ↑(φ p) = A₀ *ᵥ ↑p := by
    intro p
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp p.2
    have hp : p = ⟨B₀.mulVecLin x, LinearMap.mem_range_self _ x⟩ := Subtype.ext hx.symm
    rw [hp, hφ x]
    show A₁ *ᵥ (B₁ *ᵥ x) = A₀ *ᵥ (B₀ *ᵥ x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hC]
  have hAg : ∀ y : Fin R → ℝ, A₁ *ᵥ gLin y = A₀ *ᵥ y := by
    intro y
    have hy : y ∈ colB B₀ ⊔ kerA A₀ := by
      rw [codisjoint_iff.mp hcompl₀.codisjoint]; exact Submodule.mem_top
    obtain ⟨c, hc, k, hk, rfl⟩ := Submodule.mem_sup.mp hy
    have h3 : A₁ *ᵥ (↑(κ ⟨k, hk⟩) : Fin R → ℝ) = 0 := LinearMap.mem_ker.mp (κ ⟨k, hk⟩).2
    have h4 : A₀ *ᵥ k = 0 := LinearMap.mem_ker.mp hk
    rw [map_add, Matrix.mulVec_add, Matrix.mulVec_add, hg_col ⟨c, hc⟩, hg_ker ⟨k, hk⟩,
      hAφ ⟨c, hc⟩, h3, h4]
  -- Step 6: package the gauge as a `GL` element and conclude.
  refine ⟨⟨LinearMap.toMatrix' (gLin : (Fin R → ℝ) →ₗ[ℝ] Fin R → ℝ),
      LinearMap.toMatrix' (gLin.symm : (Fin R → ℝ) →ₗ[ℝ] Fin R → ℝ), ?_, ?_⟩, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  · -- `A₁ = A₀ * g⁻¹`
    show A₁ = A₀ * LinearMap.toMatrix' (gLin.symm : (Fin R → ℝ) →ₗ[ℝ] Fin R → ℝ)
    apply ext_of_mulVec
    intro v
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    simp only [LinearEquiv.coe_coe]
    rw [← hAg (gLin.symm v), LinearEquiv.apply_symm_apply]
  · -- `B₁ = g * B₀`
    show B₁ = LinearMap.toMatrix' (gLin : (Fin R → ℝ) →ₗ[ℝ] Fin R → ℝ) * B₀
    apply ext_of_mulVec
    intro v
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    simp only [LinearEquiv.coe_coe]
    rw [hgB v]

end MinFac

end TTN
