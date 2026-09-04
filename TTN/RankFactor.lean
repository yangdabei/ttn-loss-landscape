import Mathlib

/-!
# Minimal rank factorization of a matrix

A matrix of rank `≤ k` factors as `A Bᵀ` through an inner index `Fin k`, and can be taken
*minimal*: the columns of `B` beyond `rank M` vanish and the used columns of `A` are linearly
independent (`exists_factor_of_rank_le`; unfolded eliminator `eq_zero_of_sum_smul_col_eq_zero`).
Also home to the general-purpose rank lemmas the leaf-removal reductions consume
(`rank_le_rank_of_ker_le`, `mulVec_injective_of_rank_eq_card`). Everything is stated for a
general field, in the `Matrix` namespace.
-/

open scoped Matrix

namespace Matrix

open Submodule

variable {𝕜 : Type*} [Field 𝕜] {m n : Type*} [Fintype m] [Fintype n]

omit [Fintype m] in
/-- **Kernel containment reverses the rank inequality** (rank–nullity): if every vector
annihilated by `M` is annihilated by `N`, then `rank N ≤ rank M`. -/
theorem rank_le_rank_of_ker_le {p : Type*} (M : Matrix m n 𝕜) (N : Matrix p n 𝕜)
    (h : LinearMap.ker M.mulVecLin ≤ LinearMap.ker N.mulVecLin) : N.rank ≤ M.rank := by
  have hM := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hN := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  have hker : Module.finrank 𝕜 (LinearMap.ker M.mulVecLin)
      ≤ Module.finrank 𝕜 (LinearMap.ker N.mulVecLin) := Submodule.finrank_mono h
  unfold Matrix.rank
  omega

omit [Fintype m] in
/-- **Full column rank makes `mulVec` injective**: `rank M = #columns` forces the kernel of
`M.mulVecLin` to be trivial (rank–nullity). -/
theorem mulVec_injective_of_rank_eq_card (M : Matrix m n 𝕜) (h : M.rank = Fintype.card n) :
    Function.Injective M.mulVec := by
  have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hdom : Module.finrank 𝕜 (n → 𝕜) = Fintype.card n := by simp
  have hrank : Module.finrank 𝕜 (LinearMap.range M.mulVecLin) = M.rank := rfl
  have hker0 : Module.finrank 𝕜 (LinearMap.ker M.mulVecLin) = 0 := by omega
  have hbot : LinearMap.ker M.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hker0
  have hinj := LinearMap.ker_eq_bot.mp hbot
  intro x y hxy
  exact hinj (by simpa [Matrix.mulVecLin_apply] using hxy)

omit [Fintype m] in
/-- A matrix of rank `≤ k` over a field factors as `A * Bᵀ` through an inner index `Fin k`,
**minimally**: in addition to `M = A Bᵀ`,
* (i) `B`'s columns beyond `M.rank` vanish, and
* (ii) `A`'s columns on the support `{l | (l : ℕ) < M.rank}` are linearly independent.
These facts are what the rank-preserving leaf-removal reduction in
`TTN/Landscape/RealizabilityConverse.lean` needs. Its unfolded eliminator for
(ii) is `eq_zero_of_sum_smul_col_eq_zero`. -/
theorem exists_factor_of_rank_le [Finite m] (M : Matrix m n 𝕜) {k : ℕ} (hk : M.rank ≤ k) :
    ∃ (A : Matrix m (Fin k) 𝕜) (B : Matrix n (Fin k) 𝕜), M = A * Bᵀ ∧
      (∀ (l : Fin k), M.rank ≤ (l : ℕ) → ∀ j, B j l = 0) ∧
      LinearIndependent 𝕜 (fun l : Fin M.rank => A.col (Fin.castLE hk l)) := by
  letI := Fintype.ofFinite m
  classical
  set s : Submodule 𝕜 (m → 𝕜) := span 𝕜 (Set.range M.col) with hs
  have hdk : Module.finrank 𝕜 s ≤ k := by
    rw [hs, ← rank_eq_finrank_span_cols]; exact hk
  set d := Module.finrank 𝕜 s with hd
  have hdM : M.rank = d := by rw [hd, hs, rank_eq_finrank_span_cols]
  let Bs : Module.Basis (Fin d) 𝕜 s := Module.finBasis 𝕜 s
  let b : Fin d → (m → 𝕜) := fun i => (Bs i : m → 𝕜)
  let A' : Fin k → (m → 𝕜) := fun i => if h : (i : ℕ) < d then b ⟨i, h⟩ else 0
  have hA'0 : ∀ l : Fin k, ¬ (l : ℕ) < d → A' l = 0 := by
    intro l hl
    change (if h : (↑l : ℕ) < d then b ⟨↑l, h⟩ else 0) = 0
    rw [dif_neg hl]
  have hspan_b : span 𝕜 (Set.range b) = s := by
    have hbc : Set.range b = s.subtype '' (Set.range Bs) := by rw [← Set.range_comp]; rfl
    rw [hbc, ← Submodule.map_span, Bs.span_eq, Submodule.map_subtype_top]
  have hsub : Set.range b ⊆ Set.range A' := by
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨↑i, i.2.trans_le hdk⟩, ?_⟩
    change (if h : (↑i : ℕ) < d then b ⟨↑i, h⟩ else 0) = b i
    rw [dif_pos i.2]
  have hsle : s ≤ span 𝕜 (Set.range A') := by rw [← hspan_b]; exact span_mono hsub
  have hcol : ∀ j, M.col j ∈ span 𝕜 (Set.range A') := by
    intro j; apply hsle; rw [hs]; exact subset_span ⟨j, rfl⟩
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun 𝕜).mp (hcol j)
  refine ⟨Matrix.of (fun i l => A' l i),
    Matrix.of (fun j l => if (l : ℕ) < M.rank then c j l else 0), ?_, ?_, ?_⟩
  · -- `M = A Bᵀ`: the dropped (tail) `B`-columns multiply zero `A`-columns, so vanish.
    ext i j
    rw [Matrix.mul_apply]
    have hcj : M i j = (∑ l, c j l • A' l) i := by rw [hc j]; rfl
    rw [hcj, Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Matrix.of_apply, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hl : (l : ℕ) < M.rank
    · rw [if_pos hl]; ring
    · rw [if_neg hl, hA'0 l (by rw [hdM] at hl; exact hl)]; simp
  · -- (i) `B`'s tail columns vanish by construction.
    intro l hl j
    simp only [Matrix.of_apply]
    rw [if_neg (by omega)]
  · -- (ii) the supported columns are the basis `b` (reindexed), hence linearly independent.
    have hbli : LinearIndependent 𝕜 b := Bs.linearIndependent.map' s.subtype s.ker_subtype
    have hinj : Function.Injective (fun l : Fin M.rank => (⟨l.1, hdM ▸ l.2⟩ : Fin d)) := by
      intro l₁ l₂ h12
      have h12' := congrArg Fin.val h12
      exact Fin.ext h12'
    have hfam : (fun l : Fin M.rank =>
          (Matrix.of (fun i l => A' l i)).col (Fin.castLE hk l))
        = b ∘ (fun l : Fin M.rank => (⟨l.1, hdM ▸ l.2⟩ : Fin d)) := by
      funext l
      funext i
      change A' (Fin.castLE hk l) i = b ⟨l.1, hdM ▸ l.2⟩ i
      have hlt : ((Fin.castLE hk l : Fin k) : ℕ) < d := hdM ▸ l.2
      change (if h : ((Fin.castLE hk l : Fin k) : ℕ) < d then b ⟨_, h⟩ else 0) i
        = b ⟨l.1, hdM ▸ l.2⟩ i
      rw [dif_pos hlt]
      rfl
    rw [hfam]
    exact hbli.comp _ hinj

omit [Fintype m] in
/-- **Unfolded eliminator** for the column-independence conclusion of
`exists_factor_of_rank_le`: a coefficient family supported on `{l | (l : ℕ) < r}` that
annihilates the columns of `A` is zero. This is the raw form the leaf-removal reduction
(`reduced_rankBound`) consumes. -/
theorem eq_zero_of_sum_smul_col_eq_zero {k r : ℕ} {A : Matrix m (Fin k) 𝕜} (hrk : r ≤ k)
    (hli : LinearIndependent 𝕜 (fun l : Fin r => A.col (Fin.castLE hrk l)))
    (g : Fin k → 𝕜) (hg : ∀ l : Fin k, r ≤ (l : ℕ) → g l = 0)
    (hsum : (∑ l, g l • (fun i => A i l)) = 0) : g = 0 := by
  have hkey : (∑ i : Fin r, g (Fin.castLE hrk i) • A.col (Fin.castLE hrk i)) = 0 := by
    calc (∑ i : Fin r, g (Fin.castLE hrk i) • A.col (Fin.castLE hrk i))
        = ∑ l ∈ Finset.univ.map (Fin.castLEEmb hrk), g l • A.col l := by
          rw [Finset.sum_map]; rfl
      _ = ∑ l : Fin k, g l • A.col l := by
          refine Finset.sum_subset (Finset.subset_univ _) fun l _ hlnm => ?_
          have hnlt : ¬ (l : ℕ) < r := fun hlt =>
            hlnm (Finset.mem_map.mpr ⟨⟨l, hlt⟩, Finset.mem_univ _, by simp [Fin.castLEEmb]⟩)
          rw [hg l (Nat.le_of_not_lt hnlt), zero_smul]
      _ = 0 := hsum
  have hzero := Fintype.linearIndependent_iff.mp hli (fun i => g (Fin.castLE hrk i)) hkey
  funext l
  by_cases hl : (l : ℕ) < r
  · have hgl := hzero ⟨l, hl⟩
    rwa [show Fin.castLE hrk ⟨l, hl⟩ = l from by apply Fin.ext; rfl] at hgl
  · exact hg l (Nat.le_of_not_lt hl)

end Matrix
