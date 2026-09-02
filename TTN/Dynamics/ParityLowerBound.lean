import TTN.Dynamics.Parity

/-!
# The universal parity-saddle lower bound

This module formalizes Lemma I.2 and the universal lower-bound part of
Proposition 5.3 of the manuscript. For the `n = 2^k` input parity tree, the loss
at the halfway point cannot decrease faster than order `n / 2 + 1` under an
arbitrary sufficiently small parameter perturbation. Criticality and an
explicit strict-descent line are proved in `TTN.Dynamics.Parity`. The universal
bound here is distinct from any sharper statement about the exact saddle order.
-/

namespace TTN

namespace Arch

/-- Euclidean distance between two TTN parameter points, written using the
sum-of-squares parameter norm already used by `MinNorm`. -/
noncomputable def paramDist (a : Arch) (θ θ' : a.Param) : ℝ :=
  Real.sqrt (a.paramNormSq (fun v bi xv => θ v bi xv - θ' v bi xv))

theorem paramDist_nonneg (a : Arch) (θ θ' : a.Param) :
    0 ≤ a.paramDist θ θ' :=
  Real.sqrt_nonneg _

private theorem paramNormSq_nonneg (a : Arch) (θ : a.Param) :
    0 ≤ a.paramNormSq θ := by
  unfold paramNormSq nodeNormSq
  positivity

/-- Every parameter coordinate is bounded by the Euclidean parameter distance. -/
theorem abs_sub_le_paramDist (a : Arch) (θ θ' : a.Param) (v : a.V)
    (bi : a.BondIdx v) (xv : Fin (a.n v)) :
    |θ v bi xv - θ' v bi xv| ≤ a.paramDist θ θ' := by
  let δ : a.Param := fun w bj xj => θ w bj xj - θ' w bj xj
  have hx : (δ v bi xv) ^ 2 ≤ a.paramNormSq δ := by
    have h1 : (δ v bi xv) ^ 2 ≤ ∑ xj : Fin (a.n v), (δ v bi xj) ^ 2 :=
      Finset.single_le_sum (fun xj _ => sq_nonneg (δ v bi xj)) (Finset.mem_univ xv)
    have h2 : (∑ xj : Fin (a.n v), (δ v bi xj) ^ 2) ≤
        ∑ bj : a.BondIdx v, ∑ xj : Fin (a.n v), (δ v bj xj) ^ 2 :=
      Finset.single_le_sum
        (fun bj _ => Finset.sum_nonneg (fun xj _ => sq_nonneg (δ v bj xj)))
        (Finset.mem_univ bi)
    have h3 : a.nodeNormSq δ v ≤ ∑ w : a.V, a.nodeNormSq δ w :=
      Finset.single_le_sum (fun w _ => by unfold nodeNormSq; positivity) (Finset.mem_univ v)
    exact h1.trans (h2.trans h3)
  have hnorm : 0 ≤ a.paramNormSq δ := paramNormSq_nonneg a δ
  have hsqrt : (Real.sqrt (a.paramNormSq δ)) ^ 2 = a.paramNormSq δ := by
    rw [Real.sq_sqrt hnorm]
  have habs : |δ v bi xv| ^ 2 = (δ v bi xv) ^ 2 := sq_abs _
  have hsqrtnn : 0 ≤ Real.sqrt (a.paramNormSq δ) := Real.sqrt_nonneg _
  have habsnn : 0 ≤ |δ v bi xv| := abs_nonneg _
  change |δ v bi xv| ≤ Real.sqrt (a.paramNormSq δ)
  nlinarith

/-- Any set of parity-tree nodes containing every leaf and the root has at
least `n / 2 + 1` elements. -/
private theorem parityOrder_le_card_of_mandatory (k : ℕ) (hk : 2 ≤ k)
    (S : Finset (parityArch k hk).V)
    (hS : ∀ v : (parityArch k hk).V,
      heapLeaf (2 ^ k - 1) v ∨ v.val = 0 → v ∈ S) :
    2 ^ (k - 1) + 1 ≤ S.card := by
  classical
  let q : ℕ := 2 ^ (k - 1)
  let m : ℕ := 2 ^ k - 1
  have hkform : k = (k - 1) + 1 := by omega
  have hpow : 2 ^ k = 2 * q := by
    rw [hkform, pow_succ]
    simp only [q]
    ring
  have hqpos : 0 < q := by simp [q]
  have hqone : 1 < q := by
    have hkle : 1 ≤ k - 1 := by omega
    have : 2 ^ 1 ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) hkle
    change 1 < q
    dsimp only [q]
    norm_num at this ⊢
    omega
  have hmpos : 0 < m := by simp [m]; omega
  let root : Fin m := ⟨0, hmpos⟩
  let leafEmb : Fin q ↪ Fin m :=
    ⟨fun i => ⟨q - 1 + i.val, by omega⟩,
      fun i j hij => Fin.ext (by simpa using congrArg Fin.val hij)⟩
  let M : Finset (Fin m) := insert root (Finset.univ.map leafEmb)
  have hrootnot : root ∉ Finset.univ.map leafEmb := by
    rw [Finset.mem_map]
    rintro ⟨i, -, hi⟩
    have hval := congrArg Fin.val hi
    change q - 1 + i.val = 0 at hval
    omega
  have hcardM : M.card = q + 1 := by
    simp [M, hrootnot]
  have hMS : M ⊆ S := by
    intro v hv
    rw [Finset.mem_insert] at hv
    rcases hv with hv | hv
    · subst v
      exact hS root (Or.inr rfl)
    · rw [Finset.mem_map] at hv
      obtain ⟨i, -, rfl⟩ := hv
      apply hS
      left
      show m ≤ 2 * (q - 1 + i.val) + 1
      omega
  have hcard := Finset.card_le_card hMS
  change q + 1 ≤ S.card
  rwa [hcardM] at hcard

/-- The contribution to the parity coefficient in which exactly the nodes in
`S` use the perturbation and all other nodes use the halfway tensor. -/
private noncomputable def paritySubsetCoeff (k : ℕ) (hk : 2 ≤ k)
    (δ : (parityArch k hk).Param) (S : Finset (parityArch k hk).V) : ℝ :=
  ∑ x : (parityArch k hk).Ext, signProd hk x *
    ∑ b : (parityArch k hk).Bond,
      (∏ v ∈ S, δ v (Bond.restrict b v) (x v)) *
        ∏ v ∈ Finset.univ \ S,
          halfParam k hk v (Bond.restrict b v) (x v)

/-- Multilinearity expands the parity coefficient into its node-subset terms. -/
private theorem parityCoefficient_expand (k : ℕ) (hk : 2 ≤ k)
    (θ : (parityArch k hk).Param) :
    (∑ x : (parityArch k hk).Ext, signProd hk x *
        (parityArch k hk).represented θ x) =
      ∑ S ∈ (Finset.univ : Finset (parityArch k hk).V).powerset,
        paritySubsetCoeff k hk
          (fun v bi xv => θ v bi xv - halfParam k hk v bi xv) S := by
  classical
  let δ : (parityArch k hk).Param :=
    fun v bi xv => θ v bi xv - halfParam k hk v bi xv
  have hentry : ∀ (v : (parityArch k hk).V) (b : (parityArch k hk).Bond)
      (x : (parityArch k hk).Ext),
      θ v (Bond.restrict b v) (x v) =
        δ v (Bond.restrict b v) (x v) +
          halfParam k hk v (Bond.restrict b v) (x v) := by
    intro v b x
    dsimp only [δ]
    ring
  have hrep : ∀ x : (parityArch k hk).Ext,
      (parityArch k hk).represented θ x =
        ∑ S ∈ (Finset.univ : Finset (parityArch k hk).V).powerset,
          ∑ b : (parityArch k hk).Bond,
            (∏ v ∈ S, δ v (Bond.restrict b v) (x v)) *
              ∏ v ∈ Finset.univ \ S,
                halfParam k hk v (Bond.restrict b v) (x v) := by
    intro x
    show (∑ b : (parityArch k hk).Bond,
        ∏ v, θ v (Bond.restrict b v) (x v)) = _
    have hexpand : ∀ b : (parityArch k hk).Bond,
        (∏ v, θ v (Bond.restrict b v) (x v)) =
          ∑ S ∈ (Finset.univ : Finset (parityArch k hk).V).powerset,
            (∏ v ∈ S, δ v (Bond.restrict b v) (x v)) *
              ∏ v ∈ Finset.univ \ S,
                halfParam k hk v (Bond.restrict b v) (x v) := by
      intro b
      calc
        (∏ v, θ v (Bond.restrict b v) (x v)) =
            ∏ v, (δ v (Bond.restrict b v) (x v) +
              halfParam k hk v (Bond.restrict b v) (x v)) :=
          Finset.prod_congr rfl (fun v _ => hentry v b x)
        _ = _ := Finset.prod_add
          (fun v => δ v (Bond.restrict b v) (x v))
          (fun v => halfParam k hk v (Bond.restrict b v) (x v)) Finset.univ
    rw [Finset.sum_congr rfl (fun b _ => hexpand b)]
    rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x _ => by rw [hrep x, Finset.mul_sum])]
  unfold paritySubsetCoeff
  rw [Finset.sum_comm]

/-- Fubini for the external product coordinates. -/
private theorem sum_ext_prod_parity {a : Arch}
    (F : (v : a.V) → Fin (a.n v) → ℝ) :
    (∑ x : a.Ext, ∏ v, F v (x v)) = ∏ v, ∑ j, F v j := by
  classical
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rfl

/-- A subset term has zero parity coefficient unless every leaf and the root
are perturbed. -/
private theorem paritySubsetCoeff_zero_of_missing (k : ℕ) (hk : 2 ≤ k)
    (δ : (parityArch k hk).Param) (S : Finset (parityArch k hk).V)
    (v₀ : (parityArch k hk).V)
    (hv₀ : heapLeaf (2 ^ k - 1) v₀ ∨ v₀.val = 0) (hv₀S : v₀ ∉ S) :
    paritySubsetCoeff k hk δ S = 0 := by
  classical
  unfold paritySubsetCoeff
  rw [Finset.sum_congr rfl (fun x _ => by rw [Finset.mul_sum]), Finset.sum_comm]
  refine Finset.sum_eq_zero (fun b _ => ?_)
  let W : (parityArch k hk).Param := S.piecewise δ (halfParam k hk)
  have hpt : ∀ x : (parityArch k hk).Ext,
      signProd hk x *
          ((∏ v ∈ S, δ v (Bond.restrict b v) (x v)) *
            ∏ v ∈ Finset.univ \ S,
              halfParam k hk v (Bond.restrict b v) (x v)) =
        ∏ v, ((-1 : ℝ) ^ bitWeight (x v) * W v (Bond.restrict b v) (x v)) := by
    intro x
    rw [Finset.prod_mul_distrib]
    congr 1
    · simp only [signProd, totalBits]
      rw [Finset.prod_pow_eq_pow_sum]
    · show (∏ v ∈ S, δ v (Bond.restrict b v) (x v)) *
          ∏ v ∈ Finset.univ \ S,
            halfParam k hk v (Bond.restrict b v) (x v) =
          ∏ v, W v (Bond.restrict b v) (x v)
      rw [show (∏ v, W v (Bond.restrict b v) (x v)) =
          ∏ v, S.piecewise
            (fun w => δ w (Bond.restrict b w) (x w))
            (fun w => halfParam k hk w (Bond.restrict b w) (x w)) v from
        Finset.prod_congr rfl (fun v _ => by
          by_cases hv : v ∈ S
          · simp [W, hv]
          · simp [W, hv])]
      rw [Finset.prod_piecewise, Finset.univ_inter]
  rw [Finset.sum_congr rfl (fun x _ => hpt x),
    sum_ext_prod_parity (fun v j =>
      (-1 : ℝ) ^ bitWeight j * W v (Bond.restrict b v) j)]
  refine Finset.prod_eq_zero (Finset.mem_univ v₀) ?_
  rw [show W v₀ = halfParam k hk v₀ from by simp [W, hv₀S]]
  simp only [halfParam]
  rw [← Finset.sum_mul]
  rcases hv₀ with hleaf | hroot
  · have hn4 : (parityArch k hk).n v₀ = 4 := by
      show (if heapLeaf (2 ^ k - 1) v₀ then 4 else if v₀.val = 0 then 2 else 1) = 4
      rw [if_pos hleaf]
    have hsum : (∑ j : Fin ((parityArch k hk).n v₀),
        (-1 : ℝ) ^ bitWeight j) = 0 := by
      rw [hn4, Fin.sum_univ_four]
      norm_num [bitWeight]
    rw [hsum, zero_mul]
  · have h4pk : (4 : ℕ) ≤ 2 ^ k := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have hnleaf : ¬ heapLeaf (2 ^ k - 1) v₀ := by
      intro hleaf
      unfold heapLeaf at hleaf
      omega
    have hn2 : (parityArch k hk).n v₀ = 2 := by
      show (if heapLeaf (2 ^ k - 1) v₀ then 4 else if v₀.val = 0 then 2 else 1) = 2
      rw [if_neg hnleaf, if_pos hroot]
    have hsum : (∑ j : Fin ((parityArch k hk).n v₀),
        (-1 : ℝ) ^ bitWeight j) = 0 := by
      rw [hn2, Fin.sum_univ_two]
      norm_num [bitWeight]
    rw [hsum, zero_mul]

/-- Crude uniform bound for one subset term.  The deliberately generous
constant only counts bond and external assignments. -/
private theorem abs_paritySubsetCoeff_le (k : ℕ) (hk : 2 ≤ k)
    (δ : (parityArch k hk).Param) (S : Finset (parityArch k hk).V)
    (r : ℝ) (hr : 0 ≤ r)
    (hcoord : ∀ (v : (parityArch k hk).V) (bi : (parityArch k hk).BondIdx v)
      (xv : Fin ((parityArch k hk).n v)), |δ v bi xv| ≤ r) :
    |paritySubsetCoeff k hk δ S| ≤
      ((Fintype.card (parityArch k hk).Ext *
        Fintype.card (parityArch k hk).Bond : ℕ) : ℝ) * r ^ S.card := by
  classical
  let term : (parityArch k hk).Ext → (parityArch k hk).Bond → ℝ :=
    fun x b => signProd hk x *
      ((∏ v ∈ S, δ v (Bond.restrict b v) (x v)) *
        ∏ v ∈ Finset.univ \ S,
          halfParam k hk v (Bond.restrict b v) (x v))
  have hterm : ∀ (x : (parityArch k hk).Ext) (b : (parityArch k hk).Bond),
      |term x b| ≤ r ^ S.card := by
    intro x b
    have hδ : |∏ v ∈ S, δ v (Bond.restrict b v) (x v)| ≤ r ^ S.card := by
      rw [Finset.abs_prod]
      calc
        (∏ v ∈ S, |δ v (Bond.restrict b v) (x v)|) ≤ ∏ _v ∈ S, r := by
          exact Finset.prod_le_prod
            (fun v _ => abs_nonneg (δ v (Bond.restrict b v) (x v)))
            (fun v _ => hcoord v (Bond.restrict b v) (x v))
        _ = r ^ S.card := by rw [Finset.prod_const]
    have hhalf : |∏ v ∈ Finset.univ \ S,
        halfParam k hk v (Bond.restrict b v) (x v)| ≤ 1 := by
      rw [Finset.abs_prod]
      calc
        (∏ v ∈ Finset.univ \ S,
            |halfParam k hk v (Bond.restrict b v) (x v)|) ≤
            ∏ _v ∈ Finset.univ \ S, (1 : ℝ) := by
          exact Finset.prod_le_prod
            (fun v _ => abs_nonneg (halfParam k hk v (Bond.restrict b v) (x v)))
            (fun _v _ => by norm_num [halfParam])
        _ = 1 := by simp
    have hsign : |signProd hk x| = 1 := by
      simp [signProd]
    change |signProd hk x *
      ((∏ v ∈ S, δ v (Bond.restrict b v) (x v)) *
        ∏ v ∈ Finset.univ \ S,
          halfParam k hk v (Bond.restrict b v) (x v))| ≤ r ^ S.card
    rw [abs_mul, abs_mul, hsign, one_mul]
    calc
      |∏ v ∈ S, δ v (Bond.restrict b v) (x v)| *
          |∏ v ∈ Finset.univ \ S,
            halfParam k hk v (Bond.restrict b v) (x v)| ≤
          r ^ S.card * 1 :=
        mul_le_mul hδ hhalf (abs_nonneg _) (pow_nonneg hr _)
      _ = r ^ S.card := mul_one _
  unfold paritySubsetCoeff
  calc
    |∑ x : (parityArch k hk).Ext, signProd hk x *
        ∑ b : (parityArch k hk).Bond,
          (∏ v ∈ S, δ v (Bond.restrict b v) (x v)) *
            ∏ v ∈ Finset.univ \ S,
              halfParam k hk v (Bond.restrict b v) (x v)|
        ≤ ∑ x : (parityArch k hk).Ext,
            |signProd hk x *
              ∑ b : (parityArch k hk).Bond,
                (∏ v ∈ S, δ v (Bond.restrict b v) (x v)) *
                  ∏ v ∈ Finset.univ \ S,
                    halfParam k hk v (Bond.restrict b v) (x v)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : (parityArch k hk).Ext,
          ∑ _b : (parityArch k hk).Bond, r ^ S.card := by
      refine Finset.sum_le_sum (fun x _ => ?_)
      rw [Finset.mul_sum]
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun b _ => hterm x b))
    _ = ((Fintype.card (parityArch k hk).Ext *
          Fintype.card (parityArch k hk).Bond : ℕ) : ℝ) * r ^ S.card := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul]
      ring

/-- The parity coefficient of the unperturbed halfway tensor is zero. -/
private theorem parityCoefficient_half_eq_zero (k : ℕ) (hk : 2 ≤ k) :
    (∑ x : (parityArch k hk).Ext,
      signProd hk x * (parityArch k hk).represented (halfParam k hk) x) = 0 := by
  classical
  have hmpos : 0 < 2 ^ k - 1 := by
    have h4 : (4 : ℕ) ≤ 2 ^ k := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  let root : (parityArch k hk).V := ⟨0, hmpos⟩
  let zeroParam : (parityArch k hk).Param := fun _ _ _ => 0
  have hz := paritySubsetCoeff_zero_of_missing k hk zeroParam ∅ root
    (Or.inr rfl) (by simp)
  unfold paritySubsetCoeff at hz
  simpa only [Finset.prod_empty, Finset.sdiff_empty, one_mul, Arch.represented] using hz

/-- **Lemma I.2 (parity coefficient bound).** In the unit parameter ball around
the halfway point, the parity component of the represented-tensor difference is
bounded by a constant times `‖θ - θ₀‖ ^ (n / 2 + 1)`, where `n = 2^k`. -/
theorem parity_coefficient_order_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : (parityArch k hk).Param,
      (parityArch k hk).paramDist θ (halfParam k hk) ≤ 1 →
      |∑ x : (parityArch k hk).Ext, signProd hk x *
          ((parityArch k hk).represented θ x -
            (parityArch k hk).represented (halfParam k hk) x)| ≤
        C * (parityArch k hk).paramDist θ (halfParam k hk) ^
          (2 ^ (k - 1) + 1) := by
  classical
  let B : ℝ := ((Fintype.card (parityArch k hk).Ext *
    Fintype.card (parityArch k hk).Bond : ℕ) : ℝ)
  let P : ℝ :=
    (((Finset.univ : Finset (parityArch k hk).V).powerset.card : ℕ) : ℝ)
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  refine ⟨P * B + 1, by positivity, ?_⟩
  intro θ hdist
  let δ : (parityArch k hk).Param :=
    fun v bi xv => θ v bi xv - halfParam k hk v bi xv
  let r : ℝ := (parityArch k hk).paramDist θ (halfParam k hk)
  have hr : 0 ≤ r := by
    exact paramDist_nonneg _ _ _
  have hrone : r ≤ 1 := hdist
  have hcoord : ∀ (v : (parityArch k hk).V)
      (bi : (parityArch k hk).BondIdx v)
      (xv : Fin ((parityArch k hk).n v)), |δ v bi xv| ≤ r := by
    intro v bi xv
    exact abs_sub_le_paramDist (parityArch k hk) θ (halfParam k hk) v bi xv
  have hpair :
      (∑ x : (parityArch k hk).Ext, signProd hk x *
          ((parityArch k hk).represented θ x -
            (parityArch k hk).represented (halfParam k hk) x)) =
        ∑ S ∈ (Finset.univ : Finset (parityArch k hk).V).powerset,
          paritySubsetCoeff k hk δ S := by
    calc
      (∑ x : (parityArch k hk).Ext, signProd hk x *
          ((parityArch k hk).represented θ x -
            (parityArch k hk).represented (halfParam k hk) x)) =
          (∑ x : (parityArch k hk).Ext,
              signProd hk x * (parityArch k hk).represented θ x) -
            ∑ x : (parityArch k hk).Ext,
              signProd hk x *
                (parityArch k hk).represented (halfParam k hk) x := by
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl (fun x _ => mul_sub _ _ _)
      _ = (∑ S ∈ (Finset.univ : Finset (parityArch k hk).V).powerset,
            paritySubsetCoeff k hk δ S) - 0 := by
          rw [parityCoefficient_expand k hk θ, parityCoefficient_half_eq_zero k hk]
      _ = _ := sub_zero _
  have hsubset : ∀ S ∈ (Finset.univ : Finset (parityArch k hk).V).powerset,
      |paritySubsetCoeff k hk δ S| ≤ B * r ^ (2 ^ (k - 1) + 1) := by
    intro S hS
    by_cases hmandatory : ∀ v : (parityArch k hk).V,
        heapLeaf (2 ^ k - 1) v ∨ v.val = 0 → v ∈ S
    · have hdegree : 2 ^ (k - 1) + 1 ≤ S.card :=
        parityOrder_le_card_of_mandatory k hk S hmandatory
      calc
        |paritySubsetCoeff k hk δ S| ≤ B * r ^ S.card := by
          exact abs_paritySubsetCoeff_le k hk δ S r hr hcoord
        _ ≤ B * r ^ (2 ^ (k - 1) + 1) := by
          apply mul_le_mul_of_nonneg_left
          · exact pow_le_pow_of_le_one hr hrone hdegree
          · positivity
    · push Not at hmandatory
      obtain ⟨v, hv, hvS⟩ := hmandatory
      rw [paritySubsetCoeff_zero_of_missing k hk δ S v hv hvS]
      simpa only [abs_zero] using
        (mul_nonneg hB (pow_nonneg hr (2 ^ (k - 1) + 1)))
  rw [hpair]
  calc
    |∑ S ∈ (Finset.univ : Finset (parityArch k hk).V).powerset,
        paritySubsetCoeff k hk δ S| ≤
        ∑ S ∈ (Finset.univ : Finset (parityArch k hk).V).powerset,
          |paritySubsetCoeff k hk δ S| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ (Finset.univ : Finset (parityArch k hk).V).powerset,
          B * r ^ (2 ^ (k - 1) + 1) :=
      Finset.sum_le_sum (fun S hS => hsubset S hS)
    _ = P * (B * r ^ (2 ^ (k - 1) + 1)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rfl
    _ ≤ (P * B + 1) * r ^ (2 ^ (k - 1) + 1) := by
      have hrpow : 0 ≤ r ^ (2 ^ (k - 1) + 1) := pow_nonneg hr _
      calc
        P * (B * r ^ (2 ^ (k - 1) + 1)) =
            (P * B) * r ^ (2 ^ (k - 1) + 1) := by ring
        _ ≤ (P * B + 1) * r ^ (2 ^ (k - 1) + 1) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num)) hrpow

/-- Exact polarization of the squared loss around an arbitrary base point. -/
private theorem loss_difference_expansion (a : Arch) (Tstar : a.Ext → ℝ)
    (θ θ₀ : a.Param) :
    a.loss Tstar θ - a.loss Tstar θ₀ =
      (∑ x : a.Ext, a.residual Tstar θ₀ x *
        (a.represented θ x - a.represented θ₀ x)) +
      (1 / 2 : ℝ) * ∑ x : a.Ext,
        (a.represented θ x - a.represented θ₀ x) ^ 2 := by
  classical
  unfold loss residual
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  calc
    (1 / 2 : ℝ) *
        ∑ x : a.Ext,
          ((a.represented θ x - Tstar x) ^ 2 -
            (a.represented θ₀ x - Tstar x) ^ 2) =
      ∑ x : a.Ext,
        ((a.represented θ₀ x - Tstar x) *
            (a.represented θ x - a.represented θ₀ x) +
          (1 / 2 : ℝ) *
            (a.represented θ x - a.represented θ₀ x) ^ 2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun x _ => by ring)
    _ = (∑ x : a.Ext, (a.represented θ₀ x - Tstar x) *
          (a.represented θ x - a.represented θ₀ x)) +
        (1 / 2 : ℝ) * ∑ x : a.Ext,
          (a.represented θ x - a.represented θ₀ x) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- **Proposition 5.3 (universal parity-saddle lower bound).** For every
parameter perturbation in the unit Euclidean ball around the halfway point, the
loss decrease is no larger than order `n / 2 + 1`, with `n = 2^k`.

Together with `critical_halfParam` and `parity_saddle_achievable`, this proves
the formalized clauses of Proposition 5.3. -/
theorem parity_saddle_lower_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : (parityArch k hk).Param,
      (parityArch k hk).paramDist θ (halfParam k hk) ≤ 1 →
      (parityArch k hk).loss (parityTarget k hk) θ -
          (parityArch k hk).loss (parityTarget k hk) (halfParam k hk) ≥
        -C * (parityArch k hk).paramDist θ (halfParam k hk) ^
          (2 ^ (k - 1) + 1) := by
  obtain ⟨C, hC, hcoefficient⟩ := parity_coefficient_order_bound k hk
  refine ⟨C, hC, ?_⟩
  intro θ hdist
  let r : ℝ := (parityArch k hk).paramDist θ (halfParam k hk)
  let Q : ℝ := ∑ x : (parityArch k hk).Ext, signProd hk x *
    ((parityArch k hk).represented θ x -
      (parityArch k hk).represented (halfParam k hk) x)
  have hQabs : |Q| ≤ C * r ^ (2 ^ (k - 1) + 1) :=
    hcoefficient θ hdist
  have hQupper : Q ≤ C * r ^ (2 ^ (k - 1) + 1) :=
    (le_abs_self Q).trans hQabs
  have hr : 0 ≤ r := paramDist_nonneg _ _ _
  have hCr : 0 ≤ C * r ^ (2 ^ (k - 1) + 1) :=
    mul_nonneg hC.le (pow_nonneg hr _)
  have hrespair :
      (∑ x : (parityArch k hk).Ext,
        (parityArch k hk).residual (parityTarget k hk) (halfParam k hk) x *
          ((parityArch k hk).represented θ x -
            (parityArch k hk).represented (halfParam k hk) x)) =
        -(1 / 2 : ℝ) * Q := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by
      rw [congrFun (residual_halfParam k hk) x]
      ring)
  have hquad : 0 ≤ (1 / 2 : ℝ) *
      ∑ x : (parityArch k hk).Ext,
        ((parityArch k hk).represented θ x -
          (parityArch k hk).represented (halfParam k hk) x) ^ 2 := by
    positivity
  rw [loss_difference_expansion, hrespair]
  nlinarith

end Arch

end TTN
