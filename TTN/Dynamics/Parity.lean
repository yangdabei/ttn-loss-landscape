import TTN.Landscape.Descent
import TTN.Dynamics.SaddleOrder

/-!
# The parity case study

This module defines the balanced binary parity tree (`n = 2^k` inputs, `2^k − 1`
nodes, and bond dimension `2`) and formalizes the halfway point used in the parity
appendix. At that point the represented tensor is constant `½`, the residual is
`R₀ = −½·u₋^{⊗(n+1)}`, and the loss is critical. An explicit coordinated
perturbation gives strict descent from this point. The manuscript's universal
order-`n / 2 + 1` lower bound is proved in `TTN.Dynamics.ParityLowerBound`.

Key simplifications:
* `θ₀ ≡ ½` makes `T₀ ≡ ½` a constant bond-sum (`2^{#edges}·(½)^m = ½` via the tree
  edge count), so the two-mode residual identity is POINTWISE arithmetic.
* The external-leg bookkeeping is uniform: `bitWeight (j : Fin d) = j/2 + j%2` counts
  input bits for leaf legs (`d = 4`), the output bit at the root (`d = 2`), and nothing
  at internal nodes (`d = 1`); `parityTarget x = 1` iff the total bit count is even,
  and `u₋^{⊗(n+1)}` reads `signProd x = (−1)^{totalBits x}`.
* Heap indexing (`parent i = (i−1)/2`) gives the balanced binary tree on `Fin m` for
  free; only its `IsTree` proof is real graph work (mirror `pathGraph_isAcyclic`'s
  invariant-coloring pattern with the ancestor predicate).
-/

open Asymptotics
open scoped Matrix

namespace TTN

namespace Arch

/-! ### The parity architecture (heap-indexed balanced binary tree) -/

/-- The heap parent relation on `Fin (2^k − 1)`: `j` is the parent of `i` iff
`i ≠ 0` and `j = (i − 1)/2`. -/
def heapRel (m : ℕ) (i j : Fin m) : Prop := i.val ≠ 0 ∧ j.val = (i.val - 1) / 2

/-- The balanced binary tree on `Fin m` via heap indexing (symmetrized, loopless). -/
def heapGraph (m : ℕ) : SimpleGraph (Fin m) := SimpleGraph.fromRel (heapRel m)

/-- A node of the heap tree is a **leaf** iff it has no left child in range. -/
def heapLeaf (m : ℕ) (i : Fin m) : Prop := m ≤ 2 * i.val + 1

instance (m : ℕ) (i : Fin m) : Decidable (heapLeaf m i) :=
  inferInstanceAs (Decidable (m ≤ 2 * i.val + 1))

/-! ### The heap tree is a tree (target 1 infrastructure) -/

/-- A `Prop`-valued invariant preserved by every step of a relation is preserved by its
reflexive–transitive closure. (Mirror of `SaddleOrder.reflTransGen_iff_invariant`.) -/
private theorem reflTransGen_iff_invariant {α : Type*} {R : α → α → Prop} {P : α → Prop}
    (hP : ∀ a b, R a b → (P a ↔ P b)) {v w : α} (h : Relation.ReflTransGen R v w) :
    (P v ↔ P w) := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hbc ih => exact ih.trans (hP _ _ hbc)

/-- Heap adjacency characterization: distinct nodes, one the parent of the other. -/
private theorem heapGraph_adj (m : ℕ) (i j : Fin m) :
    (heapGraph m).Adj i j ↔ i ≠ j ∧ (heapRel m i j ∨ heapRel m j i) :=
  SimpleGraph.fromRel_adj _ i j

/-- Along a chain of parent steps the node value can only decrease. -/
private theorem heapRel_reflTransGen_le {m : ℕ} {a b : Fin m}
    (h : Relation.ReflTransGen (heapRel m) a b) : b.val ≤ a.val := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => obtain ⟨_, hval⟩ := hbc; omega

/-- Every heap node reaches the root `0`. -/
private theorem heapGraph_reach_zero {m : ℕ} (hm : 0 < m) (x : Fin m) :
    (heapGraph m).Reachable x ⟨0, hm⟩ := by
  have key : ∀ n : ℕ, ∀ x : Fin m, x.val = n → (heapGraph m).Reachable x ⟨0, hm⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hxn
      rcases Nat.eq_zero_or_pos x.val with h0 | hpos
      · rw [show x = ⟨0, hm⟩ from Fin.ext h0]
      · have hlt : (x.val - 1) / 2 < m := by omega
        set p : Fin m := ⟨(x.val - 1) / 2, hlt⟩ with hp
        have hadj : (heapGraph m).Adj x p := by
          rw [heapGraph_adj]
          refine ⟨fun hxp => ?_, Or.inl ⟨by omega, rfl⟩⟩
          have := congrArg Fin.val hxp
          simp only [hp] at this
          omega
        have hpv : p.val < n := by rw [← hxn]; simp only [hp]; omega
        exact hadj.reachable.trans (ih p.val hpv p rfl)
  exact key x.val x rfl

/-- The heap tree is connected. -/
private theorem heapGraph_connected {m : ℕ} (hm : 0 < m) : (heapGraph m).Connected := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact ⟨fun u v => (heapGraph_reach_zero hm u).trans (heapGraph_reach_zero hm v).symm⟩

/-- The heap tree is acyclic: removing the edge `{c, p}` (child `c`, parent `p`) disconnects
the subtree of `c` (invariant: "`c` is an ancestor of `x`"). -/
private theorem heapGraph_isAcyclic (m : ℕ) : (heapGraph m).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro i j hij
  rw [SimpleGraph.isBridge_iff]
  intro hreach
  rw [heapGraph_adj] at hij
  obtain ⟨hne, hpar⟩ := hij
  have contra : ∀ c p : Fin m, heapRel m c p →
      ((heapGraph m).deleteEdges {s(c, p)}).Reachable c p → False := by
    intro c p hcp hr
    rw [SimpleGraph.reachable_eq_reflTransGen] at hr
    set P : Fin m → Prop := fun x => Relation.ReflTransGen (heapRel m) x c with hP
    have step : ∀ u w : Fin m, heapRel m u w → s(u, w) ≠ s(c, p) → (P u ↔ P w) := by
      intro u w huw hs
      constructor
      · intro hPu
        rcases Relation.ReflTransGen.cases_head hPu with heq | ⟨u', hu', hrest⟩
        · exfalso
          apply hs
          have hwp : w.val = p.val := by
            obtain ⟨_, hwv⟩ := huw; obtain ⟨_, hpv⟩ := hcp
            rw [heq] at hwv; omega
          rw [heq, show w = p from Fin.ext hwp]
        · have hu'w : u' = w := by
            apply Fin.ext
            obtain ⟨_, h1⟩ := hu'; obtain ⟨_, h2⟩ := huw; omega
          rw [show w = u' from hu'w.symm]; exact hrest
      · intro hPw
        exact Relation.ReflTransGen.head huw hPw
    have key : ∀ a b, ((heapGraph m).deleteEdges {s(c, p)}).Adj a b → (P a ↔ P b) := by
      intro a b hab
      rw [SimpleGraph.deleteEdges_adj] at hab
      obtain ⟨hadj, hnotcut⟩ := hab
      rw [Set.mem_singleton_iff] at hnotcut
      rw [heapGraph_adj] at hadj
      obtain ⟨habne, hstep⟩ := hadj
      rcases hstep with h1 | h1
      · exact step a b h1 hnotcut
      · exact (step b a h1 (by rw [Sym2.eq_swap]; exact hnotcut)).symm
    have hPP : P c ↔ P p := reflTransGen_iff_invariant key hr
    have hPc : P c := Relation.ReflTransGen.refl
    have hPp : ¬ P p := by
      intro hpp
      have hle := heapRel_reflTransGen_le hpp
      obtain ⟨hc0, hpv⟩ := hcp
      omega
    exact hPp (hPP.mp hPc)
  rcases hpar with h1 | h1
  · exact contra i j h1 hreach
  · exact contra j i h1 (by rw [Sym2.eq_swap]; exact hreach.symm)

/-- The heap tree on `Fin m` (`m ≥ 1`) is a tree. -/
private theorem heapGraph_isTree {m : ℕ} (hm : 0 < m) : (heapGraph m).IsTree := by
  rw [SimpleGraph.isTree_iff]
  exact ⟨heapGraph_connected hm, heapGraph_isAcyclic m⟩

/-- **The parity architecture**: `n = 2^k` inputs, `m = 2^k − 1`
nodes on the heap-indexed balanced binary tree, bond dimension `2` everywhere;
external dims: `4` at each leaf (two input bits), `2` at the root (output bit),
`1` at internal nodes. -/
noncomputable def parityArch (k : ℕ) (hk : 2 ≤ k) : Arch where
  V := Fin (2 ^ k - 1)
  G := heapGraph (2 ^ k - 1)
  dG := Classical.decRel _
  hT := heapGraph_isTree (by
    have h4 : (4 : ℕ) ≤ 2 ^ k := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega)
  r := fun _ => 2
  n := fun i => if heapLeaf (2 ^ k - 1) i then 4 else if i.val = 0 then 2 else 1
  hr := fun _ _ => by norm_num
  hn := fun i => by
    by_cases h1 : heapLeaf (2 ^ k - 1) i <;> by_cases h2 : i.val = 0 <;>
      simp [h1, h2]

/-! ### The halfway point, the parity target, and the two-mode data -/

/-- Bit weight of an external index: `j/2 + j%2`. Counts the two input bits at a leaf
(`Fin 4`), the output bit at the root (`Fin 2`), and `0` at internal nodes (`Fin 1`). -/
def bitWeight {d : ℕ} (j : Fin d) : ℕ := j.val / 2 + j.val % 2

/-- Total bit count of an external configuration. -/
noncomputable def totalBits {k : ℕ} {hk : 2 ≤ k} (x : (parityArch k hk).Ext) : ℕ :=
  ∑ v, bitWeight (x v)

/-- **The parity target**: output bit = XOR of the input bits, i.e. total bit count
even. (`T* = ½(u₊^{⊗(n+1)} + u₋^{⊗(n+1)})` in the two-mode frame.) -/
noncomputable def parityTarget (k : ℕ) (hk : 2 ≤ k) : (parityArch k hk).Ext → ℝ :=
  fun x => if Even (totalBits (hk := hk) x) then 1 else 0

/-- **The halfway point** `θ₀`: every node tensor identically `½`
(equivalently `½·u₊^{⊗3}` per node — the `u₊` mode learned, the `u₋` mode dormant). -/
noncomputable def halfParam (k : ℕ) (hk : 2 ≤ k) : (parityArch k hk).Param :=
  fun _ _ _ => (1 : ℝ) / 2

/-- The rank-one sign tensor `u₋^{⊗(n+1)}` in aggregated coordinates. -/
noncomputable def signProd {k : ℕ} (hk : 2 ≤ k) : (parityArch k hk).Ext → ℝ :=
  fun x => (-1 : ℝ) ^ totalBits (hk := hk) x

/-! ### The two-mode identities at `θ₀` -/

/-- **The halfway point represents the constant `½`**: all node tensors are constant
`½`, so the bond sum is `2^{#edges}·(½)^{#nodes} = ½` (tree edge count `m − 1`). -/
theorem represented_halfParam (k : ℕ) (hk : 2 ≤ k) :
    (parityArch k hk).represented (halfParam k hk) = fun _ => (1 : ℝ) / 2 := by
  funext x
  have hV : Fintype.card (parityArch k hk).V
      = Fintype.card (parityArch k hk).G.edgeSet + 1 := by
    rw [SimpleGraph.card_edgeSet, (parityArch k hk).hT.card_edgeFinset]
  have hr2 : ∀ e : (parityArch k hk).G.edgeSet, (parityArch k hk).r e.1 = 2 := fun _ => rfl
  have hBond : Fintype.card (parityArch k hk).Bond
      = 2 ^ Fintype.card (parityArch k hk).G.edgeSet := by
    show Fintype.card ((e : (parityArch k hk).G.edgeSet) → Fin ((parityArch k hk).r e.1)) = _
    simp only [Fintype.card_pi, Fintype.card_fin, hr2, Finset.prod_const, Finset.card_univ]
  have hprod : ∀ b : (parityArch k hk).Bond,
      (∏ v, (halfParam k hk) v (Bond.restrict b v) (x v))
        = (1 / 2 : ℝ) ^ Fintype.card (parityArch k hk).V := by
    intro b
    simp only [halfParam, Finset.prod_const, Finset.card_univ]
  show (∑ b : (parityArch k hk).Bond,
      ∏ v, (halfParam k hk) v (Bond.restrict b v) (x v)) = 1 / 2
  rw [Finset.sum_congr rfl (fun b _ => hprod b), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hBond, hV]
  push_cast
  rw [pow_succ, ← mul_assoc, ← mul_pow]
  norm_num

/-- **The two-mode residual identity.** At the halfway point,
`R₀ = −½·u₋^{⊗(n+1)}` — the `u₊` component of the parity target is exactly learned
and the `u₋` component is exactly the residual. Pointwise: `½ − [total even] =
−½·(−1)^{totalBits}`. -/
theorem residual_halfParam (k : ℕ) (hk : 2 ≤ k) :
    (parityArch k hk).residual (parityTarget k hk) (halfParam k hk)
      = fun x => -(1 / 2 : ℝ) * signProd hk x := by
  funext x
  have h1 : (parityArch k hk).represented (halfParam k hk) x = 1 / 2 :=
    congrFun (represented_halfParam k hk) x
  show (parityArch k hk).represented (halfParam k hk) x - parityTarget k hk x
      = -(1 / 2 : ℝ) * signProd hk x
  rw [h1]
  simp only [parityTarget, signProd]
  by_cases he : Even (totalBits (hk := hk) x)
  · rw [if_pos he, he.neg_one_pow]; norm_num
  · rw [if_neg he, (Nat.not_even_iff_odd.mp he).neg_one_pow]; norm_num

/-- **External-index Fubini**: the sum over all external configurations of a nodewise product
is the product over nodes of the per-node sums (mirror of `Descent.sum_bond_prod_edge`). -/
private theorem sum_ext_prod' {a : Arch} (F : (v : a.V) → Fin (a.n v) → ℝ) :
    (∑ x : a.Ext, ∏ v, F v (x v)) = ∏ v, ∑ j, F v j := by
  classical
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rfl

/-- **The halfway point is critical**: every directional derivative pairs
`u₋^{⊗(n+1)}` against a contraction that is constant-`½` on some non-updated LEAF's
external legs, and `∑_{j : Fin 4} (−1)^{bitWeight j} = 0` kills it. -/
theorem critical_halfParam (k : ℕ) (hk : 2 ≤ k) :
    (parityArch k hk).Critical (parityTarget k hk) (halfParam k hk) := by
  intro v δ
  have h4pk : (4 : ℕ) ≤ 2 ^ k := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  -- a non-updated leaf `w₀ ≠ v`
  obtain ⟨w₀, hw₀leaf, hw₀v⟩ :
      ∃ w₀ : (parityArch k hk).V, heapLeaf (2 ^ k - 1) w₀ ∧ w₀ ≠ v := by
    by_cases hv : v.val = 2 ^ k - 1 - 1
    · refine ⟨⟨2 ^ k - 1 - 2, by omega⟩, ?_, ?_⟩
      · show 2 ^ k - 1 ≤ 2 * (2 ^ k - 1 - 2) + 1; omega
      · exact Fin.ne_of_val_ne (by show 2 ^ k - 1 - 2 ≠ v.val; omega)
    · refine ⟨⟨2 ^ k - 1 - 1, by omega⟩, ?_, ?_⟩
      · show 2 ^ k - 1 ≤ 2 * (2 ^ k - 1 - 1) + 1; omega
      · exact Fin.ne_of_val_ne (by show 2 ^ k - 1 - 1 ≠ v.val; omega)
  have hn4 : (parityArch k hk).n w₀ = 4 := by
    show (if heapLeaf (2 ^ k - 1) w₀ then 4 else if w₀.val = 0 then 2 else 1) = 4
    rw [if_pos hw₀leaf]
  have hres : ∀ x, (parityArch k hk).residual (parityTarget k hk) (halfParam k hk) x
      = -(1 / 2 : ℝ) * signProd hk x := congrFun (residual_halfParam k hk)
  -- for each bond assignment, the paired contraction vanishes (zero factor at `w₀`)
  have key : ∀ b : (parityArch k hk).Bond,
      (∑ x : (parityArch k hk).Ext, signProd hk x
        * ∏ w, (Function.update (halfParam k hk) v δ) w (Bond.restrict b w) (x w)) = 0 := by
    intro b
    have hpt : ∀ x : (parityArch k hk).Ext,
        signProd hk x * ∏ w, (Function.update (halfParam k hk) v δ) w (Bond.restrict b w) (x w)
        = ∏ w, ((-1 : ℝ) ^ (bitWeight (x w))
            * (Function.update (halfParam k hk) v δ) w (Bond.restrict b w) (x w)) := by
      intro x
      rw [Finset.prod_mul_distrib]
      congr 1
      rw [signProd, totalBits, ← Finset.prod_pow_eq_pow_sum]
    rw [Finset.sum_congr rfl (fun x _ => hpt x),
      sum_ext_prod' (fun w j => (-1 : ℝ) ^ (bitWeight j)
        * (Function.update (halfParam k hk) v δ) w (Bond.restrict b w) j)]
    refine Finset.prod_eq_zero (Finset.mem_univ w₀) ?_
    have hupd : ∀ j, (Function.update (halfParam k hk) v δ) w₀ (Bond.restrict b w₀) j = 1 / 2 := by
      intro j; rw [Function.update_of_ne hw₀v]; rfl
    simp only [hupd]
    rw [← Finset.sum_mul]
    have hsum0 : (∑ j : Fin ((parityArch k hk).n w₀), (-1 : ℝ) ^ (bitWeight j)) = 0 := by
      rw [hn4, Fin.sum_univ_four]
      norm_num [bitWeight]
    rw [hsum0, zero_mul]
  have hrep : ∀ x, (parityArch k hk).represented (Function.update (halfParam k hk) v δ) x
      = ∑ b : (parityArch k hk).Bond, ∏ w,
          (Function.update (halfParam k hk) v δ) w (Bond.restrict b w) (x w) := fun _ => rfl
  calc (∑ x, (parityArch k hk).residual (parityTarget k hk) (halfParam k hk) x
          * (parityArch k hk).represented (Function.update (halfParam k hk) v δ) x)
      = ∑ x, -(1 / 2 : ℝ) * (signProd hk x
          * (parityArch k hk).represented (Function.update (halfParam k hk) v δ) x) :=
        Finset.sum_congr rfl (fun x _ => by rw [hres x]; ring)
    _ = -(1 / 2 : ℝ) * ∑ x, signProd hk x
          * (parityArch k hk).represented (Function.update (halfParam k hk) v δ) x := by
        rw [Finset.mul_sum]
    _ = -(1 / 2 : ℝ) * ∑ b : (parityArch k hk).Bond, (∑ x, signProd hk x
          * ∏ w, (Function.update (halfParam k hk) v δ) w (Bond.restrict b w) (x w)) := by
        congr 1
        rw [Finset.sum_congr rfl (fun x _ => by rw [hrep x, Finset.mul_sum])]
        rw [Finset.sum_comm]
    _ = -(1 / 2 : ℝ) * ∑ b : (parityArch k hk).Bond, (0 : ℝ) := by
        rw [Finset.sum_congr rfl (fun b _ => key b)]
    _ = 0 := by simp

/-! ### Explicit descent from the halfway point -/

/-- An explicit coordinated perturbation gives strict loss descent from the
halfway point. Along this chosen line, the loss increment is asymptotic to
`c * t ^ (n - 1)` for some `c < 0`, where `n = 2^k`. This certifies that the
critical halfway point is not a local minimum. The statement concerns this
particular line; it does not assert that `n - 1` is the smallest possible
descent order over all perturbations. -/
theorem parity_saddle_achievable (k : ℕ) (hk : 2 ≤ k) :
    ∃ (δ : (v : (parityArch k hk).V) → (parityArch k hk).NodeTensor v) (c : ℝ),
      c < 0 ∧
      ((fun t : ℝ =>
          (parityArch k hk).loss (parityTarget k hk)
            (fun v bi xv => halfParam k hk v bi xv + t * δ v bi xv)
          - (parityArch k hk).loss (parityTarget k hk) (halfParam k hk))
        ~[nhds 0] fun t : ℝ => c * t ^ (2 ^ k - 1)) ∧
      (∃ t₀ > (0 : ℝ), ∀ t : ℝ, 0 < t → t < t₀ →
        (parityArch k hk).loss (parityTarget k hk)
            (fun v bi xv => halfParam k hk v bi xv + t * δ v bi xv)
          < (parityArch k hk).loss (parityTarget k hk) (halfParam k hk)) := by
  have h4pk : (4 : ℕ) ≤ 2 ^ k := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  haveI : Nonempty (parityArch k hk).V := ⟨⟨0, by omega⟩⟩
  haveI : Nonempty (parityArch k hk).Ext := ⟨fun v => ⟨0, (parityArch k hk).hn v⟩⟩
  -- The two-mode data.
  set η : (E : (parityArch k hk).G.edgeSet) → Fin ((parityArch k hk).r E.1) → ℝ :=
    fun _ j => (if j.val = 0 then 1 else -1) / Real.sqrt 2 with hη_def
  set uvec : (v : (parityArch k hk).V) → Fin ((parityArch k hk).n v) → ℝ :=
    fun _ j => (-1 : ℝ) ^ (bitWeight j) with huvec_def
  -- `η` is a unit dormant direction killed by the constant unfoldings.
  have hηsum : ∀ E : (parityArch k hk).G.edgeSet,
      (∑ i : Fin ((parityArch k hk).r E.1), η E i) = 0 := by
    intro E
    show (∑ i : Fin 2, η E i) = 0
    rw [Fin.sum_univ_two]
    simp only [hη_def, Fin.val_zero, Fin.val_one]
    rw [if_true, if_neg (by decide : ¬ (1 : ℕ) = 0)]
    ring
  have hunit : ∀ E : (parityArch k hk).G.edgeSet, η E ⬝ᵥ η E = 1 := by
    intro E
    show (∑ i : Fin 2, η E i * η E i) = 1
    rw [Fin.sum_univ_two]
    simp only [hη_def, Fin.val_zero, Fin.val_one]
    rw [if_true, if_neg (by decide : ¬ (1 : ℕ) = 0)]
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    simp only [div_mul_div_comm, h2]
    norm_num
  have hη : ∀ (v : (parityArch k hk).V) (e : (parityArch k hk).Inc v),
      ((parityArch k hk).matE v e ((halfParam k hk) v))ᵀ *ᵥ η ⟨e.1, e.2.1⟩ = 0 := by
    intro v e
    funext col
    simp only [Matrix.mulVec, Matrix.transpose_apply, Pi.zero_apply, dotProduct]
    have hmat : ∀ i,
        (parityArch k hk).matE v e ((halfParam k hk) v) i col = (1 / 2 : ℝ) :=
      fun _ => rfl
    simp only [hmat]
    rw [← Finset.mul_sum, hηsum ⟨e.1, e.2.1⟩, mul_zero]
  -- Pointwise two-mode identities.
  have hres : ∀ x, (parityArch k hk).residual (parityTarget k hk) (halfParam k hk) x
      = -(1 / 2 : ℝ) * signProd hk x := congrFun (residual_halfParam k hk)
  have huvec_sign : ∀ x, (∏ v, uvec v (x v)) = signProd hk x := by
    intro x
    simp only [huvec_def, signProd, totalBits]
    rw [Finset.prod_pow_eq_pow_sum]
  have hsq : ∀ x, signProd hk x * signProd hk x = 1 := by
    intro x
    simp only [signProd]
    rw [← pow_add]
    exact Even.neg_one_pow ⟨totalBits (hk := hk) x, rfl⟩
  -- The leading pairing coefficient is `-½ * |Ext| < 0`.
  have hcval : (∑ x, (parityArch k hk).residual (parityTarget k hk) (halfParam k hk) x
      * ∏ v, uvec v (x v)) = -(1 / 2 : ℝ) * (Fintype.card (parityArch k hk).Ext : ℝ) := by
    have hstep : (∑ x, (parityArch k hk).residual (parityTarget k hk) (halfParam k hk) x
        * ∏ v, uvec v (x v)) = ∑ _x : (parityArch k hk).Ext, -(1 / 2 : ℝ) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [huvec_sign x, hres x, mul_assoc, hsq x, mul_one]
    rw [hstep, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hcneg : (∑ x, (parityArch k hk).residual (parityTarget k hk) (halfParam k hk) x
      * ∏ v, uvec v (x v)) < 0 := by
    rw [hcval]
    have hpos : 0 < (Fintype.card (parityArch k hk).Ext : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (parityArch k hk).Ext)
    linarith
  -- The coordinated perturbation is a pure-power move of degree `|V|`.
  have hrep : ∀ t : ℝ, (parityArch k hk).represented
        (fun v bi xv => (halfParam k hk) v bi xv
          + t * (parityArch k hk).dormantPerturb η uvec v bi xv)
      = fun x => (parityArch k hk).represented (halfParam k hk) x
        + t ^ (Fintype.card (parityArch k hk).V) * ∏ v, uvec v (x v) :=
    fun t => (parityArch k hk).represented_add_dormant_perturb
      (halfParam k hk) η hη hunit uvec t
  have hcardV : Fintype.card (parityArch k hk).V = 2 ^ k - 1 := Fintype.card_fin _
  have hN : 1 ≤ Fintype.card (parityArch k hk).V := Fintype.card_pos
  refine ⟨(parityArch k hk).dormantPerturb η uvec, _, hcneg, ?_, ?_⟩
  · -- Exact order along this chosen line.
    have hequiv := loss_pow_move_isEquivalent (a := parityArch k hk) (parityTarget k hk)
      (halfParam k hk) ((parityArch k hk).dormantPerturb η uvec)
      (N := Fintype.card (parityArch k hk).V) hN
      (fun x => ∏ v, uvec v (x v)) hrep (ne_of_lt hcneg)
    rw [hcardV] at hequiv
    exact hequiv
  · -- Strict descent along the same line.
    exact exists_loss_lt_of_pow_move (parityTarget k hk) (halfParam k hk)
      ((parityArch k hk).dormantPerturb η uvec) hN
      (fun x => ∏ v, uvec v (x v)) hrep hcneg

end Arch

end TTN
