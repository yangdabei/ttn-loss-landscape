import TTN.Contraction

/-!
# Shared parity-case specification

This trusted statement module defines the balanced binary parity architecture,
target tensor, halfway parameter point, and parameter distance used by
Proposition 5.3. It contains no target theorem from the Comparator certificate.
-/

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

/-- Euclidean distance between two TTN parameter points. -/
noncomputable def paramDist (a : Arch) (θ θ' : a.Param) : ℝ :=
  Real.sqrt (a.paramNormSq (fun v bi xv => θ v bi xv - θ' v bi xv))

end Arch

end TTN
