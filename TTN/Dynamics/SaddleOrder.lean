import TTN.Landscape.CoreDescent

/-!
# Saddle order along a pure-power move

The coordinated perturbation identity is available in two forms
(`TTN/Landscape/Descent.lean` `represented_add_dormant_perturb`, exponent `|V|`;
`TTN/Landscape/CoreDescent.lean` `represented_add_corePerturb`, exponent `|S|`), the loss
quadratic expansion is `loss_of_represented_add`, and strict local descent is
`exists_loss_lt_of_pow_move`. This file adds the
**asymptotic saddle-order reading** of a pure-power move, stated over the same
`hrep : ∀ t, T(θ + tδ) = T(θ) + t^N·U` interface that `exists_loss_lt_of_pow_move`
uses:

* `loss_pow_move` — the exact loss law `𝓛(t) = 𝓛(0) + c·t^N + ½t^{2N}‖U‖²`
  (glue over `loss_of_represented_add` at `s := t^N`);
* `loss_pow_move_isLittleO`: increment `= c·t^N + o(t^N)`
  at `t → 0`, unconditional (`N ≥ 1`);
* `loss_pow_move_isEquivalent` — exact order: with `c ≠ 0`, increment `~ c·t^N`,
  i.e. the saddle order along the line is EXACTLY `N`.

For a dormant mode passing through `ℓ` node tensors, these results identify the exponent
of the represented-tensor move with the loss's leading asymptotic order. A concrete scalar
path instance is included below.
-/

open Asymptotics

namespace TTN

namespace Arch

variable {a : Arch}

/-- **Exact loss law along a pure-power move.** If the perturbation line moves the represented tensor by
exactly `t^N·U` (the `hrep` interface of `exists_loss_lt_of_pow_move`), the loss along the line is exactly
`𝓛(0) + c·t^N + ½·t^{2N}·‖U‖²` with `c = ⟨R, U⟩` — a polynomial identity in `t`. -/
theorem loss_pow_move (Tstar : a.Ext → ℝ) (θ : a.Param)
    (δ : (v : a.V) → a.NodeTensor v) {N : ℕ} (Uf : a.Ext → ℝ)
    (hrep : ∀ t : ℝ, a.represented (fun v bi xv => θ v bi xv + t * δ v bi xv)
      = fun x => a.represented θ x + t ^ N * Uf x) (t : ℝ) :
    a.loss Tstar (fun v bi xv => θ v bi xv + t * δ v bi xv)
      = a.loss Tstar θ + t ^ N * (∑ x, a.residual Tstar θ x * Uf x)
        + t ^ (2 * N) * ((1 : ℝ) / 2 * ∑ x, (Uf x) ^ 2) := by
  rw [a.loss_of_represented_add Tstar θ _ (t ^ N) Uf (hrep t), ← pow_mul,
    Nat.mul_comm N 2]

/-- **Saddle order, little-o reading.** Along a pure-power move the loss increment minus its leading `c·t^N`
term is `o(t^N)` at `t → 0`; the remainder is the explicit `½t^{2N}‖U‖²` and
`2N > N` since `N ≥ 1`. Unconditional in `c`. -/
theorem loss_pow_move_isLittleO (Tstar : a.Ext → ℝ) (θ : a.Param)
    (δ : (v : a.V) → a.NodeTensor v) {N : ℕ} (hN : 1 ≤ N) (Uf : a.Ext → ℝ)
    (hrep : ∀ t : ℝ, a.represented (fun v bi xv => θ v bi xv + t * δ v bi xv)
      = fun x => a.represented θ x + t ^ N * Uf x) :
    (fun t : ℝ => a.loss Tstar (fun v bi xv => θ v bi xv + t * δ v bi xv)
        - a.loss Tstar θ - t ^ N * (∑ x, a.residual Tstar θ x * Uf x))
      =o[nhds 0] fun t : ℝ => t ^ N := by
  let K : ℝ := (1 : ℝ) / 2 * ∑ x, (Uf x) ^ 2
  have hlt : N < 2 * N := lt_two_mul_self (Nat.succ_le_iff.mp hN)
  refine ((isLittleO_pow_pow (𝕜 := ℝ) hlt).const_mul_left K).congr_left ?_
  intro t
  rw [loss_pow_move Tstar θ δ Uf hrep t]
  dsimp [K]
  ring

/-- **Saddle order is exactly `N`**: when the leading residual pairing
`c = ⟨R, U⟩` is nonzero, the loss increment along a pure-power move is asymptotically
EQUIVALENT to `c·t^N` at `t → 0`. With `hrep` from `represented_add_dormant_perturb`
(`N = |V|`) or `represented_add_corePerturb` (`N = |S|`), this is the landscape side
of the `ℓ = N` identification. The descent result then picks `U` with `c < 0`; see
`exists_loss_lt_of_pow_move`. -/
theorem loss_pow_move_isEquivalent (Tstar : a.Ext → ℝ) (θ : a.Param)
    (δ : (v : a.V) → a.NodeTensor v) {N : ℕ} (hN : 1 ≤ N) (Uf : a.Ext → ℝ)
    (hrep : ∀ t : ℝ, a.represented (fun v bi xv => θ v bi xv + t * δ v bi xv)
      = fun x => a.represented θ x + t ^ N * Uf x)
    (hc : (∑ x, a.residual Tstar θ x * Uf x) ≠ 0) :
    (fun t : ℝ => a.loss Tstar (fun v bi xv => θ v bi xv + t * δ v bi xv)
        - a.loss Tstar θ)
      ~[nhds 0] fun t : ℝ => (∑ x, a.residual Tstar θ x * Uf x) * t ^ N := by
  rw [Asymptotics.IsEquivalent]
  change
    (fun t : ℝ => a.loss Tstar (fun v bi xv => θ v bi xv + t * δ v bi xv)
        - a.loss Tstar θ - (∑ x, a.residual Tstar θ x * Uf x) * t ^ N)
      =o[nhds 0] fun t : ℝ => (∑ x, a.residual Tstar θ x * Uf x) * t ^ N
  have hsmall :
      (fun t : ℝ => a.loss Tstar (fun v bi xv => θ v bi xv + t * δ v bi xv)
          - a.loss Tstar θ - (∑ x, a.residual Tstar θ x * Uf x) * t ^ N)
        =o[nhds 0] fun t : ℝ => t ^ N := by
    refine (loss_pow_move_isLittleO Tstar θ δ hN Uf hrep).congr_left ?_
    intro t
    ring
  exact hsmall.const_mul_right hc

/-! ### A concrete `ℓ = N` instance

The identification instance: the `ℓ`-node path with unit bond/external dims. Its ORIGIN is
a critical point (for `ℓ ≥ 2`: every directional derivative contains a zero factor); the
endpoint unfoldings vanish there, so with `r ≡ 1` dormancy is trivial, and the coordinated
all-ones move gives `T(t·𝟙) = t^ℓ`, the scalar factor model `s = a^ℓ`.
This is a minimal scalar-chain witness of order-`ℓ` saddles. The
dormant-mode/dynamics identification (gradient-flow slice-invariance) is NOT formalised.
-/

/-- A `Prop`-valued invariant that is preserved by every step of a relation is preserved
by its reflexive–transitive closure. -/
private theorem reflTransGen_iff_invariant {α : Type*} {R : α → α → Prop} {P : α → Prop}
    (hP : ∀ a b, R a b → (P a ↔ P b)) {v w : α} (h : Relation.ReflTransGen R v w) :
    (P v ↔ P w) := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hbc ih => exact ih.trans (hP _ _ hbc)

/-- The path graph on `Fin n` is acyclic: removing any edge `s(v,w)` disconnects the two
`v`/`w` sides of the linear order (the `≤ min v w` coloring is preserved by every surviving
edge but differs across the removed one). -/
private theorem pathGraph_isAcyclic (n : ℕ) : (SimpleGraph.pathGraph n).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro v w hvw
  rw [SimpleGraph.isBridge_iff]
  intro hreach
  rw [SimpleGraph.reachable_eq_reflTransGen] at hreach
  set m := min v.val w.val with hm
  have hvw' := SimpleGraph.pathGraph_adj.mp hvw
  have key : ∀ a b : Fin n,
      ((SimpleGraph.pathGraph n).deleteEdges {s(v, w)}).Adj a b →
        (a.val ≤ m ↔ b.val ≤ m) := by
    intro a b hab
    rw [SimpleGraph.deleteEdges_adj] at hab
    obtain ⟨hadj, hne⟩ := hab
    have hadj' := SimpleGraph.pathGraph_adj.mp hadj
    rw [Set.mem_singleton_iff] at hne
    by_contra hiff
    apply hne
    have hcase : (a.val = v.val ∧ b.val = w.val) ∨ (a.val = w.val ∧ b.val = v.val) := by
      omega
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Fin.ext h1, Fin.ext h2]
    · rw [Fin.ext h1, Fin.ext h2, Sym2.eq_swap]
  have hPP : (v.val ≤ m ↔ w.val ≤ m) :=
    reflTransGen_iff_invariant (P := fun x : Fin n => x.val ≤ m) (fun a b h => key a b h) hreach
  omega

/-- The path graph on `Fin ℓ` (`ℓ ≥ 1`) is a tree: connected (`pathGraph_connected`) and
acyclic (`pathGraph_isAcyclic`). -/
private theorem pathGraph_isTree {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : (SimpleGraph.pathGraph ℓ).IsTree := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ℓ ≠ 0)
  rw [SimpleGraph.isTree_iff]
  exact ⟨SimpleGraph.pathGraph_connected k, pathGraph_isAcyclic _⟩

/-- The path architecture on `Fin ℓ` with all bond and external dimensions `1`
(the scalar chain — the unreduced coordinates of the A1 depth-`ℓ` law). -/
noncomputable def pathArch (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : Arch where
  V := Fin ℓ
  G := SimpleGraph.pathGraph ℓ
  dG := Classical.decRel _
  hT := pathGraph_isTree hℓ
  r := fun _ => 1
  n := fun _ => 1
  hr := fun _ _ => one_pos
  hn := fun _ => one_pos

/-- The origin of any architecture with at least two nodes is a critical point: every
first-order variation retains at least one zero node factor. -/
theorem critical_zero {a : Arch} (hV : 2 ≤ Fintype.card a.V) (Tstar : a.Ext → ℝ) :
    a.Critical Tstar (fun _ _ _ => 0) := by
  intro v δ
  apply Finset.sum_eq_zero
  intro x _
  have hrep : a.represented (Function.update (fun _ _ _ => (0 : ℝ)) v δ) x = 0 := by
    simp only [Arch.represented]
    apply Finset.sum_eq_zero
    intro b _
    obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega) v
    refine Finset.prod_eq_zero (Finset.mem_univ w) ?_
    rw [Function.update_of_ne hw]
  rw [hrep, mul_zero]

/-- **A concrete `ℓ = N` identity.** On the `ℓ`-node unit
path (`ℓ ≥ 2`) with constant target `σ ≠ 0`, the origin is critical and the coordinated
all-ones direction has saddle order EXACTLY `ℓ`:
`𝓛(t·𝟙) − 𝓛(0) ~ (−σ)·t^ℓ` at `t → 0` (a DESCENT direction for `t > 0` when `σ > 0`;
sign-adjust otherwise). The exponent is `Fintype.card V = ℓ` (LL's core size `N` for the
full-tree core). Gradient-flow slice invariance is not formalized. -/
theorem pathArch_saddle_order {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {σ : ℝ} (hσ : σ ≠ 0) :
    (pathArch ℓ (by omega)).Critical (fun _ => σ) (fun _ _ _ => 0) ∧
    (fun t : ℝ =>
        (pathArch ℓ (by omega)).loss (fun _ => σ) (fun _ _ _ => (0 : ℝ) + t * 1)
          - (pathArch ℓ (by omega)).loss (fun _ => σ) (fun _ _ _ => 0))
      ~[nhds 0] fun t : ℝ => (-σ) * t ^ ℓ := by
  have hpos : 1 ≤ ℓ := by omega
  haveI hUB : Unique (pathArch ℓ hpos).Bond := by
    unfold Arch.Bond
    haveI : ∀ e : (pathArch ℓ hpos).G.edgeSet, Unique (Fin ((pathArch ℓ hpos).r e.1)) :=
      fun _ => inferInstanceAs (Unique (Fin 1))
    infer_instance
  haveI hUE : Unique (pathArch ℓ hpos).Ext := by
    unfold Arch.Ext
    haveI : ∀ v : (pathArch ℓ hpos).V, Unique (Fin ((pathArch ℓ hpos).n v)) :=
      fun _ => inferInstanceAs (Unique (Fin 1))
    infer_instance
  have hV : 2 ≤ Fintype.card (pathArch ℓ hpos).V := by
    change 2 ≤ Fintype.card (Fin ℓ); rw [Fintype.card_fin]; exact hℓ
  -- represented of a constant node tensor `c` is `c ^ ℓ`
  have hconst : ∀ (c : ℝ) (x : (pathArch ℓ hpos).Ext),
      (pathArch ℓ hpos).represented (fun _ _ _ => c) x = c ^ ℓ := by
    intro c x
    simp only [Arch.represented, Fintype.sum_unique, Finset.prod_const, Finset.card_univ]
    congr 1
    change Fintype.card (Fin ℓ) = ℓ
    exact Fintype.card_fin ℓ
  refine ⟨critical_zero hV _, ?_⟩
  -- the `hrep` interface, `N = ℓ`, `U = 1`
  have hrep : ∀ t : ℝ,
      (pathArch ℓ hpos).represented
          (fun v bi xv => (fun _ _ _ => (0:ℝ)) v bi xv + t * (fun _ _ _ => (1:ℝ)) v bi xv)
        = fun x => (pathArch ℓ hpos).represented (fun _ _ _ => (0:ℝ)) x
          + t ^ ℓ * (fun _ => (1:ℝ)) x := by
    intro t
    funext x
    have hL : (pathArch ℓ hpos).represented
        (fun v bi xv => (fun _ _ _ => (0:ℝ)) v bi xv + t * (fun _ _ _ => (1:ℝ)) v bi xv) x
        = (0 + t * 1) ^ ℓ := hconst (0 + t * 1) x
    rw [hL, hconst (0 : ℝ) x]
    simp [zero_pow (by omega : ℓ ≠ 0)]
  -- the leading coefficient equals `-σ`
  have hc : (∑ x, (pathArch ℓ hpos).residual (fun _ => σ) (fun _ _ _ => (0:ℝ)) x
      * (fun _ => (1:ℝ)) x) = -σ := by
    simp only [Arch.residual, hconst, Fintype.sum_unique]
    rw [zero_pow (by omega : ℓ ≠ 0)]
    ring
  have key := loss_pow_move_isEquivalent (a := pathArch ℓ hpos) (fun _ => σ)
    (fun _ _ _ => (0:ℝ)) (fun _ _ _ => (1:ℝ)) (N := ℓ) hpos (fun _ => (1:ℝ)) hrep
    (by rw [hc]; exact neg_ne_zero.mpr hσ)
  rw [hc] at key
  exact key

end Arch

end TTN
