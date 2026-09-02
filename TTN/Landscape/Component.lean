import TTN.Landscape.Dormant

/-!
# The rank-deficient component

At a minimum-norm point with a model-rank-deficient edge, the connected component
of deficient edges provides the data for the core descent:
the vertex set `S`, the edge set `K` (= ALL edges with both endpoints in `S`, each
deficient), unit dormant directions `η_E` on `K` (two-sided kill, from the minimum-norm
kernel identities), the
boundary-maximality fact (edges leaving `S` are full model rank), and the walk-crossing
connectivity fact used by `represented_add_corePerturb`.
-/

open scoped Matrix

namespace TTN

namespace Arch

variable {a : Arch}

/-- Two vertices joined by a **model-rank-deficient** edge. -/
def defAdj (θ : a.Param) (u v : a.V) : Prop :=
  ∃ h : a.G.Adj u v, (a.matricize h θ).rank < a.r s(u, v)

/-- Deficiency is orientation-free (`rank_matricizeOf_symm`). -/
theorem defAdj_symm (θ : a.Param) {u v : a.V} (h : defAdj θ u v) : defAdj θ v u := by
  obtain ⟨huv, hrank⟩ := h
  refine ⟨huv.symm, ?_⟩
  rw [a.matricize_eq_matricizeOf huv.symm θ, a.rank_matricizeOf_symm huv (a.represented θ),
    ← a.matricize_eq_matricizeOf huv θ]
  exact lt_of_lt_of_le hrank (le_of_eq (congrArg a.r Sym2.eq_swap))

/-- The graph of model-rank-deficient edges (a subgraph of `G` on the same vertices). -/
def Gdef (θ : a.Param) : SimpleGraph a.V where
  Adj := defAdj θ
  symm := ⟨fun _ _ h => defAdj_symm θ h⟩
  loopless := ⟨fun _ hv => a.G.irrefl hv.choose⟩

/-- A walk from inside a finite set to outside it crosses the boundary. -/
theorem exists_crossing_of_walk {V : Type*} {G : SimpleGraph V} {P : Finset V}
    {u v : V} (W : G.Walk u v) (hu : u ∈ P) (hv : v ∉ P) :
    ∃ y z : V, G.Adj z y ∧ z ∈ P ∧ y ∉ P := by
  classical
  revert hu hv
  induction W with
  | nil => intro hu hv; exact absurd hu hv
  | @cons x y' z' hadj W' ih =>
    intro hu hv
    by_cases hy : y' ∈ P
    · exact ih hy hv
    · exact ⟨y', x, hadj, hu, hy⟩

/-- **Tree edges inside a reachability class**: if `G` is a tree, `G' ≤ G`, and two
`G`-adjacent vertices are `G'`-reachable, the edge between them is a `G'`-edge. -/
theorem adj_of_reachable_of_le {V : Type*} {G G' : SimpleGraph V} (hT : G.IsTree)
    (hle : G' ≤ G) {u v : V} (huv : G.Adj u v) (hr : G'.Reachable u v) : G'.Adj u v := by
  classical
  obtain ⟨W'⟩ := hr
  have hedges : ∀ e ∈ W'.edges, e ∈ G.edgeSet := fun e he =>
    SimpleGraph.edgeSet_subset_edgeSet.mpr hle (W'.edges_subset_edgeSet he)
  have hmemW : s(u, v) ∈ (W'.transfer G hedges).edges :=
    (W'.transfer G hedges).edges_bypass_subset_edges (by
      show s(u, v) ∈ ((W'.transfer G hedges).toPath : G.Walk u v).edges
      rw [SimpleGraph.isAcyclic_iff_path_unique.mp hT.isAcyclic
        ((W'.transfer G hedges).toPath) (SimpleGraph.Path.singleton huv)]
      exact SimpleGraph.Path.mk'_mem_edges_singleton huv)
  exact W'.adj_of_mem_edges (by rwa [SimpleGraph.Walk.edges_transfer] at hmemW)

/-- A positive-dimensional dormant subspace contains a unit vector. -/
theorem exists_unit_dormant {u w : a.V} (h : a.G.Adj u w) {θ : a.Param}
    (hpos : 0 < Module.finrank ℝ (a.dormant h θ)) :
    ∃ η : Fin (a.r s(u, w)) → ℝ, η ⬝ᵥ η = 1 ∧ η ∈ a.dormant h θ := by
  have hne : a.dormant h θ ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hpos
    exact absurd hpos (lt_irrefl 0)
  obtain ⟨x, hxmem, hx0⟩ := (Submodule.ne_bot_iff _).mp hne
  have hxx : 0 < x ⬝ᵥ x := dotProduct_self_pos hx0
  set c : ℝ := Real.sqrt (x ⬝ᵥ x) with hcdef
  have hcpos : 0 < c := Real.sqrt_pos.mpr hxx
  have hcc : c * c = x ⬝ᵥ x := Real.mul_self_sqrt hxx.le
  have hcne : c ≠ 0 := ne_of_gt hcpos
  refine ⟨c⁻¹ • x, ?_, Submodule.smul_mem _ _ hxmem⟩
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hcc]
  field_simp

/-- **The rank-deficient component.** At a minimum-norm point with a
deficient edge `s(u*, w*)`, there are `S` (the component's vertices), `K` (its edges), and
unit dormant directions `η` with:
1. `u* ∈ S`; 2. the starting edge is in `K`; 3. `K`-edges have both endpoints in `S`;
4. every edge with both endpoints in `S` is in `K`; 5. `K`-edges are deficient (any
orientation); 6. edges leaving `S` are full model rank (maximality); 7. `η` is killed by
the `θ`-unfolding at both endpoints of every `K`-edge; 8. `η` is unit on `K`;
9. every proper nonempty subset of `S` is left by a `K`-edge (the connectivity hypothesis
of `represented_add_corePerturb`). -/
theorem exists_deficient_component {θ : a.Param} (hmn : a.MinNorm θ)
    {ustar wstar : a.V} (hstar : a.G.Adj ustar wstar)
    (hdef : (a.matricize hstar θ).rank < a.r s(ustar, wstar)) :
    ∃ (S : Finset a.V) (K : Finset a.G.edgeSet)
      (η : (E : a.G.edgeSet) → Fin (a.r E.1) → ℝ),
      ustar ∈ S ∧
      (⟨s(ustar, wstar), by rw [SimpleGraph.mem_edgeSet]; exact hstar⟩ : a.G.edgeSet) ∈ K ∧
      (∀ E ∈ K, ∀ v : a.V, v ∈ E.1 → v ∈ S) ∧
      (∀ E : a.G.edgeSet, (∀ v : a.V, v ∈ E.1 → v ∈ S) → E ∈ K) ∧
      (∀ E ∈ K, ∀ (u w : a.V) (h : a.G.Adj u w), s(u, w) = E.1 →
        (a.matricize h θ).rank < a.r s(u, w)) ∧
      (∀ E : a.G.edgeSet, E ∉ K → ∀ (u w : a.V) (h : a.G.Adj u w), s(u, w) = E.1 →
        u ∈ S → (a.matricize h θ).rank = a.r s(u, w)) ∧
      (∀ (v : a.V) (e : a.Inc v), (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ K →
        (a.matE v e (θ v))ᵀ *ᵥ η ⟨e.1, e.2.1⟩ = 0) ∧
      (∀ E ∈ K, η E ⬝ᵥ η E = 1) ∧
      (∀ P ⊆ S, P.Nonempty → P ≠ S →
        ∃ (y z : a.V) (hyz : a.G.Adj y z), y ∉ P ∧ z ∈ P ∧
          (⟨s(y, z), by rw [SimpleGraph.mem_edgeSet]; exact hyz⟩ : a.G.edgeSet) ∈ K) := by
  classical
  -- the component vertex set: everything `Gdef`-reachable from `u*`
  set S : Finset a.V := Finset.univ.filter (fun v => (a.Gdef θ).Reachable ustar v) with hSdef
  have hmemS : ∀ v : a.V, v ∈ S ↔ (a.Gdef θ).Reachable ustar v := fun v => by
    rw [hSdef, Finset.mem_filter]
    exact ⟨fun hv => hv.2, fun hv => ⟨Finset.mem_univ v, hv⟩⟩
  -- the component edge set: ALL edges with both endpoints in `S`
  set K : Finset a.G.edgeSet :=
    Finset.univ.filter (fun E : a.G.edgeSet => ∀ v : a.V, v ∈ E.1 → v ∈ S) with hKdef
  have hmemK : ∀ E : a.G.edgeSet, E ∈ K ↔ ∀ v : a.V, v ∈ E.1 → v ∈ S := fun E => by
    rw [hKdef, Finset.mem_filter]
    exact ⟨fun hE => hE.2, fun hE => ⟨Finset.mem_univ E, hE⟩⟩
  -- sublemma A: `S` is closed under deficient adjacency
  have hclosed : ∀ {p q : a.V}, p ∈ S → defAdj θ p q → q ∈ S := by
    intro p q hp hpq
    rw [hmemS] at hp ⊢
    exact hp.trans (SimpleGraph.Adj.reachable hpq)
  have hle : a.Gdef θ ≤ a.G := fun p q hpq => hpq.choose
  -- sublemma B: `G`-edges inside `S` are deficient (tree-unique-path argument)
  have hSadj : ∀ {p q : a.V}, p ∈ S → q ∈ S → a.G.Adj p q → defAdj θ p q := by
    intro p q hp hq hpq
    rw [hmemS] at hp hq
    exact adj_of_reachable_of_le a.hT hle hpq (hp.symm.trans hq)
  have hustarS : ustar ∈ S := (hmemS ustar).mpr (SimpleGraph.Reachable.refl ustar)
  have hwstarS : wstar ∈ S := hclosed hustarS ⟨hstar, hdef⟩
  -- conjunct 5: `K`-edges are deficient at every orientation
  have hKdefic : ∀ E ∈ K, ∀ (p q : a.V) (h : a.G.Adj p q), s(p, q) = E.1 →
      (a.matricize h θ).rank < a.r s(p, q) := by
    intro E hEK p q h hsw
    have hp : p ∈ S := (hmemK E).mp hEK p (by rw [← hsw]; exact Sym2.mem_mk_left p q)
    have hq : q ∈ S := (hmemK E).mp hEK q (by rw [← hsw]; exact Sym2.mem_mk_right p q)
    obtain ⟨h', hrank'⟩ := hSadj hp hq h
    exact hrank'
  -- per-edge unit dormant directions on `K` (cast-free `Sym2.ind` form)
  have hpere : ∀ (Ev : Sym2 a.V) (hEmem : Ev ∈ a.G.edgeSet),
      (⟨Ev, hEmem⟩ : a.G.edgeSet) ∈ K →
      ∃ ηE : Fin (a.r Ev) → ℝ, ηE ⬝ᵥ ηE = 1 ∧
        ∀ (v : a.V) (hv : v ∈ Ev), (a.matE v ⟨Ev, hEmem, hv⟩ (θ v))ᵀ *ᵥ ηE = 0 := by
    intro Ev
    induction Ev using Sym2.ind with
    | _ p q =>
      intro hEmem hKmem
      have hpq : a.G.Adj p q := by rwa [SimpleGraph.mem_edgeSet] at hEmem
      have hlt : (a.matricize hpq θ).rank < a.r s(p, q) :=
        hKdefic ⟨s(p, q), hEmem⟩ hKmem p q hpq rfl
      have hcount := a.minNorm_rank_add_finrank_dormant hpq hmn
      have hpos : 0 < Module.finrank ℝ (a.dormant hpq θ) := by omega
      obtain ⟨ηE, hunit, hmem⟩ := exists_unit_dormant hpq hpos
      obtain ⟨hd1, hd2⟩ := Submodule.mem_inf.mp hmem
      refine ⟨ηE, hunit, ?_⟩
      intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hd1
        exact hd1
      · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hd2
        exact hd2
  choose ηf hunit' hkill' using fun (E : a.G.edgeSet) (hEK : E ∈ K) => hpere E.1 E.2 hEK
  set η : (E : a.G.edgeSet) → Fin (a.r E.1) → ℝ :=
    fun E => if hEK : E ∈ K then ηf E hEK else 0 with hη
  refine ⟨S, K, η, hustarS, ?_, fun E hEK => (hmemK E).mp hEK,
    fun E hE => (hmemK E).mpr hE, hKdefic, ?_, ?_, ?_, ?_⟩
  · -- conjunct 2: the starting edge is in `K`
    rw [hmemK]
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact hustarS
    · exact hwstarS
  · -- conjunct 6: edges leaving `S` are full model rank (maximality)
    intro E hEK p q h hsw hp
    by_contra hne
    have hlt : (a.matricize h θ).rank < a.r s(p, q) :=
      lt_of_le_of_ne (a.matricize_rank_le h θ) hne
    have hq : q ∈ S := hclosed hp ⟨h, hlt⟩
    refine hEK ((hmemK E).mpr fun v hv => ?_)
    rw [← hsw] at hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact hp
    · exact hq
  · -- conjunct 7: two-sided kill at every `K`-edge
    intro v e heK
    have hβ : η (⟨e.1, e.2.1⟩ : a.G.edgeSet) = ηf ⟨e.1, e.2.1⟩ heK := by
      rw [hη]
      exact dif_pos heK
    rw [hβ]
    exact hkill' ⟨e.1, e.2.1⟩ heK v e.2.2
  · -- conjunct 8: unit norm on `K`
    intro E hEK
    have hβ : η E = ηf E hEK := by
      rw [hη]
      exact dif_pos hEK
    rw [hβ]
    exact hunit' E hEK
  · -- conjunct 9: every proper nonempty subset of `S` is left by a `K`-edge
    intro P hPS hPne hPneS
    obtain ⟨s₀, hs₀S, hs₀P⟩ : ∃ x ∈ S, x ∉ P := by
      by_contra hno
      exact hPneS (Finset.Subset.antisymm hPS fun x hx =>
        not_not.mp fun hxP => hno ⟨x, hx, hxP⟩)
    obtain ⟨z₀, hz₀⟩ := hPne
    have hreach : (a.Gdef θ).Reachable z₀ s₀ :=
      ((hmemS z₀).mp (hPS hz₀)).symm.trans ((hmemS s₀).mp hs₀S)
    obtain ⟨W⟩ := hreach
    obtain ⟨y, z, hzy, hzP, hyP⟩ := exists_crossing_of_walk W hz₀ hs₀P
    have hyS : y ∈ S := hclosed (hPS hzP) hzy
    refine ⟨y, z, hzy.choose.symm, hyP, hzP, (hmemK _).mpr fun v hv => ?_⟩
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact hyS
    · exact hPS hzP

end Arch

end TTN
