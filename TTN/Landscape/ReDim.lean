import TTN.Landscape.Dormant

/-!
# Bond re-dimensioning and reduction

The reduction "WLOG the target has full bond rank" is implemented by a **bond re-dimension
functor**: `reDim a r'` is the same tree with new bond dimensions, and `mapParam ι` embeds
small-bond parameters into the big architecture along per-edge matrices
`ι_E : Matrix (Fin (r' E)) (Fin (r E)) ℝ` with **orthonormal rows** (`ι_E ι_Eᵀ = 1`), acting on
every bond mode of every node tensor.

* `represented_mapParam` — the embedding preserves the represented tensor (the per-edge Grams
  `ι ιᵀ = 1` collapse; the paper's "bond contractions factor through `ι_eᵀι_e = I`").
* `paramNormSq_mapParam` — and the parameter norm (per-node isometry on each bond mode).
* `realizable_reDim`: a target is realizable at the reduced
  bond dimensions `s_E := rank T*⁽ᴱ⁾` (the matricization does not depend on the bond dims, so
  realizability characterization applies verbatim).
* `exists_orthonormal_rows_ker_le`: an `s×r` matrix with
  orthonormal rows whose kernel sits inside a given subspace `D` of dimension `≥ r − s`
  (kernel-flavored substitute for the paper's "choose `S_e ⊇ A_e`"; here `ker ι ≤ D_e`).
* `compressParam` and its transfer lemmas (norm/loss equality on supported points, min-norm
  transfer, criticality transfer, local-min transfer, full target rank) — the five parts of
  the compression reduction.
-/

open scoped Matrix

namespace TTN

namespace Arch

variable {a : Arch}

/-- **Bond re-dimensioning**: the same tree and external dimensions, new bond dimensions. -/
def reDim (a : Arch) (r' : Sym2 a.V → ℕ) (hr' : ∀ e ∈ a.G.edgeSet, 0 < r' e) : Arch where
  V := a.V
  fV := a.fV
  dV := a.dV
  G := a.G
  dG := a.dG
  hT := a.hT
  r := r'
  n := a.n
  hr := hr'
  hn := a.hn

variable {r' : Sym2 a.V → ℕ} {hr' : ∀ e ∈ a.G.edgeSet, 0 < r' e}

/-- Transport an incidence of `a` to the re-dimensioned architecture (the graph is unchanged). -/
def toReDimInc {v : a.V} (e : a.Inc v) : (a.reDim r' hr').Inc v := ⟨e.1, e.2⟩

/-- Transport an incidence of the re-dimensioned architecture back to `a`. -/
def ofReDimInc {v : a.V} (e : (a.reDim r' hr').Inc v) : a.Inc v := ⟨e.1, e.2⟩

/-- **Parameter embedding along per-edge bond maps**: every bond mode of every node tensor is
hit by its edge's matrix `ι_E` (small index summed against the rows). -/
noncomputable def mapParam (ι : (E : a.G.edgeSet) → Matrix (Fin (r' E.1)) (Fin (a.r E.1)) ℝ)
    (θ' : (a.reDim r' hr').Param) : a.Param :=
  fun v bi xv => ∑ bi' : (a.reDim r' hr').BondIdx v,
    (∏ e : (a.reDim r' hr').Inc v, ι ⟨e.1, e.2.1⟩ (bi' e) (bi (ofReDimInc e))) * θ' v bi' xv

/-- Distribute a finite product of sums: `∏ v ∑ k, F v k = ∑ c ∏ v, F v (c v)`. -/
private theorem prod_sum_pi {V : Type*} [Fintype V] [DecidableEq V]
    {κ : V → Type*} [∀ v, Fintype (κ v)] (F : (v : V) → κ v → ℝ) :
    (∏ v, ∑ k : κ v, F v k) = ∑ c : (v : V) → κ v, ∏ v, F v (c v) := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- **Incidence-product regrouping, endpoint-dependent form**: a product of an
edge-and-endpoint function over all incidences of all nodes is the product over edges of the
product over that edge's endpoints (`prod_inc_eq_prod_edge_sq` without the final
multiplicity-two collapse). -/
theorem prod_inc_eq_prod_edge (g : (E : a.G.edgeSet) → a.V → ℝ) :
    (∏ v : a.V, ∏ e : a.Inc v, g ⟨e.1, e.2.1⟩ v)
      = ∏ E : a.G.edgeSet, ∏ v ∈ Finset.univ.filter (fun v => v ∈ E.1), g E v := by
  classical
  have hnode : ∀ v : a.V, (∏ e : a.Inc v, g ⟨e.1, e.2.1⟩ v)
      = ∏ E : a.G.edgeSet, (if v ∈ E.1 then g E v else 1) := by
    intro v
    let eqv : a.Inc v ≃ {E : a.G.edgeSet // v ∈ E.1} :=
      { toFun := fun e => ⟨⟨e.1, e.2.1⟩, e.2.2⟩
        invFun := fun E => ⟨E.1.1, E.1.2, E.2⟩
        left_inv := fun e => rfl
        right_inv := fun E => rfl }
    calc (∏ e : a.Inc v, g ⟨e.1, e.2.1⟩ v)
        = ∏ E : {E : a.G.edgeSet // v ∈ E.1}, g E.1 v :=
          Equiv.prod_comp eqv (fun E : {E : a.G.edgeSet // v ∈ E.1} => g E.1 v)
      _ = ∏ E ∈ Finset.univ.filter (fun E : a.G.edgeSet => v ∈ E.1), g E v :=
          (Finset.prod_subtype _ (fun E => by simp) (fun E => g E v)).symm
      _ = ∏ E : a.G.edgeSet, (if v ∈ E.1 then g E v else 1) := Finset.prod_filter _ _
  rw [Finset.prod_congr rfl (fun v _ => hnode v), Finset.prod_comm]
  exact Finset.prod_congr rfl (fun E _ => (Finset.prod_filter _ _).symm)

/-- **Per-edge pairing**: over the two endpoints of `s(p, q)`, the dite-product against a
matrix `A` with orthonormal rows (`A Aᵀ = 1`) sums to the diagonal indicator of the two
endpoint slots. -/
private theorem sum_prod_pair_ite {V : Type*} [Fintype V] [DecidableEq V]
    {p q : V} (hne : p ≠ q) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : A * Aᵀ = 1)
    (s : (v : V) → v ∈ s(p, q) → Fin m) :
    (∑ k : Fin n, ∏ v ∈ Finset.univ.filter (fun v => v ∈ s(p, q)),
        (if hv : v ∈ s(p, q) then A (s v hv) k else 1))
      = if s p (Sym2.mem_mk_left p q) = s q (Sym2.mem_mk_right p q) then 1 else 0 := by
  have hfilter : Finset.univ.filter (fun v : V => v ∈ s(p, q)) = {p, q} := by
    ext v
    simp [Sym2.mem_iff]
  calc (∑ k : Fin n, ∏ v ∈ Finset.univ.filter (fun v => v ∈ s(p, q)),
        (if hv : v ∈ s(p, q) then A (s v hv) k else 1))
      = ∑ k : Fin n,
          A (s p (Sym2.mem_mk_left p q)) k * A (s q (Sym2.mem_mk_right p q)) k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hfilter, Finset.prod_pair hne, dif_pos (Sym2.mem_mk_left p q),
          dif_pos (Sym2.mem_mk_right p q)]
    _ = (A * Aᵀ) (s p (Sym2.mem_mk_left p q)) (s q (Sym2.mem_mk_right p q)) := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun k _ => by rw [Matrix.transpose_apply]
    _ = if s p (Sym2.mem_mk_left p q) = s q (Sym2.mem_mk_right p q) then 1 else 0 := by
        rw [hA, Matrix.one_apply]

/-- **Bond-sum Fubini** (local copy of `TTN.Arch.sum_bond_prod_edge`, which lives in the
downstream module `TTN/Landscape/Descent.lean`): the sum over all bond assignments of an edgewise
product is the product over edges of the per-edge sums. -/
private theorem sum_bond_prod_edge' (f : (E : a.G.edgeSet) → Fin (a.r E.1) → ℝ) :
    (∑ b : a.Bond, ∏ E : a.G.edgeSet, f E (b E)) = ∏ E : a.G.edgeSet, ∑ k, f E k := by
  classical
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rfl

/-- The per-edge pairing collapses to `1` on slot families restricted from a global
re-dimensioned bond assignment (both endpoint slots read the same bond value). -/
private theorem sum_dite_restrict_eq_one
    (ι : (E : a.G.edgeSet) → Matrix (Fin (r' E.1)) (Fin (a.r E.1)) ℝ)
    (hortho : ∀ E, ι E * (ι E)ᵀ = 1) (b' : (a.reDim r' hr').Bond) (Ev : Sym2 a.V) :
    ∀ (hEmem : Ev ∈ a.G.edgeSet),
    (∑ k : Fin (a.r Ev), ∏ v ∈ Finset.univ.filter (fun v => v ∈ Ev),
        (if hv : v ∈ Ev then ι ⟨Ev, hEmem⟩ (Bond.restrict b' v ⟨Ev, hEmem, hv⟩) k else 1))
      = 1 := by
  induction Ev using Sym2.ind with
  | _ p q =>
    intro hEmem
    have hpq : a.G.Adj p q := by
      have h2 := hEmem
      rwa [SimpleGraph.mem_edgeSet] at h2
    exact (sum_prod_pair_ite hpq.ne (ι ⟨s(p, q), hEmem⟩) (hortho ⟨s(p, q), hEmem⟩)
      (fun v hv => Bond.restrict b' v ⟨s(p, q), hEmem, hv⟩)).trans (if_pos rfl)

/-- The embedding preserves the represented tensor when every `ι_E` has orthonormal rows. -/
theorem represented_mapParam (ι : (E : a.G.edgeSet) → Matrix (Fin (r' E.1)) (Fin (a.r E.1)) ℝ)
    (hortho : ∀ E, ι E * (ι E)ᵀ = 1) (θ' : (a.reDim r' hr').Param) :
    a.represented (mapParam ι θ') = (a.reDim r' hr').represented θ' := by
  classical
  funext x
  show (∑ b : a.Bond, ∏ v : a.V, mapParam ι θ' v (Bond.restrict b v) (x v))
    = ∑ b' : (a.reDim r' hr').Bond, ∏ v : a.V, θ' v (Bond.restrict b' v) (x v)
  -- the diagonal inclusion of re-dimensioned bond assignments into per-node slot families
  set Φ : (a.reDim r' hr').Bond → ((v : a.V) → (a.reDim r' hr').BondIdx v) :=
    fun b' v => Bond.restrict b' v with hΦdef
  -- an endpoint picker for every edge
  have hpick : ∀ (Ev : Sym2 a.V), Ev ∈ a.G.edgeSet →
      ∃ (v : a.V) (e : a.Inc v), e.1 = Ev := by
    intro Ev
    induction Ev using Sym2.ind with
    | _ p q => exact fun hEmem => ⟨p, ⟨s(p, q), hEmem, Sym2.mem_mk_left p q⟩, rfl⟩
  choose vE eE hEe using fun E : a.G.edgeSet => hpick E.1 E.2
  -- `Φ` is injective: read any edge slot off the restriction at a chosen endpoint
  have hΦinj : ∀ b₁ b₂ : (a.reDim r' hr').Bond, Φ b₁ = Φ b₂ → b₁ = b₂ := by
    intro b₁ b₂ h
    have hvalE : ∀ (bb : (a.reDim r' hr').Bond) (E₁ E₂ : a.G.edgeSet), E₁ = E₂ →
        ((bb E₁ : ℕ) = (bb E₂ : ℕ)) := fun bb E₁ E₂ hh => by cases hh; rfl
    funext E
    have h1 := congrFun (congrFun h (vE E)) (toReDimInc (eE E))
    have hEE : (⟨(eE E).1, (eE E).2.1⟩ : a.G.edgeSet) = E := Subtype.ext (hEe E)
    apply Fin.ext
    rw [hvalE b₁ E ⟨(eE E).1, (eE E).2.1⟩ hEE.symm,
      hvalE b₂ E ⟨(eE E).1, (eE E).2.1⟩ hEE.symm]
    exact congrArg Fin.val h1
  -- slot families matched across every edge are restrictions of a global assignment
  have hmem : ∀ c : (v : a.V) → (a.reDim r' hr').BondIdx v,
      (∀ (p q : a.V) (hpq : a.G.Adj p q),
        c p (toReDimInc (adjIncLeft hpq)) = c q (toReDimInc (adjIncRight hpq))) →
      c ∈ Finset.image Φ Finset.univ := by
    intro c hm
    have hvc : ∀ (v : a.V) (e₁ e₂ : a.Inc v), e₁ = e₂ →
        ((c v (toReDimInc e₁) : ℕ) = (c v (toReDimInc e₂) : ℕ)) :=
      fun v e₁ e₂ hh => by cases hh; rfl
    -- every incidence is a left cut incidence for the adjacency to its other endpoint
    have hcan : ∀ (v : a.V) (e : a.Inc v), ∃ (o : a.V) (ho : a.G.Adj v o),
        e = adjIncLeft ho := by
      intro v e
      have hmem' : s(v, Sym2.Mem.other' e.2.2) ∈ a.G.edgeSet := by
        rw [Sym2.other_spec' e.2.2]
        exact e.2.1
      rw [SimpleGraph.mem_edgeSet] at hmem'
      exact ⟨Sym2.Mem.other' e.2.2, hmem', (Subtype.ext (Sym2.other_spec' e.2.2)).symm⟩
    -- matching extends to any two incidences of a common edge, at the value level
    have hval : ∀ (v : a.V) (e : a.Inc v) (w : a.V) (f : a.Inc w), e.1 = f.1 →
        ((c v (toReDimInc e) : ℕ) = (c w (toReDimInc f) : ℕ)) := by
      intro v e w f hef
      obtain ⟨o, ho, rfl⟩ := hcan v e
      obtain ⟨o', ho', rfl⟩ := hcan w f
      have hef' : s(v, o) = s(w, o') := hef
      rcases Sym2.eq_iff.mp hef' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · calc ((c v (toReDimInc (adjIncLeft ho)) : ℕ))
            = ((c o (toReDimInc (adjIncRight ho)) : ℕ)) := congrArg Fin.val (hm v o ho)
          _ = ((c o (toReDimInc (adjIncLeft ho')) : ℕ)) :=
              hvc o (adjIncRight ho) (adjIncLeft ho') (Subtype.ext Sym2.eq_swap)
    refine Finset.mem_image.mpr ⟨fun E => Fin.cast (congrArg r' (hEe E))
      (c (vE E) (toReDimInc (eE E))), Finset.mem_univ _, ?_⟩
    funext v e'
    apply Fin.ext
    exact hval (vE ⟨e'.1, e'.2.1⟩) (eE ⟨e'.1, e'.2.1⟩) v (ofReDimInc e') (hEe ⟨e'.1, e'.2.1⟩)
  calc (∑ b : a.Bond, ∏ v : a.V, mapParam ι θ' v (Bond.restrict b v) (x v))
      -- Step A: expand `mapParam`, distribute the per-node slot sums out of the product
      = ∑ b : a.Bond, ∑ c : (v : a.V) → (a.reDim r' hr').BondIdx v,
          ∏ v : a.V, ((∏ e : a.Inc v, ι ⟨e.1, e.2.1⟩ (c v (toReDimInc e)) (b ⟨e.1, e.2.1⟩))
            * θ' v (c v) (x v)) :=
        Finset.sum_congr rfl fun b _ => prod_sum_pi (fun v cv =>
          (∏ e : a.Inc v, ι ⟨e.1, e.2.1⟩ (cv (toReDimInc e)) (b ⟨e.1, e.2.1⟩))
            * θ' v cv (x v))
      -- Step B: swap the sums and pull the `θ'` part out of the bond sum
    _ = ∑ c : (v : a.V) → (a.reDim r' hr').BondIdx v,
          (∏ v : a.V, θ' v (c v) (x v))
            * ∑ b : a.Bond, ∏ v : a.V, ∏ e : a.Inc v,
                ι ⟨e.1, e.2.1⟩ (c v (toReDimInc e)) (b ⟨e.1, e.2.1⟩) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
      -- Step C: regroup the `ι` factors along edges and Fubini the bond sum edgewise
    _ = ∑ c : (v : a.V) → (a.reDim r' hr').BondIdx v,
          (∏ v : a.V, θ' v (c v) (x v))
            * ∏ E : a.G.edgeSet, ∑ k : Fin (a.r E.1),
                ∏ v ∈ Finset.univ.filter (fun v => v ∈ E.1),
                  (if hv : v ∈ E.1 then ι E (c v ⟨E.1, E.2, hv⟩) k else 1) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        congr 1
        calc (∑ b : a.Bond, ∏ v : a.V, ∏ e : a.Inc v,
              ι ⟨e.1, e.2.1⟩ (c v (toReDimInc e)) (b ⟨e.1, e.2.1⟩))
            = ∑ b : a.Bond, ∏ E : a.G.edgeSet,
                ∏ v ∈ Finset.univ.filter (fun v => v ∈ E.1),
                  (if hv : v ∈ E.1 then ι E (c v ⟨E.1, E.2, hv⟩) (b E) else 1) := by
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [← a.prod_inc_eq_prod_edge (fun E v =>
                if hv : v ∈ E.1 then ι E (c v ⟨E.1, E.2, hv⟩) (b E) else 1)]
              refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun e _ => ?_
              symm
              exact dif_pos e.2.2
          _ = ∏ E : a.G.edgeSet, ∑ k : Fin (a.r E.1),
                ∏ v ∈ Finset.univ.filter (fun v => v ∈ E.1),
                  (if hv : v ∈ E.1 then ι E (c v ⟨E.1, E.2, hv⟩) k else 1) :=
              sum_bond_prod_edge' (fun E k =>
                ∏ v ∈ Finset.univ.filter (fun v => v ∈ E.1),
                  (if hv : v ∈ E.1 then ι E (c v ⟨E.1, E.2, hv⟩) k else 1))
      -- Step D: per-edge diagonal collapse — off-diagonal families die, restrictions give 1
    _ = ∑ c : (v : a.V) → (a.reDim r' hr').BondIdx v,
          (if c ∈ Finset.image Φ Finset.univ then ∏ v : a.V, θ' v (c v) (x v) else 0) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases hc : c ∈ Finset.image Φ Finset.univ
        · rw [if_pos hc]
          obtain ⟨b', -, rfl⟩ := Finset.mem_image.mp hc
          have h1 : (∏ E : a.G.edgeSet, ∑ k : Fin (a.r E.1),
              ∏ v ∈ Finset.univ.filter (fun v => v ∈ E.1),
                (if hv : v ∈ E.1 then ι E (Φ b' v ⟨E.1, E.2, hv⟩) k else 1)) = 1 :=
            Finset.prod_eq_one fun E _ => sum_dite_restrict_eq_one ι hortho b' E.1 E.2
          rw [h1, mul_one]
        · rw [if_neg hc]
          have hnm : ¬ ∀ (p q : a.V) (hpq : a.G.Adj p q),
              c p (toReDimInc (adjIncLeft hpq)) = c q (toReDimInc (adjIncRight hpq)) :=
            fun hm => hc (hmem c hm)
          simp only [not_forall] at hnm
          obtain ⟨p, q, hpq, hne⟩ := hnm
          have hE0 : s(p, q) ∈ a.G.edgeSet := by
            rw [SimpleGraph.mem_edgeSet]
            exact hpq
          refine mul_eq_zero_of_right _ ?_
          refine Finset.prod_eq_zero
            (Finset.mem_univ (⟨s(p, q), hE0⟩ : a.G.edgeSet)) ?_
          exact (sum_prod_pair_ite hpq.ne (ι ⟨s(p, q), hE0⟩) (hortho ⟨s(p, q), hE0⟩)
            (fun v hv => c v ⟨s(p, q), hE0, hv⟩)).trans (if_neg hne)
      -- collapse the indicator sum to a sum over re-dimensioned bond assignments
    _ = ∑ b' : (a.reDim r' hr').Bond, ∏ v : a.V, θ' v (Bond.restrict b' v) (x v) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter,
          Finset.sum_image (fun b₁ _ b₂ _ h => hΦinj b₁ b₂ h)]

/-- **Isometry collapse for one node**: pushing a coefficient family `g` through per-mode
matrices with orthonormal rows preserves the sum of squares. Stated over plain pi types so it
can be applied to the (definitionally equal) `BondIdx` types of `a` and `a.reDim r' hr'`. -/
private theorem sum_sq_isometry {I : Type*} [Fintype I] [DecidableEq I]
    (R R' : I → ℕ) (A : (i : I) → Matrix (Fin (R' i)) (Fin (R i)) ℝ)
    (horth : ∀ i, A i * (A i)ᵀ = 1) (g : ((i : I) → Fin (R' i)) → ℝ) :
    (∑ bi : (i : I) → Fin (R i),
        (∑ c : (i : I) → Fin (R' i), (∏ i, A i (c i) (bi i)) * g c) ^ 2)
      = ∑ c : (i : I) → Fin (R' i), (g c) ^ 2 := by
  classical
  have hfub : ∀ (f : (i : I) → Fin (R i) → ℝ),
      (∑ bi : (i : I) → Fin (R i), ∏ i, f i (bi i)) = ∏ i, ∑ k, f i k := by
    intro f
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  calc (∑ bi : (i : I) → Fin (R i),
        (∑ c : (i : I) → Fin (R' i), (∏ i, A i (c i) (bi i)) * g c) ^ 2)
      = ∑ bi : (i : I) → Fin (R i), ∑ c : (i : I) → Fin (R' i), ∑ c' : (i : I) → Fin (R' i),
          ((∏ i, A i (c i) (bi i)) * g c) * ((∏ i, A i (c' i) (bi i)) * g c') := by
        refine Finset.sum_congr rfl fun bi _ => ?_
        rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ c : (i : I) → Fin (R' i), ∑ c' : (i : I) → Fin (R' i),
          (g c * g c') * ∑ bi : (i : I) → Fin (R i),
            ∏ i, (A i (c i) (bi i) * A i (c' i) (bi i)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun bi _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
    _ = ∑ c : (i : I) → Fin (R' i), ∑ c' : (i : I) → Fin (R' i),
          (g c * g c') * (if c = c' then 1 else 0) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
        congr 1
        rw [hfub (fun i k => A i (c i) k * A i (c' i) k)]
        calc (∏ i, ∑ k, A i (c i) k * A i (c' i) k)
            = ∏ i, (if c i = c' i then (1 : ℝ) else 0) := by
              refine Finset.prod_congr rfl fun i _ => ?_
              have h1 : (∑ k, A i (c i) k * A i (c' i) k)
                  = (A i * (A i)ᵀ) (c i) (c' i) := by
                rw [Matrix.mul_apply]
                exact Finset.sum_congr rfl fun k _ => by rw [Matrix.transpose_apply]
              rw [h1, horth i, Matrix.one_apply]
          _ = if c = c' then 1 else 0 := by
              by_cases hcc : c = c'
              · subst hcc
                simp
              · rw [if_neg hcc]
                obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hcc
                exact Finset.prod_eq_zero (Finset.mem_univ i₀) (if_neg hi₀)
    _ = ∑ c : (i : I) → Fin (R' i), (g c) ^ 2 := by
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [pow_two]

/-- The embedding preserves the squared parameter norm when every `ι_E` has orthonormal rows. -/
theorem paramNormSq_mapParam (ι : (E : a.G.edgeSet) → Matrix (Fin (r' E.1)) (Fin (a.r E.1)) ℝ)
    (hortho : ∀ E, ι E * (ι E)ᵀ = 1) (θ' : (a.reDim r' hr').Param) :
    a.paramNormSq (mapParam ι θ') = (a.reDim r' hr').paramNormSq θ' := by
  classical
  show (∑ v : a.V, ∑ bi : a.BondIdx v, ∑ xv : Fin (a.n v), (mapParam ι θ' v bi xv) ^ 2)
    = ∑ v : a.V, ∑ bi' : (a.reDim r' hr').BondIdx v, ∑ xv : Fin (a.n v), (θ' v bi' xv) ^ 2
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.sum_comm]
  rw [show (∑ bi' : (a.reDim r' hr').BondIdx v, ∑ xv : Fin (a.n v), (θ' v bi' xv) ^ 2)
      = ∑ xv : Fin (a.n v), ∑ bi' : (a.reDim r' hr').BondIdx v, (θ' v bi' xv) ^ 2
    from Finset.sum_comm]
  refine Finset.sum_congr rfl (fun xv _ => ?_)
  exact sum_sq_isometry (fun e : a.Inc v => a.r e.1) (fun e => r' e.1)
    (fun e => ι ⟨e.1, e.2.1⟩) (fun e => hortho ⟨e.1, e.2.1⟩) (fun c => θ' v c xv)

/-- The edge matricization of a **target** does not see the bond dimensions. -/
theorem matricizeOf_reDim {u w : a.V} (h : a.G.Adj u w) (T : a.Ext → ℝ) :
    (a.reDim r' hr').matricizeOf h T = a.matricizeOf h T := rfl

/-- If the reduced bond dimensions still dominate the
target's matricization ranks, the target is realizable at the reduced dimensions. -/
theorem realizable_reDim {Tstar : a.Ext → ℝ}
    (hs : ∀ (u w : a.V) (h : a.G.Adj u w), (a.matricizeOf h Tstar).rank ≤ r' s(u, w)) :
    (a.reDim r' hr').Realizable Tstar := by
  rw [(a.reDim r' hr').realizable_iff_rank_le]
  intro u w h
  exact hs u w h

/-- **Orthonormal-row matrix with prescribed kernel room** (the compression subspace choice,
form): if `D` has dimension at least `r − s` (and `s ≤ r`), there is an `s × r` matrix with
orthonormal rows whose kernel lies inside `D`. -/
theorem exists_orthonormal_rows_ker_le {r s : ℕ} (hs : s ≤ r)
    (D : Submodule ℝ (Fin r → ℝ)) (hdim : r ≤ s + Module.finrank ℝ D) :
    ∃ ι : Matrix (Fin s) (Fin r) ℝ, ι * ιᵀ = 1 ∧
      LinearMap.ker ι.mulVecLin ≤ D := by
  classical
  have hrs : r - s ≤ Module.finrank ℝ D := by omega
  -- the first `r - s` basis vectors of `D`, viewed in `ℝ^r`
  set b : Module.Basis (Fin (Module.finrank ℝ D)) ℝ D := Module.finBasis ℝ D with hb
  set w : Fin (r - s) → (Fin r → ℝ) := fun i => (b (Fin.castLE hrs i) : Fin r → ℝ) with hw
  have hw_mem : ∀ i, w i ∈ D := fun i => (b (Fin.castLE hrs i)).2
  have hw_li : LinearIndependent ℝ w :=
    (b.linearIndependent.map' D.subtype D.ker_subtype).comp
      (Fin.castLE hrs) (Fin.castLE_injective hrs)
  set B : Matrix (Fin r) (Fin (r - s)) ℝ := Matrix.of (fun i j => w j i) with hB
  have hBcol : B.col = w := rfl
  have hrankB : B.rank = r - s := by
    rw [Matrix.rank_eq_finrank_span_cols, hBcol, finrank_span_eq_card hw_li,
      Fintype.card_fin]
  have hrangeB : LinearMap.range B.mulVecLin ≤ D := by
    rw [Matrix.range_mulVecLin, hBcol]
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hw_mem)
  -- the kernel of `Bᵀ` has dimension `s`
  have hkerBT : Module.finrank ℝ (LinearMap.ker (Bᵀ).mulVecLin) = s := by
    have h1 := rank_add_finrank_ker Bᵀ
    rw [Matrix.rank_transpose, hrankB, Fintype.card_fin] at h1
    omega
  set cb : Module.Basis (Fin s) ℝ (LinearMap.ker (Bᵀ).mulVecLin) :=
    (Module.finBasis ℝ (LinearMap.ker (Bᵀ).mulVecLin)).reindex (finCongr hkerBT) with hcb
  set C : Matrix (Fin r) (Fin s) ℝ := Matrix.of (fun i l => (cb l : Fin r → ℝ) i) with hC
  have hCcol : C.col = fun l => (cb l : Fin r → ℝ) := rfl
  have hC_li : LinearIndependent ℝ (fun l => (cb l : Fin r → ℝ)) :=
    cb.linearIndependent.map' (LinearMap.ker (Bᵀ).mulVecLin).subtype
      (LinearMap.ker (Bᵀ).mulVecLin).ker_subtype
  have hrankC : C.rank = s := by
    rw [Matrix.rank_eq_finrank_span_cols, hCcol, finrank_span_eq_card hC_li,
      Fintype.card_fin]
  obtain ⟨M, -, hMorth⟩ := exists_orthonormalize C hrankC
  refine ⟨(C * M)ᵀ, ?_, ?_⟩
  · rw [Matrix.transpose_transpose]
    exact hMorth
  · -- `Cᵀ B = 0`: the columns of `C` lie in `ker Bᵀ`
    have hCB : Cᵀ * B = 0 := by
      ext l j
      have hmem := (cb l).2
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hmem
      have h0 := congrFun hmem j
      rw [Pi.zero_apply] at h0
      rw [Matrix.mul_apply, Matrix.zero_apply]
      calc (∑ i, Cᵀ l i * B i j)
          = ∑ i, Bᵀ j i * (cb l : Fin r → ℝ) i :=
            Finset.sum_congr rfl fun i _ => by
              rw [Matrix.transpose_apply, Matrix.transpose_apply]
              exact mul_comm _ _
        _ = (Bᵀ *ᵥ (cb l : Fin r → ℝ)) j := rfl
        _ = 0 := h0
    have hiB : (C * M)ᵀ * B = 0 := by
      rw [Matrix.transpose_mul, Matrix.mul_assoc, hCB, Matrix.mul_zero]
    -- `range B ≤ ker ι`
    have hle : LinearMap.range B.mulVecLin ≤ LinearMap.ker ((C * M)ᵀ).mulVecLin := by
      rintro x ⟨z, rfl⟩
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
        Matrix.mulVec_mulVec, hiB, Matrix.zero_mulVec]
    -- dimension count: `ker ι` and `range B` both have dimension `r - s`
    have hrankI : ((C * M)ᵀ).rank = s := by
      have h1 : (((C * M)ᵀ) * ((C * M)ᵀ)ᵀ).rank ≤ ((C * M)ᵀ).rank :=
        Matrix.rank_mul_le_left _ _
      rw [Matrix.transpose_transpose, hMorth, Matrix.rank_one, Fintype.card_fin] at h1
      have h2 : ((C * M)ᵀ).rank ≤ s := by
        have h3 := Matrix.rank_le_card_height ((C * M)ᵀ)
        rwa [Fintype.card_fin] at h3
      omega
    have hkerI : Module.finrank ℝ (LinearMap.ker ((C * M)ᵀ).mulVecLin) = r - s := by
      have h1 := rank_add_finrank_ker ((C * M)ᵀ)
      rw [hrankI, Fintype.card_fin] at h1
      omega
    have hrangeBfin : Module.finrank ℝ (LinearMap.range B.mulVecLin) = r - s := hrankB
    have heq : LinearMap.range B.mulVecLin = LinearMap.ker ((C * M)ᵀ).mulVecLin :=
      Submodule.eq_of_le_of_finrank_le hle (by rw [hkerI, hrangeBfin])
    rw [← heq]
    exact hrangeB

end Arch

end TTN
