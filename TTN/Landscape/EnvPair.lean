import TTN.Landscape.CoreDescent

/-!
# The environment pairing for a deficient component

For the component `(S, K)` with
unit dormant directions `η`, the **indicator** choice of the free tensors `G_v` makes the
leading descent term `T_N := represented (S.piecewise (corePerturb K η G) θ)` evaluate to a
point evaluation of the **joint environment**: all far-interior bonds stay contracted
against the unperturbed far tensors, boundary bonds are pinned to `β`, core externals are
pinned to `ξ`, and the `K`-bond sums collapse by `⟨η_E, η_E⟩ = 1`.

* `EdgeInside` / `EdgeTouches` — edge trichotomy relative to `S` (`K` = inside edges).
* `BdryBond` / `FarBond` / `SExtC` / `FarExtC` — flat coordinate types that avoid replacing
  the architecture.
* `envFactor` — the joint far contraction `E(x_far, β)`.
* `Gind` — the indicator free tensors at `(ξ, β)` (admissible: vanish off `S`, ignore
  `K`-slots).
* `represented_piecewise_Gind` — **the key evaluation**
  `T_N[G_ind](x) = ind(x|_S = ξ) · E(x|_far, β)`.
* `pair_residual_Gind` — the pairing `⟨R, T_N[G_ind]⟩` is the compressed residual
  `R̂(ξ, β) := ∑_{x_far} R(ξ ⊕ x_far) · E(x_far, β)`.
-/

open scoped Matrix

namespace TTN

namespace Arch

variable {a : Arch}

/-- The edge `E` lies inside the vertex set `S` (both endpoints in `S`). -/
def EdgeInside (S : Finset a.V) (E : a.G.edgeSet) : Prop :=
  ∀ v : a.V, v ∈ E.1 → v ∈ S

/-- The edge `E` touches the vertex set `S` (some endpoint in `S`). -/
def EdgeTouches (S : Finset a.V) (E : a.G.edgeSet) : Prop :=
  ∃ v : a.V, v ∈ E.1 ∧ v ∈ S

/-- Bond coordinates on the boundary edges of `S`. -/
def BdryBond (S : Finset a.V) : Type :=
  (f : {E : a.G.edgeSet // a.EdgeTouches S E ∧ ¬ a.EdgeInside S E}) → Fin (a.r f.1.1)

/-- Bond coordinates on the far edges (not touching `S`). -/
def FarBond (S : Finset a.V) : Type :=
  (f : {E : a.G.edgeSet // ¬ a.EdgeTouches S E}) → Fin (a.r f.1.1)

/-- External coordinates on the `S`-nodes. -/
def SExtC (S : Finset a.V) : Type := (v : {x : a.V // x ∈ S}) → Fin (a.n v.1)

/-- External coordinates on the far nodes. -/
def FarExtC (S : Finset a.V) : Type := (v : {x : a.V // x ∉ S}) → Fin (a.n v.1)

noncomputable instance (S : Finset a.V) : Fintype (a.BdryBond S) := by
  unfold BdryBond
  classical
  infer_instance

noncomputable instance (S : Finset a.V) : Fintype (a.FarBond S) := by
  unfold FarBond
  classical
  infer_instance

instance (S : Finset a.V) : Fintype (a.SExtC S) := by
  unfold SExtC
  infer_instance

instance (S : Finset a.V) : Fintype (a.FarExtC S) := by
  unfold FarExtC
  infer_instance

open Classical in
/-- **The joint environment**: the contraction of all far node tensors, with far-interior
bonds summed, boundary bonds pinned to `β`, and far externals pinned to `x_f`. (A far node
has no `K`-incidence, so its slots split into boundary and far.) -/
noncomputable def envFactor (θ : a.Param) (S : Finset a.V) (β : a.BdryBond S)
    (xf : a.FarExtC S) : ℝ :=
  ∑ bF : a.FarBond S, ∏ y : {y : a.V // y ∉ S},
    θ y.1 (fun e => if h : a.EdgeTouches S ⟨e.1, e.2.1⟩
        then β ⟨⟨e.1, e.2.1⟩, h, fun hins => y.2 (hins y.1 e.2.2)⟩
        else bF ⟨⟨e.1, e.2.1⟩, h⟩) (xf y)

open Classical in
/-- **The indicator free tensors** at `(ξ, β)`: on `S`-nodes, the non-`K` bond slots carry
indicators pinning them to `β` and the external mode an indicator pinning it to `ξ`; zero
off `S`. -/
noncomputable def Gind (S : Finset a.V) (ξ : a.SExtC S) (β : a.BdryBond S)
    (v : a.V) : a.NodeTensor v :=
  if hv : v ∈ S then
    fun bi xv =>
      (∏ e : {e : a.Inc v // ¬ a.EdgeInside S ⟨e.1, e.2.1⟩},
        if bi e.1 = β ⟨⟨e.1.1, e.1.2.1⟩, ⟨v, e.1.2.2, hv⟩, e.2⟩ then (1 : ℝ) else 0)
      * (if xv = ξ ⟨v, hv⟩ then (1 : ℝ) else 0)
  else fun _ _ => 0

/-- An edge inside `S` touches `S` (edges are nonempty). -/
theorem EdgeInside.touches {S : Finset a.V} {E : a.G.edgeSet}
    (hE : a.EdgeInside S E) : a.EdgeTouches S E := by
  obtain ⟨E, hE'⟩ := E
  induction E using Sym2.ind with
  | _ p q => exact ⟨p, Sym2.mem_mk_left p q, hE p (Sym2.mem_mk_left p q)⟩

/-- Bond coordinates on the inside edges (`= K`). -/
def KBond (S : Finset a.V) : Type :=
  (f : {E : a.G.edgeSet // a.EdgeInside S E}) → Fin (a.r f.1.1)

noncomputable instance (S : Finset a.V) : Fintype (a.KBond S) := by
  unfold KBond
  classical
  infer_instance

open Classical in
/-- Split a global bond assignment into inside / boundary / far coordinates. -/
noncomputable def bondSplit (S : Finset a.V) :
    a.Bond ≃ a.KBond S × a.BdryBond S × a.FarBond S where
  toFun b := (fun f => b f.1, fun f => b f.1, fun f => b f.1)
  invFun p := fun E =>
    if h1 : a.EdgeInside S E then p.1 ⟨E, h1⟩
    else if h2 : a.EdgeTouches S E then p.2.1 ⟨E, h2, h1⟩
    else p.2.2 ⟨E, h2⟩
  left_inv b := by
    funext E
    by_cases h1 : a.EdgeInside S E
    · simp only [dif_pos h1]
    · by_cases h2 : a.EdgeTouches S E
      · simp only [dif_neg h1, dif_pos h2]
      · simp only [dif_neg h1, dif_neg h2]
  right_inv p := by
    obtain ⟨bK, bB, bF⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨funext fun f => ?_, funext fun f => ?_, funext fun f => ?_⟩
    · exact dif_pos f.2
    · rw [dif_neg f.2.2, dif_pos f.2.1]
    · rw [dif_neg (fun hi => f.2 hi.touches), dif_neg f.2]

open Classical in
/-- Value of the reconstructed bond at an edge, by its class. -/
theorem bondSplit_symm_apply (S : Finset a.V) (bK : a.KBond S) (bB : a.BdryBond S)
    (bF : a.FarBond S) (E : a.G.edgeSet) :
    (a.bondSplit S).symm (bK, bB, bF) E
      = if h1 : a.EdgeInside S E then bK ⟨E, h1⟩
        else if h2 : a.EdgeTouches S E then bB ⟨E, h2, h1⟩ else bF ⟨E, h2⟩ := rfl

/-- The indicator tensors vanish off `S`. -/
theorem Gind_apply_of_notMem (S : Finset a.V) (ξ : a.SExtC S) (β : a.BdryBond S)
    {v : a.V} (hv : v ∉ S) (bi : a.BondIdx v) (xv : Fin (a.n v)) :
    a.Gind S ξ β v bi xv = 0 := by
  simp only [Gind, dif_neg hv]

/-- The indicator tensors ignore the `K`-slots (`K` inside `S`). -/
theorem Gind_update_of_edgeInside (S : Finset a.V) (ξ : a.SExtC S) (β : a.BdryBond S)
    {v : a.V} (e : a.Inc v) (hin : a.EdgeInside S ⟨e.1, e.2.1⟩)
    (bi : a.BondIdx v) (k : Fin (a.r e.1)) (xv : Fin (a.n v)) :
    a.Gind S ξ β v (Function.update bi e k) xv = a.Gind S ξ β v bi xv := by
  by_cases hv : v ∈ S
  · simp only [Gind, dif_pos hv]
    congr 1
    refine Finset.prod_congr rfl (fun e' _ => ?_)
    have hne : e'.1 ≠ e := by
      intro hc
      refine e'.2 ?_
      have h' : (⟨(e'.1).1, (e'.1).2.1⟩ : a.G.edgeSet) = ⟨e.1, e.2.1⟩ :=
        congrArg (fun z : a.Inc v => (⟨z.1, z.2.1⟩ : a.G.edgeSet)) hc
      rw [h']; exact hin
    rw [Function.update_of_ne hne]
  · simp only [Gind, dif_neg hv]

open Classical in
/-- Value of the indicator tensor at an `S`-node. -/
theorem Gind_apply_of_mem (S : Finset a.V) (ξ : a.SExtC S) (β : a.BdryBond S)
    {v : a.V} (hv : v ∈ S) (bi : a.BondIdx v) (xv : Fin (a.n v)) :
    a.Gind S ξ β v bi xv
      = (∏ e : {e : a.Inc v // ¬ a.EdgeInside S ⟨e.1, e.2.1⟩},
          if bi e.1 = β ⟨⟨e.1.1, e.1.2.1⟩, ⟨v, e.1.2.2, hv⟩, e.2⟩ then (1 : ℝ) else 0)
        * (if xv = ξ ⟨v, hv⟩ then (1 : ℝ) else 0) := by
  simp only [Gind, dif_pos hv]

/-- Split a vertex product into its `S` and non-`S` parts. -/
theorem prod_split_S (S : Finset a.V) (F : a.V → ℝ) :
    (∏ v : a.V, F v)
      = (∏ v : {v : a.V // v ∈ S}, F v.1) * (∏ v : {v : a.V // v ∉ S}, F v.1) := by
  classical
  rw [Finset.prod_coe_sort S F, ← Finset.prod_subtype Sᶜ (fun x => Finset.mem_compl) F]
  exact (Finset.prod_mul_prod_compl S F).symm

/-- Fubini for a Pi-indexed sum of products (generic form of `sum_bond_prod_edge`). -/
theorem sum_pi_prod {I : Type*} [Fintype I] [DecidableEq I]
    (R : I → ℕ) (f : (i : I) → Fin (R i) → ℝ) :
    (∑ b : (i : I) → Fin (R i), ∏ i, f i (b i)) = ∏ i, ∑ k, f i k := by
  classical
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

open Classical in
/-- The inside-edge (`K`) contribution at the `S`-nodes regroups into per-edge squares. -/
theorem prod_S_Kfactor (S : Finset a.V) (K : Finset a.G.edgeSet)
    (η : (E : a.G.edgeSet) → Fin (a.r E.1) → ℝ)
    (hKiff : ∀ E : a.G.edgeSet, E ∈ K ↔ a.EdgeInside S E)
    (bK : a.KBond S) (bB : a.BdryBond S) (bF : a.FarBond S) :
    (∏ v : {v : a.V // v ∈ S},
       ∏ e ∈ Finset.univ.filter (fun e : a.Inc v.1 => (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ K),
         η ⟨e.1, e.2.1⟩ (Bond.restrict ((a.bondSplit S).symm (bK, bB, bF)) v.1 e))
     = ∏ f : {E : a.G.edgeSet // a.EdgeInside S E}, (η f.1 (bK f)) ^ 2 := by
  classical
  set g : a.G.edgeSet → ℝ :=
    fun E => if h : a.EdgeInside S E then η E (bK ⟨E, h⟩) else 1 with hg
  have hnode : (∏ v : {v : a.V // v ∈ S},
       ∏ e ∈ Finset.univ.filter (fun e : a.Inc v.1 => (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ K),
         η ⟨e.1, e.2.1⟩ (Bond.restrict ((a.bondSplit S).symm (bK, bB, bF)) v.1 e))
      = ∏ v : {v : a.V // v ∈ S}, ∏ e : a.Inc v.1, g ⟨e.1, e.2.1⟩ := by
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    by_cases hins : a.EdgeInside S ⟨e.1, e.2.1⟩
    · rw [if_pos ((hKiff _).mpr hins)]
      simp only [hg]
      rw [dif_pos hins]
      congr 1
      show (a.bondSplit S).symm (bK, bB, bF) ⟨e.1, e.2.1⟩ = bK ⟨⟨e.1, e.2.1⟩, hins⟩
      rw [a.bondSplit_symm_apply, dif_pos hins]
    · rw [if_neg (fun hk => hins ((hKiff _).mp hk))]
      simp only [hg]
      rw [dif_neg hins]
  rw [hnode]
  have hallV : (∏ v : {v : a.V // v ∈ S}, ∏ e : a.Inc v.1, g ⟨e.1, e.2.1⟩)
      = ∏ v : a.V, ∏ e : a.Inc v, g ⟨e.1, e.2.1⟩ := by
    rw [prod_split_S S (fun v => ∏ e : a.Inc v, g ⟨e.1, e.2.1⟩)]
    have hone : (∏ v : {v : a.V // v ∉ S}, ∏ e : a.Inc v.1, g ⟨e.1, e.2.1⟩) = 1 := by
      refine Finset.prod_eq_one (fun v _ => Finset.prod_eq_one (fun e _ => ?_))
      simp only [hg]
      exact dif_neg (fun hins => v.2 (hins v.1 e.2.2))
    rw [hone, mul_one]
  rw [hallV, a.prod_inc_eq_prod_edge_sq g,
    ← Fintype.prod_subtype_mul_prod_subtype (fun E : a.G.edgeSet => a.EdgeInside S E)
      (fun E => (g E) ^ 2)]
  have hone2 : (∏ E : {E : a.G.edgeSet // ¬ a.EdgeInside S E}, (g E.1) ^ 2) = 1 := by
    refine Finset.prod_eq_one (fun E _ => ?_)
    simp only [hg]
    rw [dif_neg E.2, one_pow]
  rw [hone2, mul_one]
  refine Finset.prod_congr rfl (fun f _ => ?_)
  simp only [hg]
  rw [dif_pos f.2]

open Classical in
/-- The inside-edge bond sum collapses to `1` by unit dormancy. -/
theorem sum_KBond_sq_eq_one (S : Finset a.V) (K : Finset a.G.edgeSet)
    (η : (E : a.G.edgeSet) → Fin (a.r E.1) → ℝ)
    (hKiff : ∀ E : a.G.edgeSet, E ∈ K ↔ a.EdgeInside S E)
    (hunit : ∀ E ∈ K, η E ⬝ᵥ η E = 1) :
    (∑ bK : a.KBond S, ∏ f : {E : a.G.edgeSet // a.EdgeInside S E}, (η f.1 (bK f)) ^ 2) = 1 := by
  classical
  refine Eq.trans (sum_pi_prod (fun f : {E : a.G.edgeSet // a.EdgeInside S E} => a.r f.1.1)
    (fun f k => (η f.1 k) ^ 2)) ?_
  refine Finset.prod_eq_one (fun f _ => ?_)
  have hdot : (∑ k, (η f.1 k) ^ 2) = η f.1 ⬝ᵥ η f.1 := by
    simp only [dotProduct, pow_two]
  rw [hdot]
  exact hunit f.1 ((hKiff f.1).mpr f.2)

open Classical in
/-- The boundary-edge indicator product at the `S`-nodes collapses to `bB = β`. -/
theorem prod_S_Bfactor (S : Finset a.V) (bB β : a.BdryBond S) :
    (∏ v : {v : a.V // v ∈ S},
       ∏ e : {e : a.Inc v.1 // ¬ a.EdgeInside S ⟨e.1, e.2.1⟩},
         if bB ⟨⟨e.1.1, e.1.2.1⟩, ⟨v.1, e.1.2.2, v.2⟩, e.2⟩
             = β ⟨⟨e.1.1, e.1.2.1⟩, ⟨v.1, e.1.2.2, v.2⟩, e.2⟩ then (1 : ℝ) else 0)
     = if bB = β then (1 : ℝ) else 0 := by
  classical
  by_cases hbb : bB = β
  · subst hbb
    rw [if_pos rfl]
    exact Finset.prod_eq_one (fun v _ => Finset.prod_eq_one (fun e _ => if_pos rfl))
  · rw [if_neg hbb]
    obtain ⟨f, hf⟩ := Function.ne_iff.mp hbb
    obtain ⟨w, hw1, hw2⟩ := f.2.1
    refine Finset.prod_eq_zero (Finset.mem_univ (⟨w, hw2⟩ : {v : a.V // v ∈ S})) ?_
    refine Finset.prod_eq_zero (i := ⟨⟨f.1.1, f.1.2, hw1⟩, f.2.2⟩) (Finset.mem_univ _) ?_
    exact if_neg hf

open Classical in
/-- A `0/1`-indicator sum pins the summand to `b = b0`. -/
theorem sum_ite_pin {B : Type*} [Fintype B] (b0 : B) (Q : B → ℝ) :
    (∑ b, (if b = b0 then (1 : ℝ) else 0) * Q b) = Q b0 := by
  classical
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ b0 Q, if_pos (Finset.mem_univ b0)]

set_option maxHeartbeats 400000 in
-- The indicator expansion needs more than the default elaboration budget.
/-- **The key evaluation (indicator choice)**: with unit dormant `η` on the inside edges
`K` (and `K` = exactly the inside edges), the leading descent term at the indicator tensors
is the pinned joint environment. -/
theorem represented_piecewise_Gind (θ : a.Param) (S : Finset a.V)
    (K : Finset a.G.edgeSet) (η : (E : a.G.edgeSet) → Fin (a.r E.1) → ℝ)
    (hKiff : ∀ E : a.G.edgeSet, E ∈ K ↔ a.EdgeInside S E)
    (hunit : ∀ E ∈ K, η E ⬝ᵥ η E = 1)
    (ξ : a.SExtC S) (β : a.BdryBond S) (x : a.Ext) :
    a.represented (S.piecewise (a.corePerturb K η (a.Gind S ξ β)) θ) x
      = (∏ v : {v : a.V // v ∈ S}, if x v.1 = ξ v then (1 : ℝ) else 0)
        * a.envFactor θ S β (fun y : {y : a.V // y ∉ S} => x y.1) := by
  classical
  show (∑ b : a.Bond, ∏ v : a.V,
      (S.piecewise (a.corePerturb K η (a.Gind S ξ β)) θ) v (Bond.restrict b v) (x v))
    = (∏ v : {v : a.V // v ∈ S}, if x v.1 = ξ v then (1 : ℝ) else 0)
      * a.envFactor θ S β (fun y : {y : a.V // y ∉ S} => x y.1)
  set ψ : a.Param := S.piecewise (a.corePerturb K η (a.Gind S ξ β)) θ with hψ
  set EP : ℝ := ∏ v : {v : a.V // v ∈ S}, if x v.1 = ξ v then (1 : ℝ) else 0 with hEP
  -- value of `ψ` at an `S`-node, factored into K / boundary / external parts
  have hSval : ∀ (bK : a.KBond S) (bB : a.BdryBond S) (bF : a.FarBond S)
      (v : {v : a.V // v ∈ S}),
      ψ v.1 (Bond.restrict ((a.bondSplit S).symm (bK, bB, bF)) v.1) (x v.1)
      = (∏ e ∈ Finset.univ.filter (fun e : a.Inc v.1 => (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ K),
           η ⟨e.1, e.2.1⟩ (Bond.restrict ((a.bondSplit S).symm (bK, bB, bF)) v.1 e))
        * ((∏ e : {e : a.Inc v.1 // ¬ a.EdgeInside S ⟨e.1, e.2.1⟩},
             if bB ⟨⟨e.1.1, e.1.2.1⟩, ⟨v.1, e.1.2.2, v.2⟩, e.2⟩
                 = β ⟨⟨e.1.1, e.1.2.1⟩, ⟨v.1, e.1.2.2, v.2⟩, e.2⟩ then (1 : ℝ) else 0)
           * (if x v.1 = ξ v then (1 : ℝ) else 0)) := by
    intro bK bB bF v
    rw [hψ, Finset.piecewise_eq_of_mem _ _ _ v.2]
    show (∏ e ∈ Finset.univ.filter (fun e : a.Inc v.1 => (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ K),
           η ⟨e.1, e.2.1⟩ (Bond.restrict ((a.bondSplit S).symm (bK, bB, bF)) v.1 e))
         * a.Gind S ξ β v.1 (Bond.restrict ((a.bondSplit S).symm (bK, bB, bF)) v.1) (x v.1) = _
    rw [a.Gind_apply_of_mem S ξ β v.2]
    congr 1
    congr 1
    refine Finset.prod_congr rfl (fun e _ => ?_)
    rw [show (Bond.restrict ((a.bondSplit S).symm (bK, bB, bF)) v.1) e.1
          = bB ⟨⟨e.1.1, e.1.2.1⟩, ⟨v.1, e.1.2.2, v.2⟩, e.2⟩ from ?_]
    show (a.bondSplit S).symm (bK, bB, bF) ⟨e.1.1, e.1.2.1⟩
        = bB ⟨⟨e.1.1, e.1.2.1⟩, ⟨v.1, e.1.2.2, v.2⟩, e.2⟩
    rw [a.bondSplit_symm_apply, dif_neg e.2,
      dif_pos (show a.EdgeTouches S ⟨e.1.1, e.1.2.1⟩ from ⟨v.1, e.1.2.2, v.2⟩)]
  -- value of `ψ` at a far node = the environment summand
  have hFarpart : ∀ (bK : a.KBond S) (bB : a.BdryBond S) (bF : a.FarBond S),
      (∏ v : {v : a.V // v ∉ S},
        ψ v.1 (Bond.restrict ((a.bondSplit S).symm (bK, bB, bF)) v.1) (x v.1))
      = ∏ y : {y : a.V // y ∉ S}, θ y.1 (fun e => if h : a.EdgeTouches S ⟨e.1, e.2.1⟩
          then bB ⟨⟨e.1, e.2.1⟩, h, fun hins => y.2 (hins y.1 e.2.2)⟩
          else bF ⟨⟨e.1, e.2.1⟩, h⟩) (x y.1) := by
    intro bK bB bF
    refine Finset.prod_congr rfl (fun y _ => ?_)
    rw [hψ, Finset.piecewise_eq_of_notMem _ _ _ y.2]
    congr 1
    funext e
    show (a.bondSplit S).symm (bK, bB, bF) ⟨e.1, e.2.1⟩ = _
    rw [a.bondSplit_symm_apply, dif_neg (fun hins => y.2 (hins y.1 e.2.2))]
  -- the per-triple summand
  have hmaster : ∀ (bK : a.KBond S) (bB : a.BdryBond S) (bF : a.FarBond S),
      (∏ v : a.V, ψ v (Bond.restrict ((a.bondSplit S).symm (bK, bB, bF)) v) (x v))
      = (∏ f : {E : a.G.edgeSet // a.EdgeInside S E}, (η f.1 (bK f)) ^ 2)
        * ((if bB = β then (1 : ℝ) else 0)
          * (EP * ∏ y : {y : a.V // y ∉ S}, θ y.1 (fun e => if h : a.EdgeTouches S ⟨e.1, e.2.1⟩
              then bB ⟨⟨e.1, e.2.1⟩, h, fun hins => y.2 (hins y.1 e.2.2)⟩
              else bF ⟨⟨e.1, e.2.1⟩, h⟩) (x y.1))) := by
    intro bK bB bF
    rw [prod_split_S S (fun v => ψ v (Bond.restrict ((a.bondSplit S).symm (bK, bB, bF)) v) (x v)),
      hFarpart bK bB bF, Finset.prod_congr rfl (fun v _ => hSval bK bB bF v),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      a.prod_S_Kfactor S K η hKiff bK bB bF, a.prod_S_Bfactor S bB β, ← hEP]
    ring
  -- reindex the bond sum by the split, then reduce
  have hreindex : (∑ b : a.Bond, ∏ v, ψ v (Bond.restrict b v) (x v))
      = ∑ bK : a.KBond S, ∑ bB : a.BdryBond S, ∑ bF : a.FarBond S,
          ∏ v, ψ v (Bond.restrict ((a.bondSplit S).symm (bK, bB, bF)) v) (x v) := by
    calc (∑ b : a.Bond, ∏ v, ψ v (Bond.restrict b v) (x v))
        = ∑ p : a.KBond S × a.BdryBond S × a.FarBond S,
            ∏ v, ψ v (Bond.restrict ((a.bondSplit S).symm p) v) (x v) :=
          (Fintype.sum_equiv (a.bondSplit S).symm _ _ (fun p => rfl)).symm
      _ = ∑ bK : a.KBond S, ∑ q : a.BdryBond S × a.FarBond S,
            ∏ v, ψ v (Bond.restrict ((a.bondSplit S).symm (bK, q)) v) (x v) :=
          Fintype.sum_prod_type _
      _ = ∑ bK, ∑ bB, ∑ bF,
            ∏ v, ψ v (Bond.restrict ((a.bondSplit S).symm (bK, bB, bF)) v) (x v) :=
          Finset.sum_congr rfl (fun bK _ => Fintype.sum_prod_type _)
  rw [hreindex, Finset.sum_congr rfl (fun bK _ => Finset.sum_congr rfl (fun bB _ =>
    Finset.sum_congr rfl (fun bF _ => hmaster bK bB bF)))]
  rw [show a.envFactor θ S β (fun y : {y : a.V // y ∉ S} => x y.1)
      = ∑ bF : a.FarBond S, ∏ y : {y : a.V // y ∉ S}, θ y.1
          (fun e => if h : a.EdgeTouches S ⟨e.1, e.2.1⟩
            then β ⟨⟨e.1, e.2.1⟩, h, fun hins => y.2 (hins y.1 e.2.2)⟩
            else bF ⟨⟨e.1, e.2.1⟩, h⟩) (x y.1) from rfl]
  rw [Finset.sum_congr rfl fun bK _ => Finset.sum_congr rfl fun bB _ => by
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]]
  rw [Finset.sum_congr rfl fun bK _ => by rw [← Finset.mul_sum]]
  rw [sum_ite_pin β, ← Finset.sum_mul,
    a.sum_KBond_sq_eq_one S K η hKiff hunit, one_mul]

/-- **The pairing identity**: against the indicator tensors, the residual pairing is the
compressed residual `R̂(ξ, β)`. -/
theorem pair_residual_Gind (Tstar : a.Ext → ℝ) (θ : a.Param) (S : Finset a.V)
    (K : Finset a.G.edgeSet) (η : (E : a.G.edgeSet) → Fin (a.r E.1) → ℝ)
    (hKiff : ∀ E : a.G.edgeSet, E ∈ K ↔ a.EdgeInside S E)
    (hunit : ∀ E ∈ K, η E ⬝ᵥ η E = 1)
    (ξ : a.SExtC S) (β : a.BdryBond S) :
    (∑ x, a.residual Tstar θ x
        * a.represented (S.piecewise (a.corePerturb K η (a.Gind S ξ β)) θ) x)
      = ∑ xf : a.FarExtC S,
          a.residual Tstar θ
            ((Equiv.piEquivPiSubtypeProd (fun v : a.V => v ∈ S)
              (fun v => Fin (a.n v))).symm (ξ, xf))
            * a.envFactor θ S β xf := by
  classical
  set e := Equiv.piEquivPiSubtypeProd (fun v : a.V => v ∈ S) (fun v => Fin (a.n v)) with he
  -- reading the recombined point at `S`- and far-nodes
  have hxS : ∀ (ξ' : a.SExtC S) (xf : a.FarExtC S) (v : {v : a.V // v ∈ S}),
      (e.symm (ξ', xf)) v.1 = ξ' v := by
    intro ξ' xf v
    show (if h : v.1 ∈ S then (ξ', xf).1 ⟨v.1, h⟩ else (ξ', xf).2 ⟨v.1, h⟩) = ξ' v
    exact (dif_pos v.2).trans rfl
  have hxF : ∀ (ξ' : a.SExtC S) (xf : a.FarExtC S) (y : {y : a.V // y ∉ S}),
      (e.symm (ξ', xf)) y.1 = xf y := by
    intro ξ' xf y
    show (if h : y.1 ∈ S then (ξ', xf).1 ⟨y.1, h⟩ else (ξ', xf).2 ⟨y.1, h⟩) = xf y
    exact (dif_neg y.2).trans rfl
  have hEP : ∀ ξ' : a.SExtC S,
      (∏ v : {v : a.V // v ∈ S}, if ξ' v = ξ v then (1 : ℝ) else 0) = if ξ' = ξ then (1 : ℝ) else 0 := by
    intro ξ'
    by_cases hξ : ξ' = ξ
    · subst hξ; rw [if_pos rfl]; exact Finset.prod_eq_one (fun v _ => if_pos rfl)
    · rw [if_neg hξ]
      obtain ⟨v, hv⟩ := Function.ne_iff.mp hξ
      exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)
  -- the recombined summand, fully evaluated
  have hsummand : ∀ (ξ' : a.SExtC S) (xf : a.FarExtC S),
      a.residual Tstar θ (e.symm (ξ', xf))
        * ((∏ v : {v : a.V // v ∈ S}, if (e.symm (ξ', xf)) v.1 = ξ v then (1 : ℝ) else 0)
          * a.envFactor θ S β (fun y : {y : a.V // y ∉ S} => (e.symm (ξ', xf)) y.1))
      = (if ξ' = ξ then (1 : ℝ) else 0)
        * (a.residual Tstar θ (e.symm (ξ', xf)) * a.envFactor θ S β xf) := by
    intro ξ' xf
    rw [Finset.prod_congr rfl (fun v _ => by rw [hxS ξ' xf v]), hEP ξ',
      show (fun y : {y : a.V // y ∉ S} => (e.symm (ξ', xf)) y.1) = xf
        from funext (fun y => hxF ξ' xf y)]
    ring
  rw [Finset.sum_congr rfl fun x _ => by
    rw [a.represented_piecewise_Gind θ S K η hKiff hunit ξ β x]]
  rw [show (∑ x : a.Ext, a.residual Tstar θ x
        * ((∏ v : {v : a.V // v ∈ S}, if x v.1 = ξ v then (1 : ℝ) else 0)
          * a.envFactor θ S β (fun y : {y : a.V // y ∉ S} => x y.1)))
      = ∑ p : a.SExtC S × a.FarExtC S, a.residual Tstar θ (e.symm p)
          * ((∏ v : {v : a.V // v ∈ S}, if (e.symm p) v.1 = ξ v then (1 : ℝ) else 0)
            * a.envFactor θ S β (fun y : {y : a.V // y ∉ S} => (e.symm p) y.1))
      from (Fintype.sum_equiv e.symm _ _ (fun p => rfl)).symm]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun xf _ => ?_)
  have h0 : ∀ x ∈ (Finset.univ : Finset (a.SExtC S)), x ≠ ξ →
      a.residual Tstar θ (e.symm (x, xf))
        * ((∏ v : {v : a.V // v ∈ S}, if (e.symm (x, xf)) v.1 = ξ v then (1 : ℝ) else 0)
          * a.envFactor θ S β (fun y : {y : a.V // y ∉ S} => (e.symm (x, xf)) y.1)) = 0 := by
    intro x _ hx
    obtain ⟨v, hv⟩ := Function.ne_iff.mp hx
    have hz : (∏ v : {v : a.V // v ∈ S}, if (e.symm (x, xf)) v.1 = ξ v then (1 : ℝ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hxS x xf v]; exact if_neg hv)
    rw [hz, zero_mul, mul_zero]
  refine (Finset.sum_eq_single ξ h0 (fun h => absurd (Finset.mem_univ ξ) h)).trans ?_
  rw [hsummand ξ xf, if_pos rfl, one_mul]

end Arch

end TTN
