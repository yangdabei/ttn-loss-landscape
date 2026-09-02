import TTN.Landscape.CoreDescent

/-!
# Sign flip of the leading descent term

If the compressed-residual pairing is positive at the chosen indicator tensors, negate
the free tensor at one component node:
the leading term `T_N` (hence the pairing) flips sign, and the admissibility hypotheses of
`represented_add_corePerturb` are preserved. Three small lemmas:

* `represented_update_neg` — negating one node tensor negates the represented tensor.
* `corePerturb_update_neg` — `corePerturb` is pointwise in the free tensor, so a one-node
  negation of `G` is a one-node negation of the perturbation.
* `piecewise_corePerturb_update_neg` — the piecewise leading-term parameter with the negated
  free tensor is a one-node update of the original by the negated node tensor.
-/

namespace TTN

namespace Arch

variable {a : Arch}

/-- Negating one node tensor negates the represented tensor. -/
theorem represented_update_neg (Θ : a.Param) (v₀ : a.V) (W : a.NodeTensor v₀) (x : a.Ext) :
    a.represented (Function.update Θ v₀ (fun bi xv => - W bi xv)) x
      = - a.represented (Function.update Θ v₀ W) x := by
  classical
  show (∑ b : a.Bond, ∏ v,
      Function.update Θ v₀ (fun bi xv => - W bi xv) v (Bond.restrict b v) (x v))
    = - ∑ b : a.Bond, ∏ v, Function.update Θ v₀ W v (Bond.restrict b v) (x v)
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v₀),
    ← Finset.mul_prod_erase Finset.univ
      (fun v => Function.update Θ v₀ W v (Bond.restrict b v) (x v)) (Finset.mem_univ v₀),
    Function.update_self, Function.update_self]
  have hrest : (∏ v ∈ Finset.univ.erase v₀,
      Function.update Θ v₀ (fun bi xv => - W bi xv) v (Bond.restrict b v) (x v))
      = ∏ v ∈ Finset.univ.erase v₀,
          Function.update Θ v₀ W v (Bond.restrict b v) (x v) := by
    refine Finset.prod_congr rfl (fun v hv => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hv),
      Function.update_of_ne (Finset.ne_of_mem_erase hv)]
  rw [hrest]
  ring

/-- `corePerturb` is pointwise in the free tensor: a one-node negation of `G` is a one-node
negation of the perturbation. -/
theorem corePerturb_update_neg (K : Finset a.G.edgeSet)
    (η : (E : a.G.edgeSet) → Fin (a.r E.1) → ℝ) (G : (v : a.V) → a.NodeTensor v)
    (v₀ : a.V) (v : a.V) (bi : a.BondIdx v) (xv : Fin (a.n v)) :
    a.corePerturb K η
        (Function.update G v₀ (fun bi xv => - G v₀ bi xv)) v bi xv
      = (if v = v₀ then -1 else 1) * a.corePerturb K η G v bi xv := by
  classical
  by_cases hv : v = v₀
  · subst hv
    rw [if_pos rfl]
    show (∏ e ∈ Finset.univ.filter
        (fun e : a.Inc v => (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ K), η ⟨e.1, e.2.1⟩ (bi e))
      * Function.update G v (fun bi xv => - G v bi xv) v bi xv = _
    rw [Function.update_self]
    show _ * (- G v bi xv) = _
    unfold corePerturb
    ring
  · rw [if_neg hv]
    show (∏ e ∈ Finset.univ.filter
        (fun e : a.Inc v => (⟨e.1, e.2.1⟩ : a.G.edgeSet) ∈ K), η ⟨e.1, e.2.1⟩ (bi e))
      * Function.update G v₀ (fun bi xv => - G v₀ bi xv) v bi xv = _
    rw [Function.update_of_ne hv]
    unfold corePerturb
    ring

/-- The piecewise leading-term parameter at the negated free tensor is a one-node update of
the original by the negated node tensor (for a component node `v₀ ∈ S`). -/
theorem piecewise_corePerturb_update_neg (S : Finset a.V) (K : Finset a.G.edgeSet)
    (η : (E : a.G.edgeSet) → Fin (a.r E.1) → ℝ) (G : (v : a.V) → a.NodeTensor v)
    (θ : a.Param) {v₀ : a.V} (hv₀ : v₀ ∈ S) :
    S.piecewise (a.corePerturb K η
        (Function.update G v₀ (fun bi xv => - G v₀ bi xv))) θ
      = Function.update (S.piecewise (a.corePerturb K η G) θ) v₀
          (fun bi xv => - a.corePerturb K η G v₀ bi xv) := by
  classical
  funext v
  by_cases hv : v = v₀
  · subst hv
    rw [Function.update_self, S.piecewise_eq_of_mem _ _ hv₀]
    funext bi xv
    rw [a.corePerturb_update_neg K η G v v bi xv, if_pos rfl]
    ring
  · rw [Function.update_of_ne hv]
    by_cases hvS : v ∈ S
    · rw [S.piecewise_eq_of_mem _ _ hvS, S.piecewise_eq_of_mem _ _ hvS]
      funext bi xv
      rw [a.corePerturb_update_neg K η G v₀ v bi xv, if_neg hv]
      ring
    · rw [S.piecewise_eq_of_notMem _ _ hvS, S.piecewise_eq_of_notMem _ _ hvS]

end Arch

end TTN
