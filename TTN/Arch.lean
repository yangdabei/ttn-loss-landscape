import Mathlib

/-!
# Tree tensor networks: combinatorial architecture and index types

This module fixes the **architecture** of a tree tensor network (Definition 3.1):
a finite set of nodes carrying a tree of internal *bonds*, a bond dimension for
each internal edge, and a combined external dimension `n_v` at each node. It then
defines the index types over which node tensors and the represented tensor range.

## Modeling choices

* Internal edges are the edge set of a `SimpleGraph V` constrained to be a tree
  (`G.IsTree`); a bond `e` carries dimension `r e`.
* **External legs are aggregated per node** into a single combined dimension
  `n_v = ∏_{e external at v} d_e` — the aggregate notation used in this development.
  This is bridged to the literal "one mode per external edge" of Def 3.1 by
  `TTN/Landscape/External.lean`, via an *entry bijection* `Fin (n v) ≃ (Π e, Fin d_e)`
  (an arbitrary enumeration, not the lexicographic/tensor iso — sufficient for
  the rank/realizability statements, which are invariant under any index
  bijection).
* Contraction is the **global bond-sum** (see `TTN/Contraction.lean`); the tree
  hypothesis is needed only for the cut-factorization / rank results, not to
  define the represented tensor.
-/

namespace TTN

/-- A **tree tensor network architecture** (Definition 3.1, combinatorial part).

`V` is the finite set of nodes; the internal edges (bonds) are the edges of a tree
`G` on `V`. Each bond `e` has a positive bond dimension `r e`, and each node `v`
has a positive combined external dimension `n v` (the product of its external-edge
dimensions). The node tensors themselves are the *parameters* `Param a`, defined
separately so that one architecture supports many parameter points. -/
structure Arch where
  /-- The finite set of nodes. -/
  V : Type
  [fV : Fintype V]
  [dV : DecidableEq V]
  /-- The internal edges (bonds), as the edges of a graph on `V`. -/
  G : SimpleGraph V
  [dG : DecidableRel G.Adj]
  /-- The two-ended (internal) edges form a tree on `V`. -/
  hT : G.IsTree
  /-- Bond dimension `r_e` of each internal edge. -/
  r : Sym2 V → ℕ
  /-- Combined external dimension `n_v = ∏ d_e` at each node. -/
  n : V → ℕ
  /-- Bond dimensions are positive. -/
  hr : ∀ e ∈ G.edgeSet, 0 < r e
  /-- External dimensions are positive. -/
  hn : ∀ v, 0 < n v

attribute [instance] Arch.fV Arch.dV Arch.dG

namespace Arch

variable (a : Arch)

/-- The internal edges **incident** to a node `v`: bonds `e ∈ G.edgeSet` with `v ∈ e`. -/
def Inc (v : a.V) : Type := {e : Sym2 a.V // e ∈ a.G.edgeSet ∧ v ∈ e}

instance (v : a.V) : Fintype (a.Inc v) := by
  unfold Inc; infer_instance

instance (v : a.V) : DecidableEq (a.Inc v) := by
  unfold Inc; infer_instance

/-- A **bond multi-index at `v`**: a choice, for each incident bond `e`, of an index
in `Fin (r e)`. The node tensor at `v` ranges over these on its internal modes. -/
def BondIdx (v : a.V) : Type := (e : a.Inc v) → Fin (a.r e.1)

instance (v : a.V) : Fintype (a.BondIdx v) := by
  unfold BondIdx; infer_instance

/-- A **global bond assignment**: a choice of index `Fin (r e)` for every internal
edge `e`. The represented tensor is the sum over these (`TTN/Contraction.lean`). -/
def Bond : Type := (e : a.G.edgeSet) → Fin (a.r e.1)

instance : Fintype a.Bond := by
  unfold Bond; infer_instance

/-- The **external index** of the represented tensor: a choice of external index
`Fin (n v)` at every node. The represented tensor is a function `Ext a → ℝ`. -/
def Ext : Type := (v : a.V) → Fin (a.n v)

instance : Fintype a.Ext := by
  unfold Ext; infer_instance

/-- Restrict a global bond assignment to the incident bonds of a node `v`. -/
def Bond.restrict {a : Arch} (b : a.Bond) (v : a.V) : a.BondIdx v :=
  fun e => b ⟨e.1, e.2.1⟩

end Arch

end TTN
