import TTN.Arch

/-!
# Node tensors, the represented tensor, and the squared loss

Building on `TTN/Arch.lean`, this module defines the **parameters** of a tree
tensor network (the node tensors), the **represented tensor** `T(θ)` obtained by
contracting along the internal bonds, and the **squared loss** against a target,
with its residual.

The represented tensor is the *global bond-sum*

  `T(θ)(x) = ∑_{b : Bond} ∏_{v} W_v(b|_v, x_v)`,

summing over all internal bond assignments `b` the product of the node-tensor
entries; because every internal bond is shared by exactly its two endpoints, this
global sum is exactly the contracted tensor.
-/

namespace TTN

namespace Arch

variable (a : Arch)

/-- A **node tensor** `W_v`: a real array over `v`'s incident bond multi-index and
its external index (one mode per incident bond, plus the combined external mode). -/
def NodeTensor (v : a.V) : Type := a.BondIdx v → Fin (a.n v) → ℝ

/-- The **parameters** `θ = {W_v}_{v ∈ V}` of the network: a node tensor at each node. -/
def Param : Type := (v : a.V) → a.NodeTensor v

/-- The **represented tensor** `T(θ)`: contract the node tensors along
the internal bonds. Realised as the sum over all global bond assignments of the
product of node entries. -/
def represented (θ : a.Param) : a.Ext → ℝ :=
  fun x => ∑ b : a.Bond, ∏ v : a.V, θ v (Bond.restrict b v) (x v)

/-- The **residual** `R := T(θ) - T*` of the squared loss against a target `T*`. -/
def residual (Tstar : a.Ext → ℝ) (θ : a.Param) : a.Ext → ℝ :=
  fun x => a.represented θ x - Tstar x

/-- The **squared loss** `L(θ) = ½‖T(θ) - T*‖_F²`. -/
noncomputable def loss (Tstar : a.Ext → ℝ) (θ : a.Param) : ℝ :=
  (1 / 2) * ∑ x : a.Ext, (a.represented θ x - Tstar x) ^ 2

/-- Squared Frobenius norm of a single node tensor `W_v`. -/
def nodeNormSq (θ : a.Param) (v : a.V) : ℝ :=
  ∑ bi : a.BondIdx v, ∑ x : Fin (a.n v), (θ v bi x) ^ 2

/-- Squared parameter norm `‖θ‖² = ∑_v ‖W_v‖_F²` (Definition 4.1). -/
def paramNormSq (θ : a.Param) : ℝ := ∑ v : a.V, a.nodeNormSq θ v

/-- A target `T*` is **realizable** if some parameter point represents it
(`T*` lies in the image of the TTN parameterization). -/
def Realizable (Tstar : a.Ext → ℝ) : Prop := ∃ θ : a.Param, a.represented θ = Tstar

/-- **Paper correspondence: Definition 4.1, minimum-norm point.**
`θ` has minimum parameter norm among all parameters producing the same represented tensor. -/
def MinNorm (θ : a.Param) : Prop :=
  ∀ θ' : a.Param, a.represented θ' = a.represented θ → a.paramNormSq θ ≤ a.paramNormSq θ'

end Arch

end TTN
