# Criticality refactor: selective verification

The public predicate `TTN.Arch.Critical` now means
`HasFDerivAt (𝕜 := ℝ) (a.loss Tstar) 0 θ`.
`NodewiseCritical` preserves the previous predicate body exactly.
`critical_iff_nodewiseCritical` proves both directions of their equivalence.

## Checked

An exact copy of `TTN/Landscape/CriticalityBasic.lean`, followed by a topology
compatibility example and the two axiom queries below, was checked from the
public-release project with:

```sh
lake env lean -DautoImplicit=false -DwarningAsError=true /private/tmp/TTNCriticalityCheck.lean
```

The temporary audit file contains the complete module source followed by:

```lean
example (a : TTN.Arch) :
    a.instNormedAddCommGroupParam.toMetricSpace.toUniformSpace.toTopologicalSpace =
      a.instTopologicalSpaceParam := rfl
#print axioms TTN.Arch.differentiable_loss
#print axioms TTN.Arch.critical_iff_nodewiseCritical
```

Exit status: 0. Elapsed time: 163.83 seconds.
Both queries returned only `[propext, Classical.choice, Quot.sound]`.
This checked the new definitions, loss differentiability, parameter-line
calculus, the existing nodewise line calculation, and the equivalence theorem.
It also checked that the normed-space topology is definitionally equal to the
existing product topology.

SHA-256 of the checked `CriticalityBasic.lean` source:
`db79bfa107ebfbb529a546b624b385adbb9ec5d196a226b502cedc2acc7fb9ad`

The development and public-release copies of this module are byte-identical.
The release production no-sorry gate passed. Static checks found no project
import cycles or missing project imports, and the theorem signatures in the
adapted FullRank, Dormant, and Compress modules were unchanged.

## Deliberately not checked

At the user's request, no full build, downstream-module compilation, full axiom
audit, or Comparator run was performed after this refactor. The conversions in
FullRank, Dormant, Compress, and the development-only dynamics/escape files are
source adaptations that still need compilation. `Criticality.lean` now obtains
the definitions and derivative lemmas through FullRank's import of
CriticalityBasic; its remaining optimization lemmas were not recompiled.

`Challenge.lean` was updated with the same standard definition and supporting
instances, and `AxiomAudit.lean` now includes the equivalence theorem. These
changes do not constitute a new Comparator certificate. Prior certificates do
not certify the refactored source until the release checks are rerun.

The manuscript was not edited as part of this code refactor.
