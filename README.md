# TTN Loss Landscapes

This repository contains a Lean 4 formalization of the principal
loss-landscape results accompanying *Benign Loss Landscapes Can Coexist with
Worst-Case Hardness* by Zach Furman, Stephan Wäldchen, and Liam Hodgkinson.
The manuscript does not yet have a public URL.

## The result

A tree tensor network (TTN) places a tensor at every node of a tree and
contracts matching internal indices along the tree's edges. The resulting
tensor depends nonlinearly on the collection of node tensors, called the
parameter point. We study the squared error between that represented tensor
and a target tensor.

The headline theorem concerns a realizable target—one represented by some
parameter point. Among all parameter points representing the same tensor, call
one *minimum-norm* when its total squared parameter norm is smallest. Then:

> Every minimum-norm parameter point that is a local minimum of the squared
> loss is a global minimum and has zero loss.

This is Theorem 4.3 of the manuscript. Its Lean declaration is
`TTN.Arch.minNorm_isLocalMin_isGlobalMin`.

## Main declarations

| Source result | Lean declaration | Formalized result |
| --- | --- | --- |
| Theorem 4.3 | `TTN.Arch.minNorm_isLocalMin_isGlobalMin` | A minimum-norm local minimum for a realizable target is global, with zero loss. |
| Theorem 5.2 | `TTN.Arch.critical_fullRank_isGlobalMin` | A full-Tucker-rank critical point for a realizable target is a global minimum. |
| Proposition 5.3 | `TTN.Arch.parity_saddle_lower_bound` | Near the parity halfway point, every loss decrease obeys the stated order lower bound. |

The complete [paper-to-Lean correspondence](docs/correspondence.md) records
the supporting results and the exact relation of each Lean statement to its
manuscript counterpart. The manuscript authors reviewed the mapped statements
for faithfulness.

## Scope and qualifications

The production library contains no `sorry`, `admit`, `native_decide`, or
project `axiom` declarations. The audited theorems use only Lean's standard
logical axioms `propext`, `Classical.choice`, and `Quot.sound`.

The following qualifications matter:

- Theorem 5.2 states the manuscript's standing target-realizability assumption
  explicitly.
- Corollary 4.4 retains an explicit in-fiber path hypothesis, `hfiber`; the
  required semialgebraic and geometric-invariant-theory results are not
  formalized.
- The main development aggregates the external tensor modes at each node. A
  separate theorem bridges the realizability/rank characterization to literal
  individual external modes, but the full landscape theory is not transported
  to those coordinates.
- The computational-hardness and Boolean-expressivity arguments are outside
  this Lean development.

See [scope and deviations](docs/deviations.md) for the precise mathematical
details.

## Building and verification

The project pins Lean `v4.31.0` and the matching Mathlib release. With
[elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
bash scripts/no_sorry.sh
lake build
lake lint
lake env lean AxiomAudit.lean
```

Importing [`TTN.lean`](TTN.lean) checks the complete production
formalization. `AxiomAudit.lean` reports the axiom dependencies of the
headline and important supporting results.

## Comparator

[`Challenge.lean`](Challenge.lean) restates the loss-landscape definitions and
all three main declarations without importing any module that proves them. The
parity architecture and statement-side data live in the shared trusted module
[`TTN/Dynamics/ParitySpec.lean`](TTN/Dynamics/ParitySpec.lean), avoiding
proof-dependent duplication. The three `sorry` bodies in `Challenge.lean` are
intentional specification placeholders and are never imported by the
production library.

With the upstream Comparator sandbox requirements satisfied and `landrun` and
`lean4export` on `PATH`:

```sh
lake exe cache get
lake exe comparator comparator/main.json
```

The [Comparator configuration](comparator/main.json) checks statement
agreement, enforces the three-standard-axiom allowlist, and replays the proofs
with Lean's kernel. This verifies the formal statements and proof terms; their
correspondence with the natural-language manuscript is the separate
author-review claim described above. See the
[verification notes](docs/verification.md) for the trust boundary and pinned
tool versions.

## Citation and license

Citation metadata for this formalization and the associated manuscript is in
[`CITATION.cff`](CITATION.cff). AI-assisted development is disclosed in the
[development history](docs/development.md).

The code is released under the [Apache License 2.0](LICENSE).
