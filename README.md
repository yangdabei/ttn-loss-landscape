# TTN loss landscapes in Lean

This repository contains a Lean 4 formalization of the principal loss-landscape
results accompanying *Benign Loss Landscapes Can Coexist with Worst-Case
Hardness*.

## Main theorem

> *For a realizable target, every TTN parameter point that is both a local minimum of the squared loss and minimum-norm within its fiber is a global minimum, with zero loss.*

This formalizes Theorem 4.3 of the manuscript:

```lean
theorem TTN.Arch.minNorm_isLocalMin_isGlobalMin
```

See [paper-to-Lean correspondence](docs/correspondence.md) for the other
formalized results and [scope and deviations](docs/deviations.md) for the exact
qualifications.

## Verification and build

- Lean: `v4.31.0`
- Mathlib: `v4.31.0`, pinned by `lake-manifest.json`
- The production library contains no `sorry`, `admit`, `native_decide`, or
  project `axiom` declarations.

```sh
lake exe cache get
bash scripts/no_sorry.sh
lake build
lake env lean AxiomAudit.lean
```

AI-assisted development is disclosed in [development history](docs/development.md).
The root [formalization metadata](formalization.yaml) records the formalized
scope, source alignment, automation, review status, and axioms in the
Mathlib Initiative's v0.4 format.

An additional [Comparator certificate](audit/comparator/README.md) checks the
headline Theorem 4.3 against a separately stated trusted challenge, enforces
the three-axiom allowlist, and replays the production proof with Lean's kernel.
The certificate challenge deliberately contains one
`sorry`; it is a specification hole, not part of the production library. The
Linux workflow adds Landrun isolation, while a macOS run can exercise the
comparison and kernel replay without that sandbox guarantee.

## Citation and license

Citation metadata for the formalization is in [CITATION.cff](CITATION.cff).
Please also cite the associated paper when using its mathematical results.

The code is released under the [Apache License 2.0](LICENSE).
