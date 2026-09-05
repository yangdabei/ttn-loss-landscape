# Verification and trust boundary

The repository has three complementary checks:

1. `scripts/no_sorry.sh` rejects `sorry`, `admit`, `native_decide`, and project
   `axiom` declarations in the production library.
2. `AxiomAudit.lean` asks Lean to report the axiom dependencies of the main and
   important supporting results.
3. Comparator checks the two main declarations against `Challenge.lean`,
   enforces the standard-axiom allowlist, and replays their proof terms with
   Lean's kernel.

## Comparator trust boundary

`Challenge.lean` imports `TTN.Contraction` and its transitive imports. It repeats
the loss-landscape definitions needed to state Theorem 4.3 and Theorem 5.2, but
does not import a production module containing either target theorem.

The two theorem `sorry` bodies in `Challenge.lean` are intentional
specification holes. The production library never imports `Challenge`, and the
no-sorry gate scans only production sources.

Comparator establishes that the challenge and production declarations have the
same formal statements, that the production proofs use no axioms beyond
`propext`, `Quot.sound`, and `Classical.choice`, and that Lean's kernel accepts
the exported proofs. Comparator does not establish that the formal statements
faithfully express the manuscript; the manuscript authors reviewed that
correspondence separately.

## Version pins

| Component | Pin |
| --- | --- |
| Lean | `v4.31.0` |
| Mathlib | `v4.31.0`, resolved exactly in `lake-manifest.json` |
| Comparator | `fd2e25de155523dbce1f35d410511f9f63998461` |
| lean4export | `8554815c2dc6b7abe99ec1f08849c9759ba77947` |
| Landrun | `5ed4a3db3a4ad930d577215c6b9abaa19df7f99f` |

The repository revision pins the formalization and challenge themselves. A
security-sensitive Comparator run should use a clean, immutable checkout and
follow the
[upstream sandbox instructions](https://github.com/leanprover/comparator/blob/fd2e25de155523dbce1f35d410511f9f63998461/README.md).
The repository's Comparator workflow is the reproducible Linux reference run.
