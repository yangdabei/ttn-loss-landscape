# Comparator certificate for Theorem 4.3

These non-default modules in the repository's root Lake workspace form the
Comparator certificate for the headline declaration:

```lean
TTN.Arch.minNorm_isLocalMin_isGlobalMin
```

`Challenge.lean` is the trusted statement and contains one deliberate `sorry`.
It imports only `TTN.Contraction` from this repository and repeats the
`IsGlobalMin` definition and parameter-space topology instances needed to state
the theorem. In particular, it does not import any `TTN.Landscape` module or
the theorem under test. `Solution.lean` imports the production theorem
unchanged.

Comparator is configured to require the same theorem statement, allow only
Lean's standard axioms `propext`, `Quot.sound`, and `Classical.choice`, and
replay the exported solution with Lean's kernel.

## Version pins

| Component | Pin |
|---|---|
| Lean | `v4.31.0` |
| Mathlib | `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (`v4.31.0`, inherited from the repository manifest) |
| Comparator | `fd2e25de155523dbce1f35d410511f9f63998461` (`v4.31.0`) |
| lean4export | `8554815c2dc6b7abe99ec1f08849c9759ba77947` (`v4.31.0`) |
| Landrun | `5ed4a3db3a4ad930d577215c6b9abaa19df7f99f` |

The surrounding repository revision is the pin for the formalization itself.
Run the certificate from a clean, immutable checkout of that revision.

## Ordinary elaboration check

From the repository root, without installing Comparator, the following checks
ordinary Lean elaboration:

```sh
lake env lean audit/comparator/Challenge.lean
lake env lean audit/comparator/Solution.lean
```

The warning for the single `sorry` in `Challenge.lean` is expected. The root
`lakefile.toml` declares `Challenge` and `Solution` as non-default libraries,
so the production `lake build` target remains `TTN` and does not include the
intentional challenge hole.

## Comparator run

On Linux, install the pinned Comparator, matching `lean4export`, and Landrun
from source. From a fresh repository checkout, initialize the root Lake
workspace without building either certificate module:

```sh
lake update
lake exe cache get
```

Then run the command prescribed by the upstream Comparator documentation,
including its outer `systemd-run` restriction, with the repository root as the
working directory and `audit/comparator/config.json` as the configuration. A
security-sensitive run must not compile `Solution.lean` or its production
imports before Comparator takes control. An ordinary build of `Challenge.lean`
is safe because its source and import closure are part of the trusted
specification.

The repository's `.github/workflows/comparator.yml` is the reproducible Linux
reference run. It installs every security-sensitive tool at the pins above,
checks that Landrun actually denies a write outside `.lake`, invokes Comparator
under the required systemd network guard, and requires Lean's kernel to accept
the exported proof.

`.github/CODEOWNERS` marks the trusted challenge, its local import boundary,
the toolchain pins, and the workflow for review by `@yangdabei`. To make this an
enforced gate, enable branch protection on `main` and require Code Owner review.
For a solo-maintainer workflow, leave it as review documentation or add a
second trusted reviewer first, since an author cannot approve their own pull
request.

## Recorded local check

On 1 September 2026, the pinned configuration passed a macOS smoke run: the
challenge and production theorem matched, the solution used only the three
permitted axioms, and Lean's kernel accepted the exported proof. That run used
Comparator's explicitly insecure `fake-landrun.sh`, because Landrun is
Linux-only. It therefore establishes the comparison and kernel replay, but not
sandbox isolation. The Linux workflow above is the reference for the full
sandboxed run.

## What this certificate does not establish

Comparator checks agreement with the trusted Lean challenge, the permitted
axiom set, and kernel acceptance.  It does not establish that the Lean
statement faithfully expresses the natural-language theorem.  That remains
the purpose of the authors' statement review and the paper-to-Lean
correspondence document.

The trusted import boundary includes `TTN.Contraction` and its transitive
imports. A still more independent certificate would copy or move all
statement-side TTN definitions into a separately reviewed module that imports
only Mathlib. The present layout avoids importing or trusting every landscape
proof module, including the proof of Theorem 4.3, but it is not a Mathlib-only
challenge.
