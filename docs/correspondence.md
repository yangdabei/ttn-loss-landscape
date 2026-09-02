# Paper-to-Lean correspondence

Declaration names and formal hypotheses are authoritative.

The `Relation` column uses a fixed vocabulary: `Exact` means the same statement
modulo notation; `Equivalent` is a logically equivalent reformulation;
`Stronger` implies the paper claim; `Specialized` narrows its setting;
`Conditional` adds a hypothesis; and `Partial` or `Not formalized` records a gap.

| Paper label or description | Lean declaration(s) | File | Relation | Note |
|---|---|---|---|---|
| Definition 4.1 — Minimum-norm parameter | `TTN.Arch.MinNorm` | `TTN/Contraction.lean` | Exact | — |
| Proposition C.1 — Realizability characterization | `TTN.Arch.ExtStruct.realizableLit_iff_rank_le`; aggregate form `TTN.Arch.realizable_iff_rank_le` | `TTN/Landscape/External.lean`; `TTN/Landscape/RealizabilityConverse.lean` | Partial | The rank characterization is exact; the prescribed-subspace clause is not formalized as a theorem. |
| Definition 5.1 — Full Tucker rank | `TTN.Arch.FullTuckerRank` | `TTN/Landscape/FullRank.lean` | Exact | — |
| Theorem 5.2 — Full-rank critical points are global | `TTN.Arch.critical_fullRank_represented_eq`; `TTN.Arch.critical_fullRank_isGlobalMin`; `TTN.Arch.not_fullRank_of_critical_of_not_isGlobalMin` | `TTN/Landscape/FullRank.lean` | Exact | The paper's standing realizability assumption is explicit; Lean also exports the equivalent contrapositive. |
| Definition E.1 — Dormant subspace | `TTN.Arch.dormant` | `TTN/Landscape/Dormant.lean` | Exact | — |
| Proposition E.2 — Minimum-norm kernel equalities and rank count | `minNorm_ker_Hfun_eq_dormant`, `minNorm_ker_Ffun_eq_dormant`, `minNorm_rank_add_finrank_dormant`, `minNorm_ker_matE_left_eq_dormant`, `minNorm_ker_matE_right_eq_dormant` | `TTN/Landscape/Dormant.lean` | Exact | Split into a reusable theorem family. |
| Proposition E.3 — Active directions are target-aligned | `TTN.Arch.minNorm_critical_ker_crossGram_le_dormant` | `TTN/Landscape/Dormant.lean` | Stronger | Quantifies over an arbitrary target factorization through the bond space. |
| Corollary E.4 — Model cut rank is bounded by target cut rank | `TTN.Arch.minNorm_critical_rank_le_target` | `TTN/Landscape/Dormant.lean` | Stronger | Does not require target realizability. |
| Corollary E.5 — Full model cut rank makes the cross-Gram invertible | `TTN.Arch.minNorm_critical_isUnit_crossGram` | `TTN/Landscape/Dormant.lean` | Stronger | Quantifies over arbitrary target factorizations and expresses invertibility as `IsUnit`. |
| Lemma E.6 — Reduction to target cut ranks | `TTN.Arch.exists_compress_reduction` and transfer lemmas | `TTN/Landscape/Compress.lean` | Conditional | The reduction theorem assumes a nonzero target; the final theorem handles the zero target separately. |
| Lemma E.8 — Mixed terms vanish under a coordinated core perturbation | `TTN.Arch.represented_add_corePerturb` | `TTN/Landscape/CoreDescent.lean` | Stronger | Generalized component-supported form. |
| Lemma E.9 — Strict local descent | `TTN.Arch.exists_loss_lt_of_pow_move` | `TTN/Landscape/CoreDescent.lean` | Stronger | Generalized pure-power-move form. |
| Theorem 4.3 — Minimum-norm local minima are global | `TTN.Arch.minNorm_isLocalMin_represented_eq`; `TTN.Arch.minNorm_isLocalMin_isGlobalMin` | `TTN/Landscape/LocalMin.lean` | Exact | The paper's standing realizability assumption is explicit. |
| Corollary 4.4 — Escape path from a non-solution | `TTN.Arch.exists_escape_path` | `TTN/Landscape/Escape.lean` | Conditional | Assumes the explicit in-fiber path hypothesis `hfiber`. |
| Definition G.1 — Minimal two-factor factorization | `TTN.MinFac.IsMinimalFac` | `TTN/Landscape/MinFac.lean` | Exact | — |
| Lemma G.2 — Minimal two-factor factorizations | `TTN.MinFac.isMinimalFac_iff_isCompl`; `exists_isMinimalFac_mem_closure_orbit`; `isMinimalFac_orbit` | `TTN/Landscape/MinFac.lean` | Exact | Split across the displayed declarations. |
| Proposition G.12 — Per-bond Gram-difference conservation | `TTN.Arch.bondGramDiff_conserved` | `TTN/Dynamics/Conservation.lean` | Specialized | Proved for the squared loss rather than an arbitrary differentiable loss of the represented tensor. |
| Lemma I.2 — Order bound on the parity coefficient | `TTN.Arch.parity_coefficient_order_bound` | `TTN/Dynamics/ParityLowerBound.lean` | Stronger | Lean proves the bound on the unit ball (`ρ = 1`). |
| Proposition 5.3 — Parity saddle and universal lower bound | `TTN.Arch.critical_halfParam`; `TTN.Arch.parity_saddle_achievable`; `TTN.Arch.parity_saddle_lower_bound` | `TTN/Dynamics/Parity.lean`; `TTN/Dynamics/ParityLowerBound.lean` | Stronger | The clauses are split across declarations, and the lower bound is proved on the unit ball. The exhibited descent line has order `n - 1`; this is not claimed to be the smallest possible descent order. |
