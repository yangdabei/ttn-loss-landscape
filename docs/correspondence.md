# Paper-to-Lean correspondence

Declaration names and formal hypotheses are authoritative.

The `Relation` column uses a fixed vocabulary: `Exact` means the same statement
modulo notation; `Equivalent` is a logically equivalent reformulation; `By
specialisation` means the paper statement follows by instantiating a reusable
general declaration; `Conditional` adds a hypothesis; and `Partial` or `Not
formalized` records a gap.

| Paper label or description | Lean declaration(s) | File | Relation | Note |
|---|---|---|---|---|
| Definitions 3.1 and B.5 — Directed and contraction TTN presentations | `TTN.Arch.representedFromRoot_eq_represented` | `TTN/Contraction.lean` | Equivalent | After choosing bases, the directed multilinear composition expands to the same global bond sum as undirected contraction; the root disappears from the coordinate formula. |
| Definition 4.1 — Minimum-norm parameter | `TTN.Arch.MinNorm` | `TTN/Contraction.lean` | Exact | — |
| Proposition C.1 — Realizability characterization | `TTN.Arch.ExtStruct.realizableLit_iff_rank_le`; equivalent per-vertex reshaped form `TTN.Arch.realizable_iff_rank_le` | `TTN/Landscape/External.lean`; `TTN/Landscape/RealizabilityConverse.lean` | Partial | The rank characterization is exact; the prescribed-subspace clause is not formalized as a theorem. |
| Definition 5.1 — Full Tucker rank | `TTN.Arch.FullTuckerRank` | `TTN/Landscape/FullRank.lean` | Exact | — |
| Theorem 5.2 — Full-rank critical points are global | `TTN.Arch.critical_fullRank_represented_eq`; `TTN.Arch.critical_fullRank_isGlobalMin`; `TTN.Arch.not_fullRank_of_critical_of_not_isGlobalMin` | `TTN/Landscape/FullRank.lean` | Exact | The paper's standing realizability assumption is explicit; Lean also exports the equivalent contrapositive. |
| Definition E.1 — Dormant subspace | `TTN.Arch.dormant` | `TTN/Landscape/Dormant.lean` | Exact | — |
| Proposition E.2 — Minimum-norm kernel equalities and rank count | `minNorm_ker_Hfun_eq_dormant`, `minNorm_ker_Ffun_eq_dormant`, `minNorm_rank_add_finrank_dormant`, `minNorm_ker_matE_left_eq_dormant`, `minNorm_ker_matE_right_eq_dormant` | `TTN/Landscape/Dormant.lean` | Exact | Split into a reusable theorem family. |
| Proposition E.3 — Active directions are target-aligned | `TTN.Arch.minNorm_critical_ker_crossGram_le_dormant` | `TTN/Landscape/Dormant.lean` | By specialisation | Choose the target factorization induced by the paper's target realization. |
| Corollary E.4 — Model cut rank is bounded by target cut rank | `TTN.Arch.minNorm_critical_rank_le_target` | `TTN/Landscape/Dormant.lean` | By specialisation | Impose the paper's standing target-realizability assumption. |
| Corollary E.5 — Full model cut rank makes the cross-Gram invertible | `TTN.Arch.minNorm_critical_isUnit_crossGram` | `TTN/Landscape/Dormant.lean` | By specialisation | Choose the factorization induced by the target realization; `IsUnit` expresses invertibility. |
| Lemma E.6 — Reduction to target cut ranks | `TTN.Arch.exists_compress_reduction` and transfer lemmas | `TTN/Landscape/Compress.lean` | Exact | Both statements assume a nonzero target; the final theorem handles the zero target separately. |
| Lemma E.8 — Mixed terms vanish under a coordinated core perturbation | `TTN.Arch.represented_add_corePerturb` | `TTN/Landscape/CoreDescent.lean` | By specialisation | The paper statement is the component-supported instance. |
| Lemma E.9 — Strict local descent | `TTN.Arch.exists_loss_lt_of_pow_move` | `TTN/Landscape/CoreDescent.lean` | By specialisation | The paper statement is the pure-power-move instance. |
| Theorem 4.3 — Minimum-norm local minima are global | `TTN.Arch.minNorm_isLocalMin_represented_eq`; `TTN.Arch.minNorm_isLocalMin_isGlobalMin` | `TTN/Landscape/LocalMin.lean` | Exact | The paper's standing realizability assumption is explicit. |
| Corollary 4.4 — Escape path from a non-solution | `TTN.Arch.exists_escape_path` | `TTN/Landscape/Escape.lean` | Conditional | Assumes the explicit in-fiber path hypothesis `hfiber`. |
| Definition G.1 — Minimal two-factor factorization | `TTN.MinFac.IsMinimalFac` | `TTN/Landscape/MinFac.lean` | Exact | — |
| Lemma G.2 — Minimal two-factor factorizations | `TTN.MinFac.isMinimalFac_iff_isCompl`; `exists_isMinimalFac_mem_closure_orbit`; `isMinimalFac_orbit` | `TTN/Landscape/MinFac.lean` | Exact | Split across the displayed declarations. |
