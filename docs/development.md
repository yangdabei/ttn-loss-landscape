# Development history

The substantive formalization was developed from 29 June through 2 July 2026
using Anthropic's Claude Fable 5 and Claude Opus 4.8 models; project-close and
repository-reorganization work continued on 3 July. Claude Fable 5 was the
primary model, and Claude Opus 4.8 was used for selected proof obligations.
OpenAI's GPT-5.5 model was used mainly for mathematical audits and
proof-strategy review and supplied two small Lean proof bodies.

On 1 September 2026, OpenAI's GPT-5.6-Sol model was used to formalize the
manuscript's universal parity-saddle lower bound (Lemma I.2 and Proposition
5.3). Subscription access was used for both the Anthropic and OpenAI models.

A complete project-level record of token use, wall time, and billed cost was not
retained, so no API-equivalent cost is estimated. Candidate code was integrated
into the repository and checked by Lean against the pinned Mathlib revision.
Lean checks the encoded declarations and their proofs. The authors separately
checked that the formal theorem statements faithfully represent the
corresponding statements in the manuscript.
