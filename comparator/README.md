# [Comparator](https://github.com/leanprover/comparator)

Follow the [upstream setup and sandbox requirements](https://github.com/leanprover/comparator/blob/fd2e25de155523dbce1f35d410511f9f63998461/README.md), with
`landrun` and `lean4export` on `PATH`. From the repository root inside that
sandbox:

```sh
lake exe cache get
lake exe comparator comparator/main.json
```

The certificate compares the three [main results](../README.md#main-declarations)
with the trusted `Challenge.lean`, permits only `propext`, `Quot.sound`, and
`Classical.choice`, and replays the proofs with Lean's kernel. It checks the
formal statements and proof terms, not their correspondence with the
manuscript; that correspondence received a separate author review.
