# OxiDD Lite

[![Matrix](https://img.shields.io/badge/matrix-join_chat-brightgreen?style=for-the-badge&logo=matrix)](https://matrix.to/#/#oxidd:matrix.org)

This is a stripped-down version of the decision diagram framework [OxiDD](https://github.com/OxiDD/oxidd), intended as a playground for formally verifying OxiDD's functional correctness. In contrast to OxiDD, OxiDD lite …

- … only supports BDDs with ∧ and ¬
- … is very small (< 200 LOC excluding tests)
- … is not optimized for performance
- … has no unsafe code
- … is unsuitable for concurrency
- … has no garbage collection. When constructing a decision diagram, we typically create a lot of intermediate results with nodes that are not needed for the end result. We keep them as long as possible because some workloads result in high rebirth rates. Still we want to remove dead nodes before running out of memory.
- … does not support reordering. Reordering is an operation that swaps levels of a decision diagram in-place to reduce the diagram's size. This requires modification of nodes.

We presented OxiDD lite as part of a verification challenge at the [Rust Verification Workshop 2024](https://sites.google.com/view/rustverify2024). It would be great to have all of OxiDD verified. Towards this goal, we thought that it makes sense to start small. Also, it is unclear what tool is suitable to verify OxiDD at the full scale.

The developers of the verification tool [Creusot](https://github.com/creusot-rs/creusot) have created a verified BDD library as part of their test suite ([current version](https://github.com/creusot-rs/creusot/blob/master/creusot/tests/should_succeed/bdd.rs) / [permalink](https://github.com/creusot-rs/creusot/blob/04ef3b24aa19c33de48b617fec3c7c998277d340/creusot/tests/should_succeed/bdd.rs)). While there are a few technical differences between Creusot's test and OxiDD lite (e.g., Creusot's test uses a trusted axiomatic characterization of a bump allocator while OxiDD lite explicitly performs the allocation in a `Vec`), Creusot has basically solved the OxiDD lite challenge. We are still very interested in proofs using other verification tools. That way, OxiDD lite can serve as a testbed and benchmark to compare different tools and approaches. It will be interesting to see how the proofs compare with respect to their complexity, the proof overhead, and the time to verify (i.e., to run the solvers). Moreover, the question is how get from verified OxiDD lite to the large-scale verification of OxiDD.

## Structure of This Repository

This repository has three branches:

- `index-based` is the "main" branch that represents edges as indices, which appears to be easier for verification
- `pointer-based` is an alternative implementation that uses the `Rc` type to represent edges
- `creusot-index-based` is our attempt to verify the code of the `index-based` branch using [Creusot](https://github.com/creusot-rs/creusot). It is still work-in-progress.
