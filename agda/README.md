# +-comm in Agda

The proof that addition is commutative for the natural numbers can be found, for example, in the Agda standard library (`agda-stdlib`) in `Data.Nat.Properties` as `+-comm`.

We provide two versions:

* `+-comm.agda` contains a proof using standard imports;
* `+-comm-no-imports.agda` contains the (same) proof, together with all the definitions used, so no imports are needed.

## Features of Agda exhibited in the proof

* In Agda, it is standard to write out the proof terms instead of using tactics, as in Coq or Lean. Consequently, you do not need an IDE in order to be read all the details in the Agda code.

* Following the Curry–Howard correspondence, propositions are expressed as types and are proven by exhibiting a member of that type, by constructing a program that takes the given inputs and produces an output of the given type.

* Due to this overarching framework, proving things in Agda resembles writing a program in a functional programming language. This similarity is strengthened by its syntax and prevalent use of pattern-matching and other FP-isms familiar to those fluent in ML-family languages like Haskell or OCaml.

