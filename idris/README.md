# plusCommutative in Idris (Idris2)

The official Idris2 tutorial uses the commutativity of addition for natural numbers as [the running example in its introduction to theorem proving](https://idris2.readthedocs.io/en/latest/proofs/pluscomm.html#), and provides a few different proofs. We include an elementary proof of the result in  `plusCommutative_no_imports.idr`. The corresponding functions are included in Idris's `Prelude` library, under `Prelude.Nat`; they are not yet the `Prelude` for Idris2.

Idris is quite similar to Agda, especially in its syntax and emphasis on pattern-matching and programming in a functional style. The main surface-level difference between the two languages is that, as a conscious design choice, [Idris does not support the use of Unicode characters for operators](https://docs.idris-lang.org/en/latest/faq/faq.html#will-there-be-support-for-unicode-characters-for-operators).
