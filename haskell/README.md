# Commutativity of Addition in Haskell

While Haskell's default Hindley–Milner-based type system is stronger than that of almost all programming languages (and certainly so if you filter for those in use in industry), it is not powerful enough to encode the fact that the sum of two natural numbers is commutative. However, by enabling a couple of language extensions in the Glasgow Haskell Compiler  and using the technique of "programming with singleton types," we can simulate a weak form of dependent types in a non-dependently-typed langauge like Haskell. This turns out to be just strong enough to express statements like the commutativity of addition and have the typechecker verify our proofs.

*Singleton types* are types that have only one value. Types in Haskell can depend on types, but not on values. However, wrapping a value in singleton type allows us to carry that value into the type world and have other types now depend on that wrapped type. There are a number of subtleties and technical caveats on how this actually works, but this is the basic idea. The key consequence is that singleton types allow us to pattern match and extract the value that it wraps. 

Phrasing things in terms of the associated singleton types, we can proceed with our proof just as we would in any dependently typed language. The interactivity and user interface is much better in the theorem provers, but at the end of the day, the proof terms are more or less equivalent.

## A Warning

Haskell's type system is not designed to serve as a theorem prover and in particular has some "escape hatches" that languages designed for theorem proving do not have. For one, defining any function as `undefined` causes that function to typecheck, even when you have not provided any proof. For another, there is no built-in termination checking in Haskell, so you can also potentially use infinitely recursive definitions like `let x = x in x` to satisfy the typechecker.  (Both of these are statements are essentially saying that *all* types in Haskell have a "bottom" element.) Features like these are good "quality of life" choices for a programming language that actually wants to *run* programs (and not just typecheck them), but make for a poor basis on which to build a theorem prover.

If you actually want something like "Haskell verified with proofs" something like [agda2hs](https://github.com/agda/agda2hs)—which allows you to compile Agda to Haskell in a relatively direct way, in contrast to the built-in Haskell backend `MAlonzo`—may be more appropriate than the type-level tricks used here. Of course, if that level of verification is not required, there is any number of techniques that one can use in Haskell, from things as simple as type annotations to the latest and greatest in language extensions and type-level acrobatics. Using singleton types as we do is somewhere near the middle of this vast spectrum.

## Additional Resources

For more on singleton types in Haskell, we refer the reader to the [singletons library](https://github.com/goldfirere/singletons) and [Justin Le's series of blog posts](https://blog.jle.im/entry/introduction-to-singletons-1.html) which gives a gentle introduction to the `singletons` library, aimed at Haskell programmers with no assumed knowledge of dependent types. For a discussion of some of the limitations of singleton types from the perspective of dependently typed programming, Lindley and McBride's [Hasochism
paper](https://homepages.inf.ed.ac.uk/slindley/papers/hasochism.pdf) remains as convincing today as it did in 2013.
