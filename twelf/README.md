# Twelf

[Twelf](http://twelf.org/wiki/Main_Page) is an implementation of the Edinburgh Logical Framework ("ELF," whence the name, but commonly referred to as simply "LF"), which is a formalism for expressing logics, theorems, and proofs. It succeeds an earlier representation, called [Elf](http://www.cs.cmu.edu/~fp/elf.html), dating from the early 1990s. 

Twelf, like most of the other proof assistants in this repository, is based on intuitionistic/constructive dependent type theory and so proofs can be written in a similar fashion. However, one difference between Twelf and something like Coq or Agda is [how it checks that definitions are total](http://twelf.org/wiki/%25worlds), which requires a declaration of a context ("world" in LF lingo) in which a totality assertion is verified.  The lines in `plus-comm.elf` beginning with `%mode`, `%worlds`, `%unique`, or `%total` are all for this purpose.

## How to run Twelf and verify the proof

It can be a little tricky to get Twelf running on a modern machine, as its compiled binaries are made for older machines (its last official release is from 2011), and its online version [Twelf Live](http://twelf.org/wiki/Twelf_Live) seems to have been down for quite some time. However, building from source isn't too bad; for me, it was quick and error-free using the [SMLNJ](http://www.smlnj.org/) compiler.

Once it's installed, navigate to this directory with the `sources.cfg` and `.elf` files, run `twelf-server` from where you installed Twelf, and enter the command `make` to run the checker. The output from `twelf-server` regarding the verification has been recorded in `output.log`.
