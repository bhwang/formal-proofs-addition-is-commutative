# add_comm in Coq

The result that addition is commutative for the natural numbers can be found in any number of Coq tutorials and standard libraries, such as [Coq.Numbers.NatIntNZAdd](https://coq.inria.fr/library/Coq.Numbers.NatInt.NZAdd.html). 

* The quickest way to prove it is to use powerful "magic" tactics, namely, `simpl` and `auto` to obtain a proof, which can be seen in `add_comm_magic_tactics.v`.

* We can also prove the result using tactics that are less heavy-handed, which can be found in `add_comm_tactics_no_imports.v`.

It is also possible to use proof terms explicitly, as in [Coq's Wikipedia entry](https://en.wikipedia.org/wiki/Coq):

```coq
plus_comm =
fun n m : nat =>
nat_ind (fun n0 : nat => n0 + m = m + n0)
  (plus_n_0 m)
  (fun (y : nat) (H : y + m = m + y) =>
   eq_ind (S (m + y))
     (fun n0 : nat => S (y + m) = n0)
     (f_equal S H)
     (m + S y)
     (plus_n_Sm m y)) n
     : forall n m : nat, n + m = m + n
```

It is uncommon to work with explicit proof terms in Coq, and if you're using Coq along well-treaded paths often just applying known tactics will suffice for proofs. However, new formalizations of mathematics in Coq often necessitate the development of novel area-specific tactics, for which knowledge of `Ltac` (Coq's separate "tactics language") is essential and for which having a mental model of what is happen at the level of proof terms is helpful.
