(* A simple proof of commutativity using "magic" tactics like *)
Lemma plus_comm : forall n m : nat, n + m = m + n.
Proof.
induction m.  
- simpl.
  auto.
- simpl.
  rewrite <- IHm.
  auto.
Qed.
