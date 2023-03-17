Lemma add_zero: forall n: nat, n = n + 0.
Proof.
induction n.
- simpl.
  reflexivity.
- simpl.
  f_equal.
  assumption.
Qed.

Lemma add_S : forall m n: nat, S (m + n) = m + (S n).
Proof.
intros m n.
induction m.
- simpl.
  reflexivity.
- simpl.
  f_equal.
  assumption.
Qed.

Lemma add_comm : forall m n: nat, m + n = n + m.
Proof.
intros m n.
induction m.
- simpl.
  apply add_zero.
- simpl.
  rewrite IHm.
  apply add_S.
Qed.
  
