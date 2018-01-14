Theorem plus_1 :
  forall (n m:nat), n + S m = S (n + m).
Proof. intros. induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_comm :
  forall (n m:nat), n + m = m + n.
Proof.
  intros n m. 
  induction n as [|n IHn].
  - simpl. induction m; simpl; auto.
  - simpl. rewrite plus_1.  rewrite IHn. reflexivity.
Qed.