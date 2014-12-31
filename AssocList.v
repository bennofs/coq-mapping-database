Require Import NArith.
Require Import List.

(** An association list is a mapping between keys, which are natural numbers, and
    values of an arbitrary type. There is at most one value per key. *)
Definition assoc_list (T:Type) : Type := list (N * T).

Section InDomain.

  Variable T : Type.

  Definition in_domain (k:N) (l:assoc_list T) : Prop := exists v, In (k,v) l.
  Global Arguments in_domain : default implicits.

  Theorem In_in_domain :
    forall (l:assoc_list T) (k:N) (v:T), In (k,v) l -> in_domain k l.
  Proof. Hint Unfold in_domain. eauto. Qed.

  Theorem not_in_domain_In :
    forall (l:assoc_list T) (k:N) (v:T), ~in_domain k l -> ~In (k,v) l.
  Proof. Hint Unfold in_domain not. eauto. Qed.

  Lemma in_domain_inv :
    forall (k:N) (k':N) (v:T) (l:assoc_list T),
      in_domain k ((k',v) :: l) <-> k' = k \/ in_domain k l.
  Proof.
    Hint Resolve in_cons in_eq.
    unfold in_domain. intros. split.
    - destruct 1 as [v' in_l]. apply in_inv in in_l. destruct in_l.
      + inversion H. subst. tauto.
      + eauto.
    - destruct 1 as [ke | [v' in_l]]; subst; eauto.
  Qed.

  Lemma in_domain_inv_tail :
    forall (k k':N) (v:T) (l:assoc_list T),
      k' <> k -> (in_domain k ((k',v) :: l) <-> in_domain k l).
  Proof.
    intros k k' v l ineq. split.
    - intros H. apply in_domain_inv in H. destruct H; [contradiction | assumption].
    - intros. apply in_domain_inv. auto.
  Qed.

  Lemma not_in_domain_inv :
    forall (k k':N) (v:T) (l:assoc_list T),
      ~in_domain k ((k',v) :: l) -> k <> k' /\ ~in_domain k l.
  Proof.
    unfold not. unfold in_domain. split; destruct 1; eauto.
  Qed.

  Theorem not_in_domain_cons :
    forall (l:assoc_list T) (k k':N) (v:T),
      k <> k' -> ~in_domain k l -> ~in_domain k ((k',v) :: l).
  Proof.
    unfold in_domain. intros l k k' v ineq not_in_l.
    destruct 1 as [? [E|E]]; [inversion E|]; eauto.
  Qed.

  Lemma in_domain_app_or :
    forall (k:N) (l1 l2:assoc_list T),
      in_domain k (l1 ++ l2) <-> in_domain k l1 \/ in_domain k l2.
  Proof.
    Hint Resolve in_or_app.
    unfold in_domain.
    intros k l1 l2. split.
    - destruct 1 as [v in_l12]. apply in_app_or in in_l12. intuition eauto.
    - destruct 1 as [in_l|in_l]; destruct in_l as [v in_l]; eauto.
  Qed.

  Lemma not_in_domain_nil :
    forall (k:N), ~in_domain k nil.
  Proof.
    intros. unfold in_domain. destruct 1. auto.
  Qed.

  Theorem in_domain_dec : forall (l:assoc_list T) (k:N), in_domain k l + ~in_domain k l.
  Proof.
    Hint Resolve not_in_domain_nil not_in_domain_cons in_cons.
    Hint Unfold in_domain.
    intros l k. induction l as [|[k' v] t IH].
    - eauto.
    - destruct IH as [H | not_in_t].
      + left. destruct H. eauto.
      + destruct (N.eq_dec k' k); subst; eauto.
  Qed.

End InDomain.

Section Disjoint.

  Variable T : Type.

  Definition al_disjoint (l1 l2:assoc_list T) : Prop :=
    forall k, in_domain k l1 -> ~in_domain k l2.
  Global Arguments al_disjoint : default implicits.

  Lemma al_disjoint_nil_l :
    forall (l1:assoc_list T), al_disjoint nil l1.
  Proof.
    intros l1 k. unfold in_domain. destruct 1 as [v in_nil]. contradiction.
  Qed.

  Lemma al_disjoint_symmetry :
    forall (l1 l2:assoc_list T), al_disjoint l1 l2 -> al_disjoint l2 l1.
  Proof. unfold al_disjoint. eauto. Qed.

  Lemma al_disjoint_cons_not_elem :
    forall (l1 l2:assoc_list T) (k:N) (v:T),
      ~(in_domain k l2) /\ al_disjoint l1 l2 <-> al_disjoint ((k,v) :: l1) l2.
  Proof.
    Hint Resolve in_eq.
    Hint Resolve <- in_domain_inv.
    intros l1 l2 k v. split.
    - unfold al_disjoint. destruct 1. intro. rewrite in_domain_inv.
      destruct 1; subst; eauto.
    - unfold al_disjoint. intros H. split; intros; try (apply H); eauto.
  Qed.

End Disjoint.

Section Invariant.

  Variable T : Type.

  Inductive al_invariant : assoc_list T -> Prop :=
    | al_invariant_nil  : al_invariant nil
    | al_invariant_cons :
        forall (k:N) (v:T) (t:assoc_list T),
          ~in_domain k t -> al_invariant t -> al_invariant ((k,v) :: t).
  Global Arguments al_invariant : default implicits.

  Lemma al_invariant_disjoint :
    forall (l1 l2:assoc_list T), al_invariant (l1 ++ l2) -> al_disjoint l1 l2.
  Proof.
    intros l1 l2 H. induction l1 as [|h t IH].
    - apply al_disjoint_nil_l.
    - destruct h as [k v]. apply al_disjoint_cons_not_elem. split.
      + inversion H as [|k' v' t' not_in_tl2 inv_tl2]. subst.
        rewrite in_domain_app_or in not_in_tl2. auto.
      + apply IH. inversion H. assumption.
  Qed.

  Lemma al_invariant_app_split :
    forall (l1 l2:assoc_list T),
      al_invariant (l1 ++ l2) -> al_invariant l1 /\ al_invariant l2.
  Proof.
    Hint Constructors al_invariant.
    Hint Resolve <- in_domain_app_or.
    intros l1 l2 H. induction l1 as [|h t IH].
    - auto.
    - destruct h as [k v]. inversion H as [|k' v' t' not_in_tl2 inv_tl2]; subst. split;
        try (apply al_invariant_cons);
        intuition eauto.
  Qed.

  Lemma al_invariant_join_app :
    forall (l1 l2:assoc_list T),
      al_invariant l1 -> al_invariant l2 -> al_disjoint l1 l2 -> al_invariant (l1 ++ l2).
  Proof.
    intros l1 l2 inv_l1 inv_l2 dis. induction l1 as [|h t IH].
    - assumption.
    - destruct h as [k v]. simpl.
      inversion inv_l1. subst.
      apply <- al_disjoint_cons_not_elem in dis.
      apply al_invariant_cons.
      + rewrite in_domain_app_or. intuition auto.
      + apply IH; tauto.
  Qed.

  Lemma al_invariant_app_comm :
    forall (l1 l2:assoc_list T), al_invariant (l1 ++ l2) -> al_invariant (l2 ++ l1).
  Proof.
    intros l1 l2 H. apply al_invariant_join_app.
    - apply al_invariant_app_split in H. apply H.
    - apply al_invariant_app_split in H. apply H.
    - apply al_invariant_disjoint in H. apply al_disjoint_symmetry. apply H.
  Qed.

  Lemma al_invariant_in_eq :
    forall (l:assoc_list T) (k:N) (v v':T),
      al_invariant l -> In (k,v) l -> In (k,v') l -> v = v'.
  Proof.
    Hint Resolve in_inv In_in_domain.
    Hint Unfold in_domain not.
    intros l k v v' inv_l v_in v'_in. induction l as [|[k' v''] t IH].
    - destruct v_in.
    - inversion inv_l. subst. case v_in.
      + inversion 1. subst. case v'_in.
        * inversion 1. auto.
        * intros. exfalso. eauto.
      + intros. case v'_in.
        * inversion 1. subst. exfalso. eauto.
        * auto.
  Qed.

  Lemma in_eq_inv :
    forall (l:assoc_list T) (k:N) (v v':T),
      ~in_domain k l -> In (k,v) ((k,v') :: l) -> v = v'.
  Proof.
    intros l k v v' H. destruct 1 as [E|E]; [inversion E|exfalso]; eauto.
  Qed.

  Lemma in_cons_inv :
    forall (l:assoc_list T) (k k':N) (v v':T),
      k <> k' -> In (k',v') ((k,v) :: l) -> In (k',v') l.
  Proof.
    intros l k k' v v' ineq. destruct 1 as [E|E]; [inversion E; exfalso|]; eauto.
  Qed.

End Invariant.

Section Contains.

  Variable T : Type.

  Definition contains (k:N) (P:T -> Prop) (l:assoc_list T) : Prop :=
    exists v, In (k,v) l /\ P v.
  Global Arguments contains : default implicits.

  Theorem In_contains :
    forall (k:N) (P:T -> Prop) (v:T) (l:assoc_list T),
      In (k,v) l -> P v -> contains k P l.
  Proof. intros. unfold contains. eauto. Qed.

End Contains.

Section Empty.

  Definition al_empty {T:Type} : assoc_list T := nil.

  Theorem empty_invariant : forall (T:Type), al_invariant (@al_empty T).
  Proof. constructor. Qed.

End Empty.

Section Alter.

  Variable T : Type.

  Let alter_tail (k:N) (v:option T) (t:assoc_list T) :=
    match v with
      | None    => t
      | Some v' => (k,v') :: t
    end.

  Fixpoint al_alter (f:option T -> option T) (k:N) (l:assoc_list T) : assoc_list T :=
    match l with
      | nil    => alter_tail k (f None) nil
      | h :: t =>
        let (k',v) := h in
        if N.eq_dec k' k
        then alter_tail k (f (Some v)) t
        else h :: al_alter f k t
    end.
  Global Arguments al_alter : default implicits.

  Theorem in_alter_tail :
    forall (k k':N) (v:T) (x:option T) (l:assoc_list T),
      In (k,v) l -> In (k,v) (alter_tail k' x l).
  Proof.
    Hint Resolve in_eq in_cons.
    intros k k' v x l. unfold alter_tail. destruct x; auto.
  Qed.

  Theorem in_alter_tail_inv :
    forall (k k':N) (v:T) (x:option T) (l:assoc_list T),
      k <> k' -> In (k,v) (alter_tail k' x l) -> In (k,v) l.
  Proof.
    intros k k' v x l ineq. destruct x.
    - simpl. destruct 1 as [H|H].
      + inversion H. subst. exfalso. auto.
      + assumption.
    - trivial.
  Qed.

  Theorem in_tail_inv :
    forall (k k':N) (v v':T) (l:assoc_list T),
      k <> k' -> In (k,v) ((k',v') :: l) -> In (k,v) l.
  Proof.
    intros k k' v v' l ineq.
    destruct 1 as [H|H].
    - inversion H. subst. exfalso. auto.
    - auto.
  Qed.

  Theorem alter_preserve_other :
    forall (l:assoc_list T) (k1 k2:N) (f:option T -> option T) (v:T),
      k1 <> k2 -> (In (k1,v) l <-> In (k1,v) (al_alter f k2 l)).
  Proof.
    Hint Resolve in_cons in_eq in_tail_inv in_alter_tail.
    intros l k1 k2 f v ineq.
    induction l as [|[k' v'] t IH].
    - intros. split.
      + contradiction.
      + simpl. destruct (f None).
        * destruct 1 as [H|H]; inversion H; auto.
        * destruct 1.
    - split.
      + intros H. apply in_inv in H. apply proj1 in IH.
        simpl. destruct (N.eq_dec k' k2).
        * subst. eauto.
        * simpl. destruct H; eauto.
      + simpl. apply proj2 in IH. intros H. destruct (N.eq_dec k' k2).
        * simpl in H. subst. apply in_alter_tail_inv in H; auto.
        * simpl. destruct H; eauto.
  Qed.

  Theorem alter_invariant :
    forall (l:assoc_list T) (k:N) (f:option T -> option T),
      al_invariant l -> al_invariant (al_alter f k l).
  Proof.
    Hint Constructors al_invariant.
    Hint Resolve al_invariant_cons not_in_domain_nil.
    Hint Resolve <- alter_preserve_other.
    Hint Unfold in_domain.
    intros l k f inv_l.
    induction l as [|[k' v'] t IH].
    - simpl. destruct (f None); simpl; auto.
    - simpl. inversion inv_l. destruct (N.eq_dec k' k).
      + subst. destruct (f (Some v')); simpl; auto.
      + subst. apply al_invariant_cons.
        * destruct 1 as [v H]. eauto.
        * eauto.
  Qed.

End Alter.

Section Remove.

  Variable T : Type.

  Definition al_remove : N -> assoc_list T -> assoc_list T := al_alter (fun _ => None).
  Global Arguments al_remove : default implicits.

  Theorem remove_empty : forall k, al_remove k al_empty = al_empty.
  Proof. intros. reflexivity. Qed.

  Theorem remove_not_in :
    forall (l:assoc_list T) (k:N), al_invariant l -> ~in_domain k (al_remove k l).
  Proof.
    Hint Resolve -> in_domain_inv_tail.
    intros l k inv_l. induction l as [|[k' v'] t IH].
    - destruct 1. auto.
    - unfold al_remove. simpl. inversion inv_l. destruct (N.eq_dec k' k).
      + subst. assumption.
      + subst. intros H. apply IH; eauto.
  Qed.

  Theorem remove_subset :
    forall (l:assoc_list T) (k kr:N) (v:T),
      al_invariant l -> In (k,v) (al_remove kr l) -> In (k,v) l.
  Proof.
    Hint Resolve <- alter_preserve_other.
    Hint Resolve remove_not_in In_in_domain.
    intros l k kr v H. destruct (N.eq_dec k kr).
    - intros. exfalso. subst. eapply remove_not_in; eauto.
    - eauto.
  Qed.

  Theorem remove_invariant :
    forall (l:assoc_list T) (k:N), al_invariant l -> al_invariant (al_remove k l).
  Proof.
    Hint Resolve alter_invariant. unfold al_remove. eauto.
  Qed.

  Theorem remove_preserve_other :
    forall (l:assoc_list T) (k k':N) (v:T),
      k <> k' -> (In (k,v) l <-> In (k,v) (al_remove k' l)).
  Proof.
    Hint Resolve alter_preserve_other.
    intros. unfold al_remove. eauto.
  Qed.


End Remove.

Section Insert.

  Variable T : Type.

  Definition al_insert (k:N) (v:T): assoc_list T -> assoc_list T :=
    al_alter (fun _ => Some v) k.
  Global Arguments al_insert : default implicits.

  Theorem insert_In :
    forall (l:assoc_list T) (k:N) (v:T),
      In (k,v) (al_insert k v l).
  Proof.
    Hint Resolve in_eq in_cons.
    intros l k v. unfold al_insert. induction l as [|[k' v'] t IH].
    - simpl. eauto.
    - simpl. destruct (N.eq_dec k' k); eauto.
  Qed.

  Theorem insert_in_domain :
    forall (l:assoc_list T) (k:N) (v:T),
      in_domain k (al_insert k v l).
  Proof.
    Hint Resolve In_in_domain insert_In.
    eauto.
  Qed.

  Theorem insert_domain_superset :
    forall (l:assoc_list T) (k ki:N) (vi:T),
      in_domain k l -> in_domain k (al_insert ki vi l).
  Proof.
    Hint Resolve In_in_domain insert_in_domain.
    Hint Resolve -> alter_preserve_other.
    intros l k ki vi in_l. destruct (N.eq_dec k ki).
    - subst. eauto.
    - destruct in_l as [v H]. unfold al_insert. eauto.
  Qed.

  Theorem insert_invariant :
    forall (l:assoc_list T) (k:N) (v:T),
      al_invariant l -> al_invariant (al_insert k v l).
  Proof. Hint Resolve alter_invariant. unfold al_insert. auto. Qed.

  Theorem insert_preserve_other :
    forall (l:assoc_list T) (k k':N) (v v':T),
      k <> k' -> (In (k,v) l <-> In (k,v) (al_insert k' v' l)).
  Proof. Hint Resolve alter_preserve_other. unfold al_insert. auto. Qed.

End Insert.

Section Assoc.

  Variable T : Type.

  Fixpoint al_assoc (k:N) (l:assoc_list T) : option T :=
    match l with
      | nil    => None
      | h :: t => if N.eq_dec (fst h) k then Some (snd h) else al_assoc k t
    end.
  Global Arguments al_assoc : default implicits.

  Theorem assoc_In :
    forall (l:assoc_list T) (k:N) (v:T),
      al_assoc k l = Some v -> In (k,v) l.
  Proof.
    Hint Resolve in_eq in_cons.
    intros l k v.
    induction l as [|[k' v'] t IH].
    + discriminate.
    + simpl. destruct (N.eq_dec k' k); inversion 1; subst; auto.
  Qed.

  Theorem In_assoc :
    forall (l:assoc_list T) (k:N) (v:T),
      al_invariant l -> In (k,v) l -> al_assoc k l = Some v.
  Proof.
    Hint Resolve In_in_domain.
    intros l k v inv_l. induction l as [|[k' v'] t IH].
    - contradiction.
    - inversion inv_l. subst. simpl. destruct (N.eq_dec k' k).
      + destruct 1 as [E | in_t]; [inversion E|exfalso]; subst; eauto.
      + destruct 1 as [E | in_t]; [inversion E;exfalso|]; subst; eauto.
  Qed.

  Theorem assoc_in_domain :
    forall (l:assoc_list T) (k:N),
      ((exists v, al_assoc k l = Some v) <-> in_domain k l).
  Proof.
    Hint Resolve In_in_domain assoc_In in_eq in_cons.
    intros l k. split.
    - destruct 1; eauto.
    - intros in_l. induction l as [|[k' v] t IH].
      + destruct in_l. contradiction.
      + apply in_domain_inv in in_l. simpl. destruct (N.eq_dec k' k); intuition eauto.
  Qed.

  Theorem assoc_in_1 :
    forall (l:assoc_list T) (k:N) (v:T),
      al_assoc k l = Some v -> in_domain k l.
  Proof. Hint Resolve -> assoc_in_domain. eauto. Qed.

  Theorem assoc_not_in :
    forall (l:assoc_list T) (k:N),
      (al_assoc k l = None <-> ~in_domain k l).
  Proof.
    Hint Resolve assoc_In.
    intros. split.
    - destruct (al_assoc k l) eqn:A.
      + discriminate 1.
      + intros. eauto. rewrite <- assoc_in_domain.
        rewrite A. destruct 1. discriminate.
    - destruct (al_assoc k l) eqn:A.
      + intros. exfalso. eauto.
      + reflexivity.
  Qed.

End Assoc.

Section InsertMerge.

  Variable T : Type.

  Let alter_fun (f:T -> T) (def:T) (x:option T) : option T :=
    Some (match x with | None => def | Some v => f v end).

  Definition al_insert_merge (k:N) (f:T -> T) (def:T) : assoc_list T -> assoc_list T :=
    al_alter (alter_fun f def) k.
  Global Arguments al_insert_merge : default implicits.

  Theorem insert_merge_inserts :
    forall (l:assoc_list T) (k:N) (f:T -> T) (def:T),
      in_domain k (al_insert_merge k f def l).
  Proof.
    Hint Resolve <- in_domain_inv.
    intros l k f def. unfold al_insert_merge. induction l as [|[k' v'] t IH].
    - simpl. auto.
    - simpl. destruct (N.eq_dec k' k); auto.
  Qed.

  Theorem insert_merge_superset :
    forall (l:assoc_list T) (k k':N) (f:T -> T) (def:T),
      in_domain k l -> in_domain k (al_insert_merge k' f def l).
  Proof.
    Hint Resolve insert_merge_inserts.
    Hint Resolve -> alter_preserve_other.
    Hint Unfold in_domain.
    intros l k k' f def H.
    destruct (N.eq_dec k k').
    - subst. eauto.
    - unfold al_insert_merge. destruct H. eauto.
  Qed.

  Theorem insert_merge_preserve_other :
    forall (l:assoc_list T) (k k':N) (v:T) (f:T -> T) (def:T),
      k <> k' -> (In (k,v) l <-> In (k,v) (al_insert_merge k' f def l)).
  Proof.
    Hint Resolve alter_preserve_other.
    unfold al_insert_merge. auto.
  Qed.

  Theorem In_insert_merge_inv :
    forall (l:assoc_list T) (k:N) (v def:T) (f:T -> T),
      al_invariant l ->
      In (k,v) (al_insert_merge k f def l) ->
      (~in_domain k l /\ v = def) \/ (contains k (fun x => f x = v) l).
  Proof.
    Hint Resolve not_in_domain_nil in_eq in_cons In_in_domain not_in_domain_cons.
    Hint Resolve In_contains in_cons_inv.
    intros l k v def f inv_l H. induction l as [|[k' v'] t IH].
    - destruct H as [E|E]; inversion E; subst; eauto.
    - unfold al_insert_merge in H. simpl in H. inversion inv_l. subst.
      destruct (N.eq_dec k' k).
      + apply in_eq_inv in H; subst; eauto.
      + destruct IH as [[? ?]|[? [? ?]]]; eauto.
  Qed.

  Theorem insert_merge_invariant :
    forall (l:assoc_list T) (k:N) (f:T -> T) (def:T),
      al_invariant l -> al_invariant (al_insert_merge k f def l).
  Proof. Hint Resolve alter_invariant. unfold al_insert_merge. auto. Qed.

  Theorem insert_merge_contains :
    forall (l:assoc_list T) (k:N) (f:T -> T) (def:T) (P:T -> Prop),
      (~in_domain k l -> P def) ->
      (forall v, In (k,v) l -> P (f v)) -> contains k P (al_insert_merge k f def l).
  Proof.
    Hint Resolve in_eq in_cons In_contains not_in_domain_nil.
    Hint Resolve -> in_domain_inv_tail.
    intros l k f def P Pdef Pf.
    unfold al_insert_merge. induction l as [|[k' v'] t IH].
    - simpl. eauto.
    - simpl. destruct (N.eq_dec k' k).
      + subst. eauto.
      + destruct IH as [v [H Q]]; eauto.
  Qed.

End InsertMerge.

Section Merge.

  Variable T : Type.

  Fixpoint al_merge (f:T -> T -> T) (l1:assoc_list T) (l2:assoc_list T) : assoc_list T :=
    match l1 with
      | nil            => l2
      | (k,v1) :: l1_t => al_insert_merge k (f v1) v1 (al_merge f l1_t l2)
    end.
  Global Arguments al_merge : default implicits.

  Definition al_union : assoc_list T -> assoc_list T -> assoc_list T :=
    al_merge (fun _ b => b).
  Global Arguments al_union : default implicits.

  Theorem merge_no_new_elements :
    forall (l1 l2:assoc_list T) (f:T -> T -> T) (k:N),
      ~in_domain k l1 -> ~in_domain k l2 -> ~in_domain k (al_merge f l1 l2).
  Proof.
    Hint Unfold in_domain.
    Hint Resolve <- insert_merge_preserve_other in_domain_inv.
    intros l1 l2 f k H.
    induction l1 as [|[k' v] t IH].
    - intros. assumption.
    - simpl. intros not_in_l2.
      intros R. unfold not in H. destruct R.
      destruct (N.eq_dec k k').
      + subst. eauto.
      + apply IH; eauto.
  Qed.

  Theorem merge_invariant :
    forall (l1 l2:assoc_list T) (f:T -> T -> T),
      al_invariant l1 -> al_invariant l2 -> al_invariant (al_merge f l1 l2).
  Proof.
    Hint Resolve insert_merge_invariant.
    intros l1 l2 f inv_l1 inv_l2.
    induction l1 as [|[k v] t IH].
    - assumption.
    - inversion inv_l1. simpl. eauto.
  Qed.

  Theorem merge_superset_first :
    forall (l1 l2:assoc_list T) (f:T -> T -> T) (k:N),
      in_domain k l1 -> in_domain k (al_merge f l1 l2).
  Proof.
    Hint Resolve insert_merge_superset insert_merge_inserts.
    intros l1 l2 f k in_l1.
    - induction l1 as [|[k' v] t IH].
      + simpl. exfalso. eapply not_in_domain_nil. eauto.
      + simpl. apply in_domain_inv in in_l1. destruct in_l1; subst; eauto.
  Qed.

  Theorem merge_superset_second :
    forall (l1 l2:assoc_list T) (f:T -> T -> T) (k:N),
      in_domain k l2 -> in_domain k (al_merge f l1 l2).
  Proof.
    Hint Resolve insert_merge_superset insert_merge_inserts.
    intros l1 l2 f k in_l2.
    - induction l1 as [|[k' v] t IH].
      + trivial.
      + simpl. eauto.
  Qed.

End Merge.

Section Filter.

  Variable T : Type.

  Definition al_filter (f:N -> T -> bool) : assoc_list T -> assoc_list T :=
    filter (fun x => match x with (k,v) => f k v end).
  Global Arguments al_filter : default implicits.

  Theorem filter_subset :
    forall (l:assoc_list T) (k:N) (v:T) (f:N -> T -> bool),
      In (k,v) (al_filter f l) -> In (k,v) l.
  Proof.
    intros l k P f. induction l as [|[k' v] t IH].
    - auto.
    - simpl. destruct (f k' v) eqn:fkv.
      + simpl. destruct 1 as [E|in_t]; [inversion E|]; subst; eauto.
      + eauto.
  Qed.

  Theorem filter_predicate_true :
    forall (l:assoc_list T) (k:N) (v:T) (f:N -> T -> bool),
      In (k,v) (al_filter f l) -> f k v = true.
  Proof.
    unfold al_filter. intros l k v f. rewrite filter_In. tauto.
  Qed.

  Theorem filter_invariant :
    forall (l:assoc_list T) (f:N -> T -> bool),
      al_invariant l -> al_invariant (al_filter f l).
  Proof.
    Hint Resolve filter_subset al_invariant_cons.
    Hint Resolve <- in_domain_inv.
    Hint Unfold in_domain.
    intros l f H. induction l as [|[k v] t IH].
    - auto.
    - simpl. inversion H as [|k' v' t' not_in_t inv_t]. subst. destruct (f k v) eqn:fkv.
      + apply al_invariant_cons; try (destruct 1); eauto.
      + auto.
  Qed.

  Theorem al_filter_In :
    forall (f:N -> T -> bool) (l:assoc_list T) (k:N) (v:T),
      (f k v = true /\ In (k,v) l) <-> In (k,v) (al_filter f l).
  Proof.
    intros. unfold al_filter. rewrite filter_In. tauto.
  Qed.

End Filter.

Section RevAssoc.

  Variable T : Type.

  Definition al_rev_assoc (p:T -> bool) (l:assoc_list T) : list N :=
    map (@fst N T) (al_filter (fun _ => p) l).
  Global Arguments al_rev_assoc : default implicits.

  Let map_fst_In :
    forall (k:N) (l:assoc_list T), In k (map (@fst N T) l) -> exists v, In (k,v) l.
  Proof.
    intros k l H. induction l as [|[k' v'] t IH].
    - contradiction.
    - simpl. destruct H.
      + subst. eauto.
      + destruct IH; eauto.
  Qed.

  Theorem rev_assoc_assoc :
    forall (f:T -> bool) (l:assoc_list T) (k:N),
      In k (al_rev_assoc f l) -> exists v, In (k,v) l /\ f v = true.
  Proof.
    Hint Resolve filter_subset.
    unfold al_rev_assoc. intros f l k H.
    apply map_fst_In in H. destruct H as [v H]. exists v. split.
    + eauto.
    + apply filter_predicate_true in H. eauto.
  Qed.

  Theorem assoc_rev_assoc :
    forall (f:T -> bool) (l:assoc_list T) (k:N) (v:T),
      al_invariant l ->
      In (k,v) l -> f v = true -> In k (al_rev_assoc f l).
  Proof.
    Hint Resolve in_eq in_cons.
    intros f l k v inv_l. induction l as [|[k' v'] t IH].
    - contradiction.
    - simpl. inversion inv_l. subst. destruct 1 as [eq|in_t].
      + inversion eq. subst. intros fvt. unfold al_rev_assoc. simpl. rewrite fvt. simpl.
        eauto.
      + unfold al_rev_assoc. simpl. destruct (f v') eqn:fv'; simpl; eauto.
  Qed.

End RevAssoc.

Section Update.

  Variable T : Type.

  Let alter_fun (f:T -> T) (x:option T) : option T :=
    match x with | None => None | Some v => Some (f v) end.

  Definition al_update (k:N) (f:T -> T) : assoc_list T -> assoc_list T :=
    al_alter (alter_fun f) k.
  Global Arguments al_update : default implicits.

  Theorem update_invariant :
    forall (l:assoc_list T) (k:N) (f:T -> T),
      al_invariant l -> al_invariant (al_update k f l).
  Proof. Hint Resolve alter_invariant. unfold al_update. auto. Qed.

  Theorem update_updates :
    forall (l:assoc_list T) (k:N) (v:T) (f:T -> T),
      al_invariant l -> (In (k,v) l -> In (k,f v) (al_update k f l)).
  Proof.
    Hint Resolve in_eq in_cons In_in_domain.
    intros l k v f inv_l.
    induction l as [|[k'' v''] t IH].
    - contradiction.
    - unfold al_update. simpl. inversion inv_l. destruct (N.eq_dec k'' k).
      + destruct 1 as [E|E]; [inversion E|exfalso]; subst; eauto.
      + simpl. destruct 1 as [E|E]; [inversion E;exfalso|]; subst; eauto.
  Qed.

  Theorem update_preserve_at_k :
    forall (l:assoc_list T) (k:N) (f:T -> T),
      in_domain k l <-> in_domain k (al_update k f l).
  Proof.
    intros l k f. induction l as [|[k' v'] t IH].
    - split; destruct 1; contradiction.
    - unfold al_update. simpl. destruct (N.eq_dec k' k).
      + subst. split; eauto.
      + rewrite_all in_domain_inv_tail; eauto.
  Qed.

  Theorem update_preserve_domain :
    forall (l:assoc_list T) (k k':N) (f:T -> T),
      in_domain k l <-> in_domain k (al_update k' f l).
  Proof.
    Hint Resolve update_preserve_at_k.
    Hint Resolve -> alter_preserve_other.
    Hint Resolve <- alter_preserve_other.
    intros l k k' f. destruct (N.eq_dec k k').
    - subst. eauto.
    - unfold al_update; split; destruct 1; eauto.
  Qed.

  Theorem update_preserve_other :
    forall (l:assoc_list T) (f:T -> T) (k k':N) (v:T),
      k <> k' -> (In (k,v) l <-> In (k,v) (al_update k' f l)).
  Proof.
    Hint Resolve alter_preserve_other.
    intros. unfold al_update. eauto.
  Qed.

  Theorem In_update_inv :
    forall (l:assoc_list T) (f:T -> T) (k:N) (v:T),
      al_invariant l -> (In (k,v) (al_update k f l) <-> exists x, In (k,x) l /\ f x = v).
  Proof.
    Hint Resolve In_in_domain update_updates in_cons_inv.
    intros l f k v inv_l. split.
    - unfold al_update. induction l as [|[k' v'] t IH].
      + simpl. contradiction.
      + simpl. inversion inv_l. subst. intros H. destruct (N.eq_dec k' k).
        * apply in_eq_inv in H; subst; eauto.
        * destruct IH as [? [? ?]]; eauto.
    - destruct 1 as [? [? ?]]. subst. auto.
  Qed.

End Update.

Section Map.

  Variable A B : Type.

  Let map_fun (f:N -> A -> B) (x:N * A) : (N * B) :=
    match x with (k,v) => (k, f k v) end.

  Definition al_map (f:N -> A -> B) : assoc_list A -> assoc_list B :=
    map (map_fun f).
  Global Arguments al_map : default implicits.

  Theorem map_updates_all :
    forall (l:assoc_list A) (f:N -> A -> B) (k:N) (v:A),
      In (k,v) l -> In (k,f k v) (al_map f l).
  Proof.
    intros l f k v. unfold al_map.
    replace (k, f k v) with (map_fun f (k,v)) by reflexivity.
    apply in_map.
  Qed.

  Theorem map_preserve_domain :
    forall (l:assoc_list A) (f:N -> A -> B) (k:N),
      in_domain k l <-> in_domain k (al_map f l).
  Proof.
    Hint Resolve In_in_domain map_updates_all.
    split.
    - destruct 1. eauto.
    - unfold al_map. intros H. destruct H as [v H]. apply in_map_iff in H.
      destruct H as [[k' v'] [H Q]]. inversion H. subst. eauto.
  Qed.

  Theorem map_invariant :
    forall (l:assoc_list A) (f:N -> A -> B),
      al_invariant l -> al_invariant (al_map f l).
  Proof.
    Hint Constructors al_invariant.
    Hint Resolve al_invariant_cons.
    Hint Resolve <- map_preserve_domain.
    intros l f inv_l. induction l as [|[k v] t IH].
    - simpl. auto.
    - simpl. inversion inv_l. subst. apply al_invariant_cons; eauto.
  Qed.

  Theorem In_map_iff :
    forall (f:N -> A -> B) (l:assoc_list A) (b:B) (k:N),
      In (k, b) (al_map f l) <-> exists a : A, b = f k a /\ In (k,a) l.
  Proof.
    intros f l b k. unfold al_map. rewrite in_map_iff. split.
    - destruct 1 as [x [E H]]. destruct x. inversion E. subst. eauto.
    - destruct 1 as [a [E H]]. exists (k,a). subst. auto.
  Qed.

End Map.
