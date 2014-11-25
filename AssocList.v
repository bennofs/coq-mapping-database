Require Import NArith.
Require Import List.

Section AssocListDef.

Variable T : Type.

(** An association list is a mapping between keys, which are natural numbers, and
    values of an arbitrary type. There is at most one value per key. *)
Definition assoc_list : Type := list (N * T).

Set Contextual Implicit.
Definition empty : assoc_list := nil.
Global Arguments empty : default implicits.

Fixpoint remove (k:N) (l:assoc_list) : assoc_list :=
  match l with
    | nil    => nil
    | h :: t => let (k',v) := h in if N.eq_dec k' k then t else h :: remove k t
  end.
Global Arguments remove : default implicits.

Definition insert (k:N) (v:T) (l:assoc_list) : assoc_list :=
  (k,v) :: remove k l.
Global Arguments insert : default implicits.

Fixpoint assoc (k:N) (l:assoc_list) : option T :=
  match l with
    | nil    => None
    | h :: t => if N.eq_dec (fst h) k then Some (snd h) else assoc k t
  end.
Global Arguments assoc : default implicits.

Fixpoint rev_assoc (p:T -> bool) (l:assoc_list) : list N :=
  match l with
    | nil         => nil
    | (k,v) :: t => if p v then k :: rev_assoc p t else rev_assoc p t
  end.
Global Arguments rev_assoc : default implicits.

Fixpoint merge (f:T -> T -> T) (l1:assoc_list) (l2:assoc_list) : assoc_list :=
  match l1 with
    | nil        => l2
    | (k,v1) :: l1_t =>
      match assoc k l2 with
        | None    => (k,v1) :: merge f l1_t l2
        | Some v2 => (k,f v1 v2) :: merge f l1_t (remove k l2)
      end
  end.
Global Arguments merge : default implicits.

Definition union : assoc_list -> assoc_list -> assoc_list :=
  merge (fun _ b => b).
Global Arguments union : default implicits.

Fixpoint fold {X:Type} (f:N -> T -> X -> X) (x:X) (l:assoc_list) : X :=
  match l with
    | nil        => x
    | (k,v) :: t => f k v (fold f x t)
  end.
Global Arguments fold : default implicits.

End AssocListDef.


Section InvariantDef.

Variable T : Type.

Definition in_domain (k:N) (l:assoc_list T) : Prop :=
  exists v, In (k,v) l.

Lemma in_domain_inv :
  forall (k:N) (k':N) (v:T) (l:assoc_list T),
    in_domain k ((k',v) :: l) <-> k' = k \/ in_domain k l.
Proof.
  intros k k' v l. split.
  - intros H. unfold in_domain in H. destruct H as [v' k_in].
    apply in_inv in k_in. destruct k_in.
    + inversion H. subst. tauto.
    + unfold in_domain. eauto.
  - unfold in_domain. intros H. destruct H as [H|H].
    + subst. exists v. apply in_eq.
    + destruct H as [v' v'_in]. exists v'. apply in_cons. assumption.
Qed.

Lemma in_domain_app_or :
  forall (k:N) (l1 l2:assoc_list T),
    in_domain k (l1 ++ l2) <-> in_domain k l1 \/ in_domain k l2.
Proof.
  Hint Resolve in_or_app.
  Hint Unfold in_domain.
  intros k l1 l2. split.
  - destruct 1 as [v in_l12]. apply in_app_or in in_l12. intuition eauto.
  - destruct 1 as [in_l | in_l]; destruct in_l as [v in_l]; intuition eauto.
Qed.

Definition al_disjoint (l1 l2:assoc_list T) : Prop :=
  forall k, in_domain k l1 -> ~in_domain k l2.

Lemma al_disjoint_nil_l :
  forall (l1:assoc_list T), al_disjoint nil l1.
Proof.
  intros l1. unfold al_disjoint. unfold in_domain. intros k in_nil.
  destruct in_nil as [v v_in_nil]. inversion v_in_nil.
Qed.

Lemma al_disjoint_symmetry :
  forall (l1 l2:assoc_list T), al_disjoint l1 l2 -> al_disjoint l2 l1.
Proof.
  unfold al_disjoint. unfold in_domain. unfold not.
  intuition eauto.
Qed.

Lemma al_disjoint_app_split :
  forall (l1 l2 l3:assoc_list T),
    al_disjoint (l1 ++ l2) l3 -> al_disjoint l1 l3 /\ al_disjoint l2 l3.
Proof.
  Hint Resolve <- in_domain_app_or.
  unfold al_disjoint. intros l1 l2 l3 H. split; intros k P; apply H; eauto.
Qed.

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

Inductive al_invariant : assoc_list T -> Prop :=
  | al_invariant_nil  : al_invariant nil
  | al_invariant_cons :
      forall (k:N) (v:T) (t:assoc_list T),
        ~in_domain k t -> al_invariant t -> al_invariant ((k,v) :: t).

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
  Hint Resolve in_domain_app_or al_invariant_cons.
  intros l1 l2 H. induction l1 as [|h t IH].
  - auto.
  - destruct h as [k v]. inversion H as [|k' v' t' not_in_tl2 inv_tl2]; subst. split;
      try (apply al_invariant_cons);
      intuition auto.
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

End InvariantDef.


Section EmptyTheorems.

Variable T : Type.

Theorem assoc_empty : forall (k:N), assoc k (@empty T) = None.
Proof. reflexivity. Qed.

Theorem empty_invariant : al_invariant T empty.
Proof. constructor. Qed.

End EmptyTheorems.

Section RemoveTheorems.

Variable T : Type.

Theorem remove_subset :
  forall (l:assoc_list T) (k k':N), in_domain T k (remove k' l) -> in_domain T k l.
Proof.
  Hint Resolve <- in_domain_inv.
  intros l k k'. induction l as [|[k'' v] t IH].
  - destruct 1. contradiction.
  - simpl. destruct (N.eq_dec k'' k').
    + auto.
    + rewrite in_domain_inv. destruct 1; subst; auto.
Qed.

Theorem remove_invariant :
  forall (l:assoc_list T) (k:N), al_invariant T l -> al_invariant T (remove k l).
Proof.
  Hint Unfold not.
  Hint Resolve remove_subset al_invariant_cons.
  intros l k. induction l as [|[k' v] t IH].
  - trivial.
  - inversion 1. subst. simpl. destruct (N.eq_dec k' k); intuition eauto.
Qed.

Theorem remove_preserve_other :
  forall (l:assoc_list T) (k k':N),
    k' <> k -> in_domain T k l -> in_domain T k (remove k' l).
Proof.
  intros l k k' ineq. induction l as [|[k'' v] t IH].
  - destruct 1. contradiction.
  - simpl. rewrite in_domain_inv. destruct (N.eq_dec k'' k').
    + subst. tauto.
    + intuition auto.
Qed.

Theorem not_in_remove :
  forall (l:assoc_list T) (k:N), al_invariant T l -> ~in_domain T k (remove k l).
Proof.
  intros l k inv_l. induction l as [|[k' v] t IH].
  - destruct 1. contradiction.
  - simpl. inversion inv_l. subst. destruct (N.eq_dec k' k); subst.
    + auto.
    + rewrite in_domain_inv. tauto.
Qed.

End RemoveTheorems.

Section InsertTheorems.

Variable T : Type.

Theorem insert_superset :
  forall (l:assoc_list T) (k k':N) (v:T), 
    in_domain T k l -> in_domain T k (insert k' v l).
Proof.
  Hint Resolve <- in_domain_inv.
  Hint Resolve remove_preserve_other.
  intros. unfold insert. destruct (N.eq_dec k k'); auto.
Qed.

Theorem insert_invariant :
  forall (l:assoc_list T) (k:N) (v:T), al_invariant T l -> al_invariant T (insert k v l).
Proof.
  Hint Resolve al_invariant_cons remove_invariant not_in_remove.
  intros. unfold insert. intuition auto.
Qed.

Theorem insert_preserve_other :
  forall (l:assoc_list T) (k k':N) (v:T),
    k' <> k -> in_domain T k (insert k' v l) -> in_domain T k l.
Proof.
  Hint Resolve remove_subset.
  intros l k k' v ineq.  unfold insert. rewrite in_domain_inv. intuition eauto.
Qed.

Theorem in_insert :
  forall (l:assoc_list T) (k:N) (v:T), in_domain T k (insert k v l).
Proof. intros. unfold insert. apply in_domain_inv. tauto. Qed.

End InsertTheorems.

Section AssocTheorems.

Variable T : Type.

Theorem assoc_in :
  forall (l:assoc_list T) (k:N), (exists v, assoc k l = Some v) <-> in_domain T k l.
Proof.
  Hint Resolve <- in_domain_inv.
  intros l k. split.
  - induction l as [|[k' v'] t IH].
    + destruct 1. discriminate.
    + simpl. destruct (N.eq_dec k' k); subst; auto.
  - induction l as [|[k' v'] t IH].
    + destruct 1. contradiction.
    + rewrite in_domain_inv. simpl. destruct (N.eq_dec k' k); subst; intuition eauto.
Qed.

Theorem assoc_not_in :
  forall (l:assoc_list T) (k:N), assoc k l = None <-> ~in_domain T k l.
Proof.
  intros. split.
  - destruct (assoc k l) eqn:A.
    + discriminate 1.
    + intros. rewrite <- assoc_in. rewrite A. destruct 1. discriminate.
  - destruct (assoc k l) eqn:A.
    + intros.
      apply ex_intro with (P := fun x => assoc k l = Some x) in A.
      apply assoc_in in A. contradiction.
    + reflexivity.
Qed.

End AssocTheorems.

Section MergeTheorems.

Variable T : Type.

Theorem merge_no_new_elements :
  forall (l1 l2:assoc_list T) (f:T -> T -> T) (k:N),
    ~in_domain T k l1 -> ~in_domain T k l2 -> ~in_domain T k (merge f l1 l2).
Proof.
  Hint Unfold not.
  Hint Resolve remove_subset.
  intros l1 l2 f k H.
  generalize dependent l2.
  induction l1 as [|[k' v] t IH].
  - intros. assumption.
  - simpl. intros l2. rewrite in_domain_inv in H.
    destruct (assoc k' l2) eqn:A; rewrite in_domain_inv; intuition eauto.
Qed.

Theorem merge_invariant :
  forall (l1 l2:assoc_list T) (f:T -> T -> T),
    al_invariant T l1 -> al_invariant T l2 -> al_invariant T (merge f l1 l2).
Proof.
  Hint Resolve al_invariant_cons merge_no_new_elements not_in_remove remove_invariant.
  intros l1 l2 f inv_l1.
  generalize dependent l2.
  induction l1 as [|[k v] t IH].
  - intros. assumption.
  - intros l2 inv_l2. inversion inv_l1. subst. simpl. destruct (assoc k l2) eqn:A.
    + apply ex_intro with (P := fun x => assoc k l2 = Some x) in A.
      apply assoc_in in A. auto.
    + apply assoc_not_in in A. auto.
Qed.

Theorem merge_superset_first :
  forall (l1 l2:assoc_list T) (f:T -> T -> T) (k:N),
    in_domain T k l1 -> in_domain T k (merge f l1 l2).
Proof.
  Hint Resolve <- in_domain_inv.
  Hint Resolve remove_subset.
  intros l1 l2 f k.
  generalize dependent l2.
  - induction l1 as [|[k' v] t IH].
    + destruct 1. contradiction.
    + intros l2. rewrite in_domain_inv. intros H. simpl.
      destruct (assoc k' l2) eqn:A; intuition auto.
Qed.

Theorem merge_superset_second :
  forall (l1 l2:assoc_list T) (f:T -> T -> T) (k:N),
    in_domain T k l2 -> in_domain T k (merge f l1 l2).
Proof.
  Hint Resolve <- in_domain_inv.
  Hint Resolve remove_preserve_other.
  intros l1 l2 f k.
  generalize dependent l2.
  - induction l1 as [|[k' v] t IH].
    + trivial.
    + intros l2. intros H. simpl.
      destruct (assoc k' l2) eqn:A; destruct (N.eq_dec k' k); subst; auto.
Qed.

End MergeTheorems.

Section RevAssocTheorems.

Variable T : Type.

Theorem rev_assoc_assoc :
  forall (f:T -> bool) (l:assoc_list T) (k:N),
    al_invariant T l ->
    (In k (rev_assoc f l) <-> exists v, assoc k l = Some v /\ f v = true).
Proof.
  intros f l k inv_l. split.
  - generalize dependent k. induction l as [|[k' v'] t IH].
    + contradiction.
    + intros k. simpl. destruct (N.eq_dec k' k).
      * subst. destruct (f v') eqn:fv.
        intros. exists v'. split; auto.
        intros H. inversion inv_l. destruct IH with k as [v'' [A FVT]].
        assumption.
        assumption.
        apply ex_intro with (P := fun x => assoc k t = Some x) in A.
        apply assoc_in in A. contradiction.
      * destruct (f v') eqn:fv. intros H. apply in_inv in H. inversion inv_l. 
        intuition eauto.
        intros H. inversion inv_l. auto.
Abort.
