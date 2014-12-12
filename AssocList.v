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

End AssocListDef.

Section InvariantDef.

Variable T : Type.

Definition contains (k:N) (P:T -> Prop) (l:assoc_list T) : Prop :=
  exists v, In (k,v) l /\ P v.

Lemma contains_inv :
  forall (k:N) (P:T -> Prop) (k':N) (v:T) (l:assoc_list T),
    contains k P ((k',v) :: l) <-> (k' = k /\ P v) \/ contains k P l.
Proof.
  Hint Resolve in_eq in_cons.
  intros k P k' v l. unfold contains. split.
  - destruct 1 as [v' [in_k HP]]. apply in_inv in in_k. destruct in_k.
    + inversion H. subst. tauto.
    + eauto.
  - destruct 1 as [[ke HP]|[v' [v'_in HP]]]; subst; intuition eauto.
Qed.

Lemma contains_app_or :
  forall (k:N) (P:T -> Prop) (l1 l2:assoc_list T),
    contains k P (l1 ++ l2) <-> contains k P l1 \/ contains k P l2.
Proof.
  Hint Resolve in_or_app .
  unfold contains.
  intros k P l1 l2. split.
  - destruct 1 as [v [in_l12 HP]]. apply in_app_or in in_l12. intuition eauto.
  - destruct 1 as [in_l|in_l]; destruct in_l as [v [in_l HP]]; eauto.
Qed.

Definition in_domain (k:N) : assoc_list T -> Prop := contains k (fun _ => True).

Theorem contains_in_domain :
  forall (l:assoc_list T) (k:N) (P:T -> Prop), contains k P l -> in_domain k l.
Proof.
  unfold in_domain. unfold contains. intros l k P. destruct 1. intuition eauto.
Qed.

Lemma in_domain_inv :
  forall (k:N) (k':N) (v:T) (l:assoc_list T),
    in_domain k ((k',v) :: l) <-> k' = k \/ in_domain k l.
Proof. unfold in_domain. intros. rewrite contains_inv. tauto. Qed.

Theorem in_domain_contains_eq :
  forall (l:assoc_list T) (k:N), in_domain k l -> exists v, contains k (eq v) l.
Proof.
  Hint Resolve in_domain_inv in_nil.
  intros l k. induction l as [|[k' v] t IH].
  - destruct 1. exfalso. intuition auto.
  - unfold in_domain. unfold contains. destruct 1 as [v' [k_in _]].
    apply in_inv in k_in. case k_in.
    + inversion 1. subst. eauto.
    + eauto.
Qed.

Lemma in_domain_app_or :
  forall (k:N) (l1 l2:assoc_list T),
    in_domain k (l1 ++ l2) <-> in_domain k l1 \/ in_domain k l2.
Proof. unfold in_domain. intros. rewrite contains_app_or. tauto. Qed.

Definition al_disjoint (l1 l2:assoc_list T) : Prop :=
  forall k, in_domain k l1 -> ~in_domain k l2.

Lemma al_disjoint_nil_l :
  forall (l1:assoc_list T), al_disjoint nil l1.
Proof.
  intros l1 k. unfold in_domain. unfold contains. destruct 1 as [v [in_nil HP]].
  contradiction.
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
  Hint Resolve in_inv contains_in_domain.
  Hint Unfold contains in_domain not.
  intros l k v v' inv_l v_in v'_in. induction l as [|[k' v''] t IH].
  - destruct v_in.
  - inversion inv_l. subst. case v_in.
    + inversion 1. subst. case v'_in.
      * inversion 1. auto.
      * intros. exfalso. eauto 6.
    + intros. case v'_in.
      * inversion 1. subst. exfalso. eauto 6.
      * auto.
Qed.

Lemma contains_combine :
  forall (l:assoc_list T) (k:N) (P1 P2:T -> Prop),
    al_invariant l -> contains k P1 l -> contains k P2 l ->
    contains k (fun x => P1 x /\ P2 x) l.
Proof.
  Hint Resolve al_invariant_in_eq.
  unfold contains.
  intros l k P1 P2 inv_l c_P1 c_P2.
  destruct c_P1 as [v [in1 HP1]].
  destruct c_P2 as [v' [in2 HP2]].
  assert (eq: v' = v); subst; eauto.
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
  forall (l:assoc_list T) (k k':N) (P:T -> Prop),
    contains T k P (remove k' l) -> contains T k P l.
Proof.
  Hint Resolve <- contains_inv.
  intros l k k' P. induction l as [|[k'' v] t IH].
  - destruct 1 as [v [in_nil HP]]. contradiction.
  - simpl. destruct (N.eq_dec k'' k').
    + auto.
    + rewrite contains_inv. destruct 1; subst; auto.
Qed.

Theorem remove_invariant :
  forall (l:assoc_list T) (k:N), al_invariant T l -> al_invariant T (remove k l).
Proof.
  Hint Unfold not in_domain.
  Hint Resolve remove_subset al_invariant_cons.
  intros l k. induction l as [|[k' v] t IH].
  - trivial.
  - inversion 1. subst. simpl.
    destruct (N.eq_dec k' k); intuition eauto 6.
Qed.

Theorem remove_preserve_other :
  forall (l:assoc_list T) (k k':N) (P:T -> Prop),
    k' <> k -> contains T k P l -> contains T k P (remove k' l).
Proof.
  intros l k k' P ineq. induction l as [|[k'' v] t IH].
  - trivial.
  - simpl. rewrite contains_inv. destruct (N.eq_dec k'' k').
    + subst. tauto.
    + intuition auto.
Qed.

Theorem not_in_remove :
  forall (l:assoc_list T) (k:N), al_invariant T l -> ~in_domain T k (remove k l).
Proof.
  intros l k inv_l. induction l as [|[k' v] t IH].
  - destruct 1. intuition auto.
  - simpl. inversion inv_l. subst. destruct (N.eq_dec k' k); subst.
    + auto.
    + rewrite in_domain_inv. tauto.
Qed.

End RemoveTheorems.

Section InsertTheorems.

Variable T : Type.

Theorem insert_domain_superset :
  forall (l:assoc_list T) (k k':N) (v:T),
    in_domain T k l -> in_domain T k (insert k' v l).
Proof.
  Hint Resolve <- in_domain_inv.
  Hint Resolve remove_preserve_other.
  Hint Unfold in_domain.
  intros. unfold insert. destruct (N.eq_dec k k'); auto.
Qed.

Theorem insert_invariant :
  forall (l:assoc_list T) (k:N) (v:T), al_invariant T l -> al_invariant T (insert k v l).
Proof.
  Hint Resolve al_invariant_cons remove_invariant not_in_remove.
  intros. unfold insert. intuition auto.
Qed.

Theorem insert_preserve_other :
  forall (l:assoc_list T) (k k':N) (v:T) (P:T -> Prop),
    k' <> k -> (contains T k P (insert k' v l) <-> contains T k P l).
Proof.
  Hint Resolve remove_subset.
  intros l k k' v P ineq. unfold insert. rewrite contains_inv. split; intuition eauto.
Qed.

Theorem contains_insert :
  forall (l:assoc_list T) (k:N) (v:T) (P:T -> Prop),
    P v -> contains T k P (insert k v l).
Proof. intros. unfold insert. apply contains_inv. tauto. Qed.

Theorem in_insert :
  forall (l:assoc_list T) (k:N) (v:T), in_domain T k (insert k v l).
Proof. intros. apply contains_insert. apply I. Qed.

End InsertTheorems.

Section AssocTheorems.

Variable T : Type.

Theorem assoc_in_contains :
  forall (l:assoc_list T) (k:N) (v:T),
    assoc k l = Some v -> contains T k (eq v) l.
Proof.
  Hint Resolve <- contains_inv.
  intros l k v.
  induction l as [|[k' v'] t IH].
    + discriminate.
    + simpl. destruct (N.eq_dec k' k); inversion 1; subst; auto.
Qed.

Theorem contains_assoc_in :
  forall (l:assoc_list T) (k:N) (v:T),
    al_invariant T l -> contains T k (eq v) l -> assoc k l = Some v.
Proof.
  Hint Resolve contains_in_domain.
  intros l k v inv_l.
  - induction l as [|[k' v'] t IH].
    + destruct 1 as [v' [H HP]]. contradiction.
    + inversion inv_l. subst. rewrite contains_inv. simpl. destruct (N.eq_dec k' k).
      * destruct 1 as [[ke ve] | contains_in]; [|exfalso]; subst; eauto.
      * intuition auto.
Qed.

Theorem assoc_in_domain :
  forall (l:assoc_list T) (k:N),
    (exists v, assoc k l = Some v) <-> in_domain T k l.
Proof.
   Hint Resolve <- in_domain_inv.
   intros l k. split.
   - induction l as [|[k' v'] t IH].
     + destruct 1. discriminate.
     + simpl. destruct (N.eq_dec k' k); subst; auto.
   - induction l as [|[k' v'] t IH].
     + destruct 1. exfalso. intuition auto.
     + rewrite in_domain_inv. simpl. destruct (N.eq_dec k' k); subst; intuition eauto.
Qed.

Theorem assoc_in_1 :
  forall (l:assoc_list T) (k:N) (v:T),
    assoc k l = Some v -> in_domain T k l.
Proof. Hint Resolve -> assoc_in_domain. eauto. Qed.

Theorem assoc_not_in :
  forall (l:assoc_list T) (k:N), assoc k l = None <-> ~in_domain T k l.
Proof.
  Hint Resolve assoc_in_contains.
  intros. split.
  - destruct (assoc k l) eqn:A.
    + discriminate 1.
    + intros. rewrite <- assoc_in_domain. rewrite A. destruct 1. discriminate.
  - destruct (assoc k l) eqn:A.
    + intros. exfalso. eauto.
    + reflexivity.
Qed.

End AssocTheorems.

Section Merge.

Variable T : Type.

Fixpoint merge (f:T -> T -> T) (l1:assoc_list T) (l2:assoc_list T) : assoc_list T :=
  match l1 with
    | nil        => l2
    | (k,v1) :: l1_t =>
      match assoc k l2 with
        | None    => (k,v1) :: merge f l1_t l2
        | Some v2 => (k,f v1 v2) :: merge f l1_t (remove k l2)
      end
  end.
Global Arguments merge : default implicits.

Definition union : assoc_list T -> assoc_list T -> assoc_list T :=
  merge (fun _ b => b).
Global Arguments union : default implicits.

Theorem merge_no_new_elements :
  forall (l1 l2:assoc_list T) (f:T -> T -> T) (k:N),
    ~in_domain T k l1 -> ~in_domain T k l2 -> ~in_domain T k (merge f l1 l2).
Proof.
  Hint Unfold not in_domain.
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
  Hint Resolve -> assoc_not_in assoc_in_domain.
  intros l1 l2 f inv_l1.
  generalize dependent l2.
  induction l1 as [|[k v] t IH].
  - intros. assumption.
  - intros l2 inv_l2. inversion inv_l1. subst. simpl. case_eq (assoc k l2); auto.
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
    + destruct 1. exfalso. intuition auto.
    + intros l2. rewrite in_domain_inv. simpl.
      destruct (assoc k' l2) eqn:A; intuition auto.
Qed.

Theorem merge_superset_second :
  forall (l1 l2:assoc_list T) (f:T -> T -> T) (k:N),
    in_domain T k l2 -> in_domain T k (merge f l1 l2).
Proof.
  Hint Resolve <- contains_inv.
  Hint Resolve remove_preserve_other.
  intros l1 l2 f k.
  generalize dependent l2.
  - unfold in_domain. induction l1 as [|[k' v] t IH].
    + trivial.
    + intros l2. intros H. simpl.
      destruct (assoc k' l2) eqn:A; destruct (N.eq_dec k' k); subst; auto.
Qed.

End Merge.

Section RevAssoc.

Variable T : Type.

Fixpoint rev_assoc (p:T -> bool) (l:assoc_list T) : list N :=
  match l with
    | nil         => nil
    | (k,v) :: t => if p v then k :: rev_assoc p t else rev_assoc p t
  end.
Global Arguments rev_assoc : default implicits.

Theorem rev_assoc_assoc :
  forall (f:T -> bool) (l:assoc_list T) (k:N),
    al_invariant T l ->
    In k (rev_assoc f l) -> contains T k (fun v => f v = true) l.
Proof.
  intros f l k inv_l H. induction l as [|[k' v'] t IH].
  - contradiction.
  - apply contains_inv. simpl in H. inversion inv_l. subst. destruct (f v') eqn:fv.
    + apply in_inv in H. destruct (N.eq_dec k' k); intuition eauto.
    + destruct (N.eq_dec k' k). subst.
      * Hint Resolve contains_in_domain. exfalso. intuition eauto.
      * eauto.
Qed.

Theorem assoc_rev_assoc :
  forall (f:T -> bool) (l:assoc_list T) (k:N),
    al_invariant T l ->
    contains T k (fun v => f v = true) l -> In k (rev_assoc f l).
Proof.
  Hint Unfold contains.
  Hint Resolve in_eq in_cons.
  intros f l k inv_l. induction l as [|[k' v'] t IH].
  - destruct 1 as [v [a fv]]. auto.
  - simpl. inversion inv_l. subst. destruct 1 as [v [v_in fvt]].
    apply in_inv in v_in. destruct v_in as [eq|in_t].
    + inversion eq. subst. rewrite fvt. auto.
    + destruct (f v') eqn:fv'; eauto 6.
Qed.

End RevAssoc.

Section Filter.

Variable T : Type.

Definition al_filter (f:N -> T -> bool) : assoc_list T -> assoc_list T :=
  filter (fun x => match x with (k,v) => f k v end).
Global Arguments al_filter : default implicits.

Theorem al_filter_subset :
  forall (l:assoc_list T) (k:N) (P:T -> Prop) (f:N -> T -> bool),
    contains T k P (al_filter f l) -> contains T k P l.
Proof.
  Hint Resolve <- contains_inv.
  intros l k P f. induction l as [|[k' v] t IH].
  - auto.
  - simpl. destruct (f k' v) eqn:fkv.
    + rewrite contains_inv. destruct 1 as [[ke Pv] | contains_filter_t]; auto.
    + auto.
Qed.

Theorem al_filter_invariant :
  forall (l:assoc_list T) (f:N -> T -> bool),
    al_invariant T l -> al_invariant T (al_filter f l).
Proof.
  Hint Resolve al_filter_subset al_invariant_cons.
  Hint Unfold in_domain.
  intros l f H. induction l as [|[k v] t IH].
  - auto.
  - simpl. inversion H; subst. destruct (f k v) eqn:fkv; eauto 7.
Qed.

End Filter.

Definition update {T:Type} (k:N) (f:T -> T) (l:assoc_list T) : assoc_list T :=
  match assoc k l with
    | None   => l
    | Some v => insert k v l
  end.

Definition insert_merge {T:Type} (k:N) (f:T -> T) (def:T) (l:assoc_list T) : 
  assoc_list T :=
  insert k (f (match assoc k l with
                 | None   => def
                 | Some v => v
               end)) l.

Definition al_map {A B:Type} (f:N -> A -> B) : assoc_list A -> assoc_list B :=
  map (fun x => match x with (k,v) => (k,f k v) end).