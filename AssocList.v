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

Definition in_domain (k:N) (l:assoc_list) : bool :=
  match (assoc k l) with
    | None   => false
    | Some _ => true
  end.
Global Arguments in_domain : default implicits.

Fixpoint rev_assoc (p:T -> bool) (l:assoc_list) : list N :=
  match l with
    | nil         => nil
    | (k,v) :: t => if p v then k :: rev_assoc p t else rev_assoc p t
  end.
Global Arguments assoc : default implicits.

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

End AssocListDef.


Section InvariantDef.

Variable T : Type.

Definition in_domain_prop (k:N) (l:assoc_list T) : Prop :=
  exists v, In (k,v) l.

Lemma in_domain_app_or :
  forall (k:N) (l1 l2:assoc_list T),
    in_domain_prop k (l1 ++ l2) <-> in_domain_prop k l1 \/ in_domain_prop k l2.
Proof.
  intros k l1 l2. split.
  - intros H. destruct H as [v in_l12]. apply in_app_or in in_l12.
    destruct in_l12.
    + left. exists v. assumption.
    + right. exists v. assumption.
  - intros P. destruct P as [in_l | in_l];
      destruct in_l as [v in_l]; exists v; apply in_or_app; tauto.
Qed.

Definition al_disjoint (l1 l2:assoc_list T) : Prop :=
  forall k, in_domain_prop k l1 -> ~in_domain_prop k l2.

Lemma al_disjoint_nil_l :
  forall (l1:assoc_list T), al_disjoint nil l1.
Proof.
  intros l1. unfold al_disjoint. unfold in_domain_prop. intros k in_nil.
  destruct in_nil as [v v_in_nil]. inversion v_in_nil.
Qed.

Lemma al_disjoint_symmetry :
  forall (l1 l2:assoc_list T), al_disjoint l1 l2 -> al_disjoint l2 l1.
Proof.
  unfold al_disjoint. unfold in_domain_prop. unfold not. 
  intros l1 l2 H k in_l2 in_l1.
  apply H with k; assumption.
Qed.

Lemma al_disjoint_app_split :
  forall (l1 l2 l3:assoc_list T),
    al_disjoint (l1 ++ l2) l3 -> al_disjoint l1 l3 /\ al_disjoint l2 l3.
Proof.
  intros l1 l2 l3. unfold al_disjoint. unfold in_domain_prop. intros H. split;
    intros k in_l12 in_l3;
    destruct in_l12 as [v12 v_in_l12];
    apply H with k;
      try (exists v12; apply in_or_app);
      tauto.
Qed.

Lemma al_disjoint_cons_not_elem :
  forall (l1 l2:assoc_list T) (k:N) (v:T),
    ~(in_domain_prop k l2) /\ al_disjoint l1 l2 <-> al_disjoint ((k,v) :: l1) l2.
Proof.
  intros l1 l2 k v. split.
    - intros P. destruct P as [not_in_l2 H].
      unfold al_disjoint. unfold in_domain_prop. intros any_k in_r.
      destruct in_r as [vr vr_in_r].
      apply in_inv in vr_in_r.
      destruct vr_in_r as [E|in_l1].
      + inversion E as [[ke ve]]. rewrite <- ke. assumption.
      + apply H with (k := any_k). unfold in_domain_prop. exists vr. assumption.
    - intros H. split.
      + unfold al_disjoint in H.
        apply H. unfold in_domain_prop. exists v. apply in_eq.
      + replace ((k,v) :: l1) with (((k,v) :: nil) ++ l1) in H by reflexivity.
        apply al_disjoint_app_split in H. apply H.
Qed.

Inductive al_invariant : assoc_list T -> Prop :=
  | al_invariant_nil  : al_invariant nil
  | al_invariant_cons :
      forall (k:N) (v:T) (t:assoc_list T),
        ~in_domain_prop k t -> al_invariant t -> al_invariant ((k,v) :: t).

Lemma al_invariant_disjoint :
  forall (l1 l2:assoc_list T), al_invariant (l1 ++ l2) -> al_disjoint l1 l2.
Proof.
  intros l1 l2 H. induction l1 as [|h t IH].
  - apply al_disjoint_nil_l.
  - destruct h as [k v]. apply al_disjoint_cons_not_elem. split.
    + inversion H as [|k' v' t' not_in_tl2 inv_tl2]. subst.
      rewrite in_domain_app_or in not_in_tl2. intro not_in_l2. apply not_in_tl2.
      tauto.
    + apply IH. inversion H. assumption.
Qed.

Lemma al_invariant_app_split :
  forall (l1 l2:assoc_list T),
    al_invariant (l1 ++ l2) -> al_invariant l1 /\ al_invariant l2.
Proof.
  intros l1 l2 H. induction l1 as [|h t IH].
  - split. constructor. assumption.
  - destruct h as [k v]. inversion H as [|k' v' t' not_in_tl2 inv_tl2]; subst. split.
    + apply al_invariant_cons.
      * intro not_in_t. apply not_in_tl2. apply in_domain_app_or. tauto.
      * apply IH. assumption.
    + apply IH. assumption.
Qed.

Lemma al_invariant_join_app :
  forall (l1 l2:assoc_list T),
    al_invariant l1 -> al_invariant l2 -> al_disjoint l1 l2 -> al_invariant (l1 ++ l2).
Proof.
  intros l1 l2 inv_l1 inv_l2 dis. induction l1 as [|h t IH].
  - assumption.
  - destruct h as [k v]. simpl. apply <- al_disjoint_cons_not_elem in dis.
    destruct dis as [not_in_l2 dis_t_l2]. apply al_invariant_cons.
    + inversion inv_l1 as [|k' v' t' not_in_t inv_t]. subst.
      intros in_tl2. apply in_domain_app_or in in_tl2. destruct in_tl2 as [in_t | in_l2].
      * apply not_in_t. assumption.
      * apply not_in_l2. assumption.
    + apply IH.
      * inversion inv_l1. assumption.
      * assumption.
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


Section AssocListTheorems.

Variable T : Type.
Variable l : assoc_list T.
Hypothesis inv_l : al_invariant T l.

Theorem empty_al_invariant : al_invariant T empty.
Proof. intros. apply al_invariant_nil. Qed.

Lemma al_invariant_cons_snoc :
  forall (l1 l2:assoc_list T) (h:N * T),
    al_invariant T ((h :: l1) ++ l2) <-> al_invariant T (l1 ++ l2 ++ h :: nil).
Proof.
  intros l1 l2 h. replace (h :: l1) with ((h :: nil) ++ l1) by reflexivity.
  split.
  - intros H.
    rewrite app_assoc. apply al_invariant_app_comm. rewrite app_assoc. assumption.
  - intros H.
    rewrite <- app_assoc. apply al_invariant_app_comm. rewrite <- app_assoc. assumption.
Qed.

Lemma remove_al_invariant_helper :
  forall (k:N) (l2:assoc_list T),
    al_invariant T (l ++ l2) -> al_invariant T (remove k l ++ l2).
Proof.
  intros k. induction l as [|h t IH].
  - trivial.
  - intros l2 H. destruct h as [k' v]. simpl. destruct (N.eq_dec k' k) as [E|E].
    + inversion H. assumption.
    + rewrite al_invariant_cons_snoc. apply IH.
      * apply al_invariant_app_split in H. destruct H as [Ha Hb].
        inversion Ha. assumption.
      * rewrite <- al_invariant_cons_snoc. assumption.
Qed.

Theorem remove_al_invariant : forall (k:N), al_invariant T (remove k l).
Proof.
  intros. rewrite <- app_nil_r. apply remove_al_invariant_helper.
  rewrite app_nil_r. assumption.
Qed.

Theorem remove_not_in :
  forall (k:N), ~in_domain_prop T k (remove k l).
Proof.
  unfold in_domain_prop. intros k in_r. destruct in_r as [v in_r]. induction l as [|h t IH].
  - inversion in_r.
  - destruct h as [k' v']. simpl in in_r. destruct (N.eq_dec k' k) as [E|E].
    + subst. inversion inv_l as [|k'' v'' t'' not_in_t inv_t]. subst. apply not_in_t.
      exists v. assumption.
    + apply IH.
      * inversion inv_l. assumption.
      * inversion in_r. inversion H. contradiction. assumption.
Qed.

Theorem insert_al_invariant :
  forall (k:N) (v:T), al_invariant T (insert k v l).
Proof.
  intros. unfold insert. apply al_invariant_cons. apply remove_not_in.
  apply remove_al_invariant.
Qed.

Theorem assoc_insert :
  forall (k:N) (v:T), assoc k (insert k v l) = Some v.
Proof.
  intros k v. unfold insert. simpl. destruct (N.eq_dec k k).
  - reflexivity.
  - elimtype False. apply n. reflexivity.
Qed.

Theorem assoc_not_in :
  forall (k:N) (l2:assoc_list T),
    ~in_domain_prop T k l2 -> assoc k l2 = None.
Proof.
  intros k l2 not_in. induction l2 as [|h t IH].
  - reflexivity.
  - destruct h as [k' v]. simpl. destruct (N.eq_dec k' k).
    + elimtype False. apply not_in. rewrite e. exists v. apply in_eq.
    + apply IH. intros in_t. apply not_in. destruct in_t as [v' v'_in_t].
      exists v'. apply in_cons. assumption.
Qed.

Theorem assoc_remove :
  forall (k:N), assoc k (remove k l) = None.
Proof. intros k. apply assoc_not_in. apply remove_not_in. Qed.

Theorem assoc_empty :
  forall (k:N), assoc k (@empty T) = None.
Proof. reflexivity. Qed.

End AssocListTheorems.

(*
- in_domain
- fold (mit key)
- rev_assoc (mit predicate)
- union/merge