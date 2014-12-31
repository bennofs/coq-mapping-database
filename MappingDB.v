Require Import NArith.
Require Import List.
Require Import AssocList.
Require Import Bool.

Section MappingDB.
Variable kernel_object : Type.

Section Def.

  Definition mapping_db : Type := assoc_list (assoc_list kernel_object).

  Definition has_mapping (pd:N) (sel:N) (ko:kernel_object) : mapping_db -> Prop :=
    contains pd (In (sel,ko)).

  Definition in_mapping_db (pd:N) (sel:N) : mapping_db -> Prop :=
    contains pd (in_domain sel).

End Def.

Section Create.

  Definition create_mapping (pd:N) (sel:N) (ko:kernel_object) :
    mapping_db -> mapping_db :=
    al_insert_merge pd (al_insert sel ko) (al_insert sel ko al_empty).

  Theorem create_has_mapping :
    forall (db:mapping_db) (pd:N) (sel:N) (ko:kernel_object),
      has_mapping pd sel ko (create_mapping pd sel ko db).
  Proof.
    Hint Resolve insert_In In_contains.
    intros db pd sel ko. unfold has_mapping. unfold create_mapping.
    apply insert_merge_contains; simpl; eauto.
  Qed.

  Lemma ineq_2_dec :
    forall (a a' b b':N), (a <> a' \/ b <> b') -> (a <> a' \/ (a = a' /\ b <> b')).
  Proof.
    intros a a' b b' H. destruct (N.eq_dec a a'); tauto.
  Qed.

  Theorem create_preserve_other :
    forall (db:mapping_db) (pd pd':N) (sel sel':N) (ko ko':kernel_object),
      (pd' <> pd \/ sel' <> sel) -> al_invariant db ->
      (has_mapping pd sel ko db
       <-> has_mapping pd sel ko (create_mapping pd' sel' ko' db)).
  Proof.
    Hint Resolve <- insert_preserve_other insert_merge_preserve_other.
    Hint Resolve -> insert_preserve_other insert_merge_preserve_other.
    Hint Resolve insert_In In_contains In_in_domain al_invariant_in_eq.
    intros db pd pd' sel sel' ko ko' ineq inv_db. apply ineq_2_dec in ineq.
    unfold has_mapping. unfold create_mapping. destruct ineq as [H|[? H]].
    - split;
      destruct 1 as [pd_mappings [in_db in_pd]];
      eapply insert_merge_preserve_other in in_db; eauto.
    - subst. split.
      + destruct 1 as [pd_mappings [in_db in_pd]]. apply insert_merge_contains.
        * intros. exfalso. eauto.
        * intros. replace v with pd_mappings by eauto. eauto.
      + destruct 1 as [pd_mappings [in_created in_pd]].
        apply In_insert_merge_inv in in_created as [[? ?] | [? [? ?]]];
          subst;
          try (apply insert_preserve_other in in_pd);
          eauto.
  Qed.

End Create.

Section Delete.

  Definition delete_mapping (pd:N) (sel:N) : mapping_db -> mapping_db :=
    al_update pd (al_remove sel).

  Theorem delete_deletes_mapping :
    forall (db:mapping_db) (pd:N) (sel:N) (ko:kernel_object),
      (forall k x, In (k,x) db -> al_invariant x) ->
      al_invariant db -> ~has_mapping pd sel ko (delete_mapping pd sel db).
  Proof.
    Hint Unfold not.
    Hint Resolve remove_not_in In_in_domain.
    intros db pd sel ko inv inv_l. unfold delete_mapping. unfold has_mapping.
    destruct 1 as [pdv [pd_in sel_in]].
    apply In_update_inv in pd_in as [x [in_db rm_eq]];
      try (eapply remove_not_in with (l := x));
      subst; eauto.
  Qed.

  Theorem delete_preserve_other :
    forall (db:mapping_db) (pd pd':N) (sel sel':N) (ko:kernel_object),
      al_invariant db ->
      (forall k x, In (k,x) db -> al_invariant x) ->
      (pd' <> pd \/ sel <> sel') ->
      (has_mapping pd sel ko db <-> has_mapping pd sel ko (delete_mapping pd' sel' db)).
  Proof.
    Hint Resolve -> update_preserve_other remove_preserve_other.
    Hint Resolve <- update_preserve_other remove_preserve_other.
    Hint Resolve update_updates.
    intros db pd pd' sel sel' ko inv_db inv_all ineq. apply ineq_2_dec in ineq.
    unfold has_mapping. unfold contains. unfold delete_mapping.
    destruct ineq as [H|[pd_eq sel_ineq]].
    - split; destruct 1; intuition eauto.
    - subst. split; destruct 1 as [pdm [in_db in_pdm]].
      + eauto.
      + apply In_update_inv in in_db as [? [? ?]]; subst; eauto.
  Qed.

End Delete.

Section Union.

  Definition db_union : mapping_db -> mapping_db -> mapping_db :=
    al_merge (@al_union _).

  Theorem merge_In_first :
    forall (T:Type) (l1 l2:assoc_list T) (f:T -> T -> T) (v:T) (k:N),
      al_invariant l1 -> al_invariant l2 -> ~in_domain k l2 -> In (k,v) (al_merge f l1 l2) -> In (k,v) l1.
  Proof.
    Hint Resolve In_in_domain in_eq in_cons merge_invariant.
    Hint Resolve <- insert_merge_preserve_other.
    intros T l1 l2 f v k inv_l1 inv_l2 not_in_l1 in_merge.
    induction l1 as [|[k' v'] t IH].
    - exfalso. eauto.
    - simpl in in_merge. inversion inv_l1. subst. destruct (N.eq_dec k k').
      + subst k'. apply In_insert_merge_inv in in_merge as [[_ ve]|contains_merge].
        * subst. eauto.
        * destruct contains_merge as [x [x_in _]]. exfalso.
          eapply merge_no_new_elements with (l1 := t) (l2 := l2); eauto.
        * eauto.
      + apply insert_merge_preserve_other in in_merge; eauto.
  Qed.

  Theorem merge_In_second :
    forall (T:Type) (l1 l2:assoc_list T) (f:T -> T -> T) (v:T) (k:N),
      ~in_domain k l1 -> In (k,v) (al_merge f l1 l2) -> In (k,v) l2.
  Proof.
    intros T l1 l2 f v k not_in_l2 in_merge.
    induction l1 as [|[k' v'] t IH].
    - assumption.
    - simpl in in_merge. apply not_in_domain_inv in not_in_l2 as [ineq_k not_in_t].
      apply insert_merge_preserve_other in in_merge; eauto.
  Qed.

  Theorem merge_In_both :
    forall (T:Type) (l1 l2:assoc_list T) (f:T -> T -> T) (v:T) (k:N),
      al_invariant l1 -> al_invariant l2 ->
      in_domain k l1 -> in_domain k l2 -> In (k,v) (al_merge f l1 l2) ->
      exists x y, f x y = v /\ In (k,x) l1 /\ In (k,y) l2.
  Proof.
    Hint Resolve merge_superset_second merge_invariant In_in_domain in_cons.
    Hint Resolve -> insert_merge_preserve_other.
    intros T l1 l2 f v k inv_l1 inv_l2 in_l1 in_l2 in_merge.
    induction l1 as [|[k' v'] t IH].
    - destruct in_l1. contradiction.
    - destruct in_l1 as [x [E | in_t]].
      + inversion E. subst k'. subst x. clear E.
        simpl in in_merge. apply In_insert_merge_inv in in_merge.
        * destruct in_merge as [[not_in_merge ve]|contains_t].
          { exfalso. eauto. }
          { unfold contains in contains_t.
            destruct contains_t as [a [in_merge fe]].
            clear IH. exists v'. exists a.
            inversion inv_l1. subst. apply merge_In_second in in_merge;
              repeat split; auto. }
        * inversion inv_l1. subst. auto.
      + inversion inv_l1. subst. simpl in in_merge.
        destruct (N.eq_dec k k').
        * subst. exfalso. eauto.
        * destruct IH as [x' [y' [fe' [in_t' in_l2']]]]; subst; repeat eexists; eauto.
  Qed.

  Theorem db_union_In_second :
    forall (db1 db2:mapping_db) (ko:kernel_object) (pd sel:N),
      al_invariant db1 -> al_invariant db2 ->
      ~in_mapping_db pd sel db1 -> has_mapping pd sel ko (db_union db1 db2) ->
      has_mapping pd sel ko db2.
  Proof.
    Hint Unfold contains.
    Hint Resolve In_in_domain.
    unfold has_mapping. unfold db_union. unfold contains.
    intros db1 db2 ko pd sel inv_db1 inv_db2 not_in_db1 in_union.
    destruct in_union as [pdm [in_union in_pdm]].
    destruct (in_domain_dec _ db1 pd) as [pd_in_db1|pd_not_in_db1].
    - destruct (in_domain_dec _ db2 pd) as [pd_in_db2|pd_not_in_db2].
      + apply merge_In_both with (1 := inv_db1) (2 := inv_db2) (3 := pd_in_db1) (4 := pd_in_db2) in in_union.
        destruct in_union as [x [y [pdme [in_db1 in_db2]]]].
          subst pdm. destruct (in_domain_dec _ x sel).
          { exfalso. apply not_in_db1. unfold in_mapping_db. unfold contains. eauto. }
          { apply merge_In_second in in_pdm; try (eexists; split); eauto. }
      + apply merge_In_first with (1 := inv_db1) (2 := inv_db2) (3 := pd_not_in_db2) in in_union. exfalso. apply not_in_db1. unfold in_mapping_db. eauto.
    - apply merge_In_second with (1 := pd_not_in_db1) in in_union.
      eauto.
  Qed.

End Union.

Section DeleteAll.

  Definition delete_all_except
             (f:kernel_object -> bool)
             (exceptions:assoc_list (list N))
             : mapping_db -> mapping_db :=
    al_map
      (fun pd pdm =>
         match al_assoc pd exceptions with
           | None     => al_filter (fun _ x => negb (f x)) pdm
           | Some exc => al_filter
                           (fun sel x => negb (andb
                                                 (f x)
                                                 (negb (existsb (N.eqb sel) exc))))
                           pdm
         end).

  Theorem In_map_iff :
    forall (A B:Type) (f:N -> A -> B) (l:assoc_list A) (b:B) (k:N),
      In (k, b) (al_map f l) <-> exists a : A, b = f k a /\ In (k,a) l.
  Proof.
    intros A B f l b k. unfold al_map. rewrite in_map_iff. split.
    - destruct 1 as [x [E H]]. destruct x. inversion E. subst. eauto.
    - destruct 1 as [a [E H]]. exists (k,a). subst. auto.
  Qed.

  Theorem al_filter_In :
    forall (T:Type) (f:N -> T -> bool) (l:assoc_list T) (k:N) (v:T),
      (f k v = true /\ In (k,v) l) <-> In (k,v) (al_filter f l).
  Proof.
    intros. unfold al_filter. rewrite filter_In. tauto.
  Qed.

  Theorem delete_all_except_deletes :
    forall (db:mapping_db) (pd:N) (sel:N) (ko:kernel_object) (f:kernel_object -> bool)
           (exceptions:assoc_list (list N)),
      has_mapping pd sel ko (delete_all_except f exceptions db) ->
      f ko = false \/ contains pd (In sel) exceptions.
  Proof.
    Hint Resolve assoc_In.
    intros db pd sel ko f exceptions. unfold has_mapping.
    unfold delete_all_except. unfold contains. destruct 1 as [pdm [in_map in_pdm]].
    apply In_map_iff in in_map as [pdm' [pdm_pdm' pdm'_in_db]].
    destruct (al_assoc pd exceptions) eqn:A;
      subst pdm; apply filter_predicate_true in in_pdm;
      apply negb_true_iff in in_pdm.
    - apply andb_false_iff in in_pdm. destruct in_pdm as [H|H].
      + tauto.
      + apply negb_false_iff in H. apply existsb_exists in H as [sel' [in_l E]].
        apply Neqb_ok in E. subst. eauto.
    - eauto.
  Qed.

  Theorem delete_all_except_preseve_other :
  forall (db:mapping_db) (pd:N) (sel:N) (ko:kernel_object) (f:kernel_object -> bool)
         (exceptions:assoc_list (list N)),
    f ko = false ->
    (has_mapping pd sel ko db <->
     has_mapping pd sel ko (delete_all_except f exceptions db)).
  Proof.
    intros db pd sel ko f exceptions ffalse. unfold delete_all_except.
    split.
    - unfold has_mapping. unfold contains.
      destruct 1 as [pdm [in_db in_pdm]]. destruct (al_assoc pd exceptions) eqn:A;
        eexists; (split;
          [ apply In_map_iff; rewrite A; eauto
          | apply al_filter_In; rewrite negb_true_iff; rewrite ffalse; simpl; auto
          ]).
    - unfold has_mapping. unfold contains. destruct 1 as [pdm [in_map in_pdm]].
      apply In_map_iff in in_map. destruct in_map as [pdm' [pdm_pdm' in_db]].
      destruct (al_assoc pd exceptions);
        subst pdm; apply al_filter_In in in_pdm; destruct in_pdm; eauto.
  Qed.

End DeleteAll.

End MappingDB.