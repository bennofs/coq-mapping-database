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