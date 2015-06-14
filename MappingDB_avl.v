Require Import NArith.
Require List.
Require Import AVLTree.
Require Import Bool.

Section MappingDB.
Variable kernel_object : Type.

Section Def.

  Definition mapping_db : Type := avl_tree (avl_tree kernel_object).

  Definition has_mapping (pd:N) (sel:N) (ko:kernel_object) : mapping_db -> Prop :=
    contains pd (In (sel,ko)).

  Definition in_mapping_db (pd:N) (sel:N) : mapping_db -> Prop :=
    contains pd (in_domain sel).

  Definition mapping_db_inv (db:mapping_db) : Prop :=
    avl_tree_invariant db /\ (forall k v, In (k,v) db -> avl_tree_invariant v).

End Def.

Section Create.

  Definition create_mapping (pd:N) (sel:N) (ko:kernel_object) :
    mapping_db -> mapping_db :=
    avl_insert_merge pd (avl_insert sel ko) (avl_insert sel ko Avl_empty).

  Theorem create_has_mapping :
    forall (db:mapping_db) (pd:N) (sel:N) (ko:kernel_object),
      mapping_db_inv db ->
      has_mapping pd sel ko (create_mapping pd sel ko db).
  Proof.
    Hint Resolve insert_In In_contains.
    intros db pd sel ko db_inv. unfold has_mapping. unfold create_mapping.
    unfold mapping_db_inv in db_inv. unfold avl_tree_invariant in db_inv.
    apply insert_merge_contains; simpl; intuition eauto.
  Qed.

  Lemma ineq_2_dec :
    forall (a a' b b':N), (a <> a' \/ b <> b') -> (a <> a' \/ (a = a' /\ b <> b')).
  Proof.
    intros a a' b b' H. destruct (N.eq_dec a a'); tauto.
  Qed.

  Theorem create_preserve_other :
    forall (db:mapping_db) (pd pd':N) (sel sel':N) (ko ko':kernel_object),
      (pd' <> pd \/ sel' <> sel) -> mapping_db_inv db ->
      (has_mapping pd sel ko db
       <-> has_mapping pd sel ko (create_mapping pd' sel' ko' db)).
  Proof.
    Hint Resolve <- insert_preserve_other insert_merge_preserve_other.
    Hint Resolve -> insert_preserve_other insert_merge_preserve_other.
    pose In_in_domain as T3.
    pose In_eq as T4.
    intros db pd pd' sel sel' ko ko' ineq inv_db. apply ineq_2_dec in ineq.
    unfold has_mapping. unfold create_mapping. destruct ineq as [H|[? H]].
    - split;
      destruct 1 as [pd_mappings [in_db in_pd]];
      eapply insert_merge_preserve_other in in_db; eauto.
    - subst. split.
      + destruct 1 as [pd_mappings [in_db in_pd]]. apply insert_merge_contains.
        * apply inv_db.
        * intros not_in_db. exfalso. eauto. 
        * intros v v_in_db. unfold mapping_db_inv in inv_db.
          unfold avl_tree_invariant in inv_db.
          replace v with pd_mappings; intuition eauto.
      + destruct 1 as [pd_mappings [in_created in_pd]]. unfold mapping_db_inv in inv_db.
        unfold avl_tree_invariant in inv_db.
        apply insert_merge_In_inv in in_created as [[? ?] | [? [? ?]]];
          subst;
          try apply insert_preserve_other in in_pd;
          intuition eauto.
  Qed.
  
  Theorem create_invariant :
    forall (db:mapping_db) (pd:N) (sel:N) (ko:kernel_object),
      mapping_db_inv db ->
      mapping_db_inv (create_mapping pd sel ko db).
  Proof.
    pose insert_merge_binary_tree_invariant as T1.
    pose insert_merge_balance_correct as T2.
    pose insert_balance_correct as T3.
    pose insert_binary_tree_invariant as T4.
    assert (empty_balance_correct:
              forall T, balance_correct (@Avl_empty T)) by (simpl; auto).
    intros db pd sel ko. intros inv_db. unfold create_mapping.
    unfold mapping_db_inv in *.
    split.
    - unfold avl_tree_invariant in *. intuition auto.
    - intros k v H. destruct (N.eq_dec pd k).
      + subst. unfold avl_tree_invariant in *. apply insert_merge_In_inv in H.
        { destruct H as [H|H].
          - intuition (subst; simpl; auto).
          - destruct H as [x [in_db xe]]. subst v. destruct inv_db as [_ P].
            specialize P with k x. intuition auto.
        } tauto.
      + rewrite <- insert_merge_preserve_other in H; simpl; intuition eauto.
  Qed.

End Create.

Section Delete.

  Definition delete_mapping (pd:N) (sel:N) : mapping_db -> mapping_db :=
    avl_update pd (avl_remove sel).

  Theorem delete_deletes_mapping :
    forall (db:mapping_db) (pd:N) (sel:N) (ko:kernel_object),
      mapping_db_inv db -> ~has_mapping pd sel ko (delete_mapping pd sel db).
  Proof.
    pose remove_not_In as T1. unfold not in T1.
    intros db pd sel ko inv_db. unfold delete_mapping. unfold has_mapping.
    unfold mapping_db_inv in inv_db. unfold avl_tree_invariant in inv_db.
    destruct inv_db as [inv_db inv_sel].
    destruct 1 as [pdv [pd_in sel_in]].
    apply update_In_inv in pd_in as [x [in_db rm_eq]].
    - subst. specialize inv_sel with pd x. intuition eauto.
    - tauto.
  Qed.

  Theorem delete_preserve_other :
    forall (db:mapping_db) (pd pd':N) (sel sel':N) (ko:kernel_object),
      mapping_db_inv db ->
      (pd' <> pd \/ sel <> sel') ->
      (has_mapping pd sel ko db <-> has_mapping pd sel ko (delete_mapping pd' sel' db)).
  Proof.
    Hint Resolve -> update_preserve_other remove_preserve_other.
    Hint Resolve <- update_preserve_other remove_preserve_other.
    intros db pd pd' sel sel' ko [inv_db inv_all] ineq. apply ineq_2_dec in ineq.
    unfold has_mapping. unfold contains. unfold delete_mapping.
    destruct ineq as [H|[pd_eq sel_ineq]].
    - split; destruct 1; intuition eauto.
    - subst. split; destruct 1 as [pdm [in_db in_pdm]].
      + exists (avl_remove sel' pdm). split.
        * unfold avl_tree_invariant in inv_db.
          rewrite update_In_inv; try (exists pdm; split); tauto.
        * rewrite remove_preserve_other in in_pdm.
          destruct in_pdm as [H|H].
          { apply H. }
          { simpl in H. absurd (sel = sel'); tauto. }          
      + unfold avl_tree_invariant in inv_db.
        apply update_In_inv in in_db as [? [? ?]]; subst; intuition eauto.
  Qed.

  Theorem delete_invariant :
    forall (db:mapping_db) (pd sel:N),
      mapping_db_inv db -> mapping_db_inv (delete_mapping pd sel db).
  Proof.
    intros db pd sel [db_inv sel_inv]. unfold delete_mapping.    
    unfold mapping_db_inv. unfold avl_tree_invariant in *.
    pose update_balance_correct as T1. pose update_binary_tree_invariant as T2.
    pose remove_balance_correct as T3. pose remove_binary_tree_invariant as T4. split.
    - intuition auto.
    - intros k v H. destruct (N.eq_dec k pd) as [eq|ineq].
      + subst. apply update_In_inv in H.
        * destruct H as [pd_mappings [in_db mappings_eq]]. subst v.
          apply sel_inv in in_db.
          intuition auto.
        * tauto.
      + apply update_preserve_other in H; eauto.
  Qed.

End Delete.

Section DeleteAll.

  Definition delete_all_except
             (f:kernel_object -> bool)
             (exceptions:avl_tree (list N))
             : mapping_db -> mapping_db :=
    avl_map
      (fun pd pdm =>
         match avl_lookup pd exceptions with
           | None     => avl_filter (fun _ x => negb (f x)) pdm
           | Some exc => avl_filter
                           (fun sel x => negb (andb
                                                 (f x)
                                                 (negb (List.existsb (N.eqb sel) exc))))
                           pdm
         end).

  Theorem delete_all_except_deletes :
    forall (db:mapping_db) (pd:N) (sel:N) (ko:kernel_object) (f:kernel_object -> bool)
           (exceptions:avl_tree (list N)),
      mapping_db_inv db ->
      has_mapping pd sel ko (delete_all_except f exceptions db) ->
      f ko = false \/ contains pd (List.In sel) exceptions.
  Proof.
    pose lookup_In as T1.
    intros db pd sel ko f exceptions db_inv. unfold mapping_db_inv in db_inv.
    unfold avl_tree_invariant in db_inv.
    unfold has_mapping.
    unfold delete_all_except. unfold contains. destruct 1 as [pdm [in_map in_pdm]].
    apply In_map_iff in in_map as [pdm' [pdm_pdm' pdm'_in_db]].
    assert (bt_inv_pdm': binary_tree_invariant pdm'). {
      apply proj2 in db_inv. apply db_inv in pdm'_in_db. tauto.
    }           
    destruct (avl_lookup pd exceptions) eqn:A; subst pdm.
    - apply filter_predicate_true in in_pdm.
      + apply negb_true_iff in in_pdm. apply andb_false_iff in in_pdm.
        destruct in_pdm as [H|H].
        * tauto.
        * apply negb_false_iff in H. apply List.existsb_exists in H as [sel' [in_l E]].
          apply Neqb_ok in E. subst. eauto.
      + assumption.
    - apply filter_predicate_true in in_pdm.
      + apply negb_true_iff in in_pdm. tauto.
      + assumption.
  Qed.

  Theorem delete_all_except_preseve_other :
  forall (db:mapping_db) (pd:N) (sel:N) (ko:kernel_object) (f:kernel_object -> bool)
         (exceptions:avl_tree (list N)),
    mapping_db_inv db ->
    f ko = false ->
    (has_mapping pd sel ko db <->
     has_mapping pd sel ko (delete_all_except f exceptions db)).
  Proof.
    intros db pd sel ko f exceptions db_inv ffalse. unfold delete_all_except.
    unfold mapping_db_inv in db_inv. unfold avl_tree_invariant in db_inv.
    apply proj2 in db_inv. split.
    - unfold has_mapping. unfold contains.
      destruct 1 as [pdm [in_db in_pdm]].
      assert (pdm_bt_inv: binary_tree_invariant pdm) by (apply db_inv in in_db; tauto).
      destruct (avl_lookup pd exceptions) eqn:A;
        eexists; (split;
          [ apply In_map_iff; rewrite A; eauto
          | apply filter_In; assumption || (rewrite negb_true_iff; rewrite ffalse; simpl; auto)
          ]).        
    - unfold has_mapping. unfold contains. destruct 1 as [pdm [in_map in_pdm]].
      apply In_map_iff in in_map. destruct in_map as [pdm' [pdm_pdm' in_db]].
      destruct (avl_lookup pd exceptions);
        subst pdm;
        (apply filter_In in in_pdm;
        [(destruct in_pdm; eauto)
        |(apply db_inv in in_db; tauto)
        ]).
  Qed.

  Theorem delete_all_invariant :
    forall (db:mapping_db) (pd:N) (sel:N) (ko:kernel_object) (f:kernel_object -> bool)
           (exceptions:avl_tree (list N)),
      mapping_db_inv db -> mapping_db_inv (delete_all_except f exceptions db).
  Proof.
    pose map_balance_correct as T1. pose map_binary_tree_invariant as T2.
    pose filter_balance_correct as T3. pose filter_binary_tree_invariant as T4.
    intros db pd sel ko f exceptions db_inv. unfold mapping_db_inv in *.
    unfold avl_tree_invariant in *. unfold delete_all_except. split. 
    - intuition auto.
    - intros k pd_mappings' in_r.
      apply In_map_iff in in_r as [pd_mappings [mappings_eq in_db]].
      subst pd_mappings'. apply proj2 in db_inv. apply db_inv in in_db.
      destruct (avl_lookup k exceptions); intuition eauto.
  Qed.

End DeleteAll.

End MappingDB.