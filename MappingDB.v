Require Import NArith.
Require Import List.
Require Import AssocList.

Section MappingDB.

Variable kernel_object : Type.

Definition mapping_db : Type := assoc_list (assoc_list kernel_object).

Definition has_mapping (pd:N) (sel:N) (ko:kernel_object) : mapping_db -> Prop :=
  contains _ pd (contains _ sel (eq ko)).

Definition create_mapping (pd:N) (sel:N) (ko:kernel_object) : mapping_db -> mapping_db :=
  insert_merge pd (insert sel ko) empty.

Definition remove_mapping (pd:N) (sel:N) : mapping_db -> mapping_db :=
  update pd (remove sel).

Fixpoint restrict (exceptions:assoc_list (list N)) : mapping_db -> mapping_db :=
  al_map (fun pd mappings =>
    match assoc pd exceptions with
      | None     => mappings
      | Some exc =>
        al_filter (fun sel _ => if in_dec N.eq_dec sel exc then true else false) mappings
    end).


Definition remove_all (f:kernel_object -> bool) : mapping_db -> mapping_db :=
  al_map (fun _ => al_filter (fun _ => f)).

Definition remove_all_except
           (f:kernel_object -> bool)
           (exceptions:assoc_list (list N))
           (db:mapping_db) : mapping_db :=
  union (restrict exceptions db) (remove_all f db).

Theorem create_preserve_other :
  forall (db:mapping_db) (pd pd':N) (sel sel':N) (ko ko':kernel_object),
    (pd' <> pd \/ sel' <> sel) -> al_invariant _ db ->
    (has_mapping pd sel ko db
     <-> has_mapping pd sel ko (create_mapping pd' sel' ko' db)).
Proof.
  Hint Resolve <- insert_preserve_other.
  Hint Resolve contains_insert.
  intros db pd pd' sel sel' ko ko' ineq inv_db. split.
  - unfold create_mapping. unfold insert_merge. destruct (assoc pd' db) eqn:A.
    + intros H. unfold has_mapping. destruct (N.eq_dec pd' pd); subst; eauto.
      destruct ineq as [pde | sele].
      * eauto.
      * apply contains_insert. apply insert_preserve_other. assumption. unfold has_mapping in H. apply assoc_in_contains in A.
        apply contains_combine with (P1 := eq a) in H.
        unfold contains in H. destruct H as [v [in_db [av E]]].
        unfold contains. subst. assumption. assumption. assumption.
    + destruct (N.eq_dec pd' pd). 
      * destruct ineq as [H|H]; try tauto. subst. unfold has_mapping. intros P. 
        apply contains_in_domain in P. apply assoc_not_in in A. contradiction.
      * intros. unfold has_mapping. apply insert_preserve_other. assumption.
        assumption.
  - unfold create_mapping. unfold insert_merge. intros H. unfold has_mapping.
    destruct (assoc pd' db) eqn:A.
    + destruct ineq as [ineq|ineq]. 
      * apply insert_preserve_other in H; assumption.
      * destruct (N.eq_dec pd' pd).
        subst. unfold has_mapping in H.
Abort.

Theorem create_has_mapping :
  forall (db:mapping_db) (pd:N) (sel:N) (ko:kernel_object),
    has_mapping pd sel ko (create_mapping pd sel ko db).
Proof.
Abort.

Theorem remove_removes_mapping :
  forall (db:mapping_db) (pd:N) (sel:N) (ko:kernel_object),
    ~has_mapping pd sel ko (remove_mapping pd sel db).
Proof.
Abort.

Theorem remove_preserve_other :
  forall (db:mapping_db) (pd pd':N) (sel sel':N) (ko:kernel_object),
    (pd' <> pd /\ sel <> sel') ->
    (has_mapping pd sel ko db <-> has_mapping pd sel ko (remove_mapping pd sel db)).
Proof.
Abort.

Theorem remove_all_except_removes :
  forall (db:mapping_db) (pd:N) (sel:N) (ko:kernel_object) (f:kernel_object -> bool)
         (exceptions:assoc_list (list N)),
    has_mapping pd sel ko (remove_all_except f exceptions db) ->
    f ko = false \/ contains (list N) pd (In sel) exceptions.
Proof.
Abort.

Theorem remove_all_except_preseve_other :
  forall (db:mapping_db) (pd:N) (sel:N) (ko:kernel_object) (f:kernel_object -> bool)
         (exceptions:assoc_list (list N)),
    f ko = true ->
    (has_mapping pd sel ko db <->
     has_mapping pd sel ko (remove_all_except f exceptions db)).
Proof.
Abort.

End MappingDB.