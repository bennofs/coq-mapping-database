Require Import NArith.
Require Import Bool.

Open Scope N.

(** This data types represents a number that is either negative (-1), zero (0) or 
 * positive.
 * It is mostly used to represent the sign of differences (for example, the difference
 * in the height of the two subtrees in an AVL tree).
 *)
Inductive sign : Type :=
  | negative : sign
  | zero : sign
  | positive : sign.

(** Get the opposite sign (maps negative to positive and positive to negative). *)
Definition sign_negate (a:sign) : sign :=
  match a with
    | negative => positive
    | zero     => zero
    | positive => negative
  end.

(** Two signs are either equal or not. *)
Definition sign_eq_dec (a b:sign) : {a = b} + {a <> b}.
Proof.
  destruct a; destruct b; auto || (right; discriminate 1).
Defined.

Definition beq_sign (a b:sign) : bool :=
  match (a,b) with
    | (negative, negative) => true
    | (zero, zero) => true
    | (positive, positive) => true
    | (_, _) => false
  end.

(** Definition of an AVL tree. The invariant for this tree (defined later) is that
 * the difference in height of the left and the right subtree is always between -1 and 1.
 *)
Inductive avl_tree (T:Type) : Type :=
  (** A branch consists of a balance, the left subtree, the key + value and the
   * right subtree. The balance if [positive] if the left subtree's height is greater
   * than the height of the right subtree. If the heights are the same, the balance is
   * [zero], otherwise it will be [negative].
   *)
  | avl_branch : sign -> avl_tree T -> N * T -> avl_tree T -> avl_tree T
  | avl_empty  : avl_tree T.
Arguments avl_branch [T] _ _ _ _.
Arguments avl_empty [T].

(** Proposition that states that the given key/value pair is contained in the tree. *)
Fixpoint In {T:Type} (v:N * T) (t:avl_tree T) : Prop :=
  match t with
    | avl_empty => False
    | avl_branch _ l v' r => v = v' \/ In v l \/ In v r
  end.

(** A tree consisting only of a single element. *)
Definition avl_singleton {T:Type} (k:N) (v:T) : avl_tree T :=
  avl_branch zero avl_empty (k,v) avl_empty.

(** The empty tree doesn't contain any elements. *)
Theorem not_In_empty : forall (T:Type) (k:N) (v:T), ~In (k,v) avl_empty.
Proof. intros. destruct 1. Qed.

Section Height.

  Variable T : Type.

  (** Calculate the height of an AVL tree. The height is maximal number of edges from
   * the root to any leaf.
   *)
  Fixpoint avl_height (t:avl_tree T) : N :=
    match t with
      | avl_empty => 0
      | avl_branch _ l _ r => N.succ (N.max (avl_height l) (avl_height r))
    end.
  Global Arguments avl_height : default implicits.

  Example avl_height_ex_empty : avl_height avl_empty = 0.
  Proof. reflexivity. Qed.

  Example avl_height_ex_1 :
    forall a b c d : T,
      avl_height
        (avl_branch
           negative
           (avl_singleton 1 a)
           (2,b)
           (avl_branch
              positive
              (avl_singleton 3 c)
              (4,d)
              avl_empty)) = 3.
  Proof. reflexivity. Qed.

End Height.

Section Invariants.

  Variable T : Type.

  Fixpoint forall_keys (f:N -> Prop) (t:avl_tree T) : Prop :=
    match t with
      | avl_empty => True
      | avl_branch _ l p r => f (fst p) /\ forall_keys f l /\ forall_keys f r
    end.
  Global Arguments forall_keys : default implicits.

  Theorem all_keys_greater_chain :
    forall (k k':N) (t:avl_tree T),
      k' < k -> forall_keys (N.lt k) t -> forall_keys (N.lt k') t.
  Proof.
    Hint Resolve N.lt_trans.
    intros k k' t ineq H.
    induction t as [b l IHl [k'' v] r IHr|];
      hnf in *;
      intuition eauto.
  Qed.

  Theorem all_keys_smaller_chain :
    forall (k k':N) (t:avl_tree T),
      k < k' -> forall_keys (N.gt k) t -> forall_keys (N.gt k') t.
  Proof.
    Hint Resolve N.lt_trans.
    intros k k' t ineq H.
    induction t as [b l IHl [k'' v] r IHr|];
      hnf in *;
      rewrite_all N.gt_lt_iff;
      intuition eauto.
  Qed.

  Theorem all_keys_greater_chain_eq :
    forall (k k':N) (t:avl_tree T),
      k' <= k -> forall_keys (N.lt k) t -> forall_keys (N.lt k') t.
  Proof.
    Hint Resolve N.le_lt_trans.
    intros k k' t ineq H.
    induction t as [b l IH [k'' v] r IHr|]; simpl in *; intuition eauto.
  Qed.

  Lemma invert_tuple_eq :
    forall (A B:Type) (a a':A) (b b':B),
      (a,b) = (a',b') <-> a = a' /\ b = b'.
  Proof. split; inversion 1; subst; auto. Qed.

  Theorem forall_keys_In_iff :
    forall (P:N -> Prop) (t:avl_tree T),
      forall_keys P t <-> (forall p, In p t -> P (fst p)).
  Proof.
    intros P t. induction t as [b l IHl p r IHr|].
    - simpl. rewrite IHl. rewrite IHr. split; intuition (subst; eauto).
    - split; simpl; intuition auto.
  Qed.

  Fixpoint binary_tree_invariant (t:avl_tree T) : Prop :=
    match t with
      | avl_empty => True
      | avl_branch _ l p r =>
        forall_keys (N.gt (fst p)) l /\ forall_keys (N.lt (fst p)) r /\
        binary_tree_invariant l /\ binary_tree_invariant r
    end.
  Global Arguments binary_tree_invariant : default implicits.

  Fixpoint avl_invariant (t:avl_tree T) : Prop :=
    match t with
      | avl_empty => True
      | avl_branch _ l _ r =>
        (avl_height l = avl_height r \/ avl_height l = N.succ (avl_height r) \/ N.succ (avl_height l) = avl_height r)
        /\ avl_invariant l /\ avl_invariant r
    end.
  Global Arguments avl_invariant : default implicits.

  Definition balanced_with (b:sign) (l r:avl_tree T) : Prop :=
    match b with
      | positive => avl_height l = N.succ (avl_height r)
      | zero     => avl_height l = avl_height r
      | negative => N.succ (avl_height l) = avl_height r
    end.

  Fixpoint balance_correct (t:avl_tree T) : Prop :=
    match t with
      | avl_empty => True
      | avl_branch b l _ r => balanced_with b l r /\ balance_correct l /\ balance_correct r
    end.
  Global Arguments balance_correct : default implicits.

  Theorem balance_correct_implies_avl_invariant :
    forall (t:avl_tree T), balance_correct t -> avl_invariant t.
  Proof.
    intros t H. induction t as [b l IHl p r IHr|].
    - simpl in *. destruct b; simpl in *; tauto.
    - auto.
  Qed.

  (** Combination of all invariants that an AVL tree has to satisfy. *)
  Definition avl_tree_invariant (t:avl_tree T) : Prop :=
    balance_correct t /\ binary_tree_invariant t.
  Global Arguments avl_tree_invariant : default implicits.

  Theorem In_inv_left :
    forall (l r:avl_tree T) (k k':N) (v v':T),
      forall_keys (N.lt k') r -> k < k' ->
      ((k,v) = (k',v') \/ In (k,v) l \/ In (k,v) r) ->
      In (k,v) l.
  Proof.
    pose N.lt_irrefl as T1. pose N.lt_asymm as T2.
    intros l r k k' v v' r_all_gt k_lt H.
    destruct H as [H|[H|H]].
    - inversion H. subst k'. absurd (k < k); auto.
    - assumption.
    - rewrite forall_keys_In_iff in r_all_gt. apply r_all_gt in H.
      simpl in H. absurd (k < k'); auto.
  Qed.

  Theorem In_inv_right :
    forall (l r:avl_tree T) (k k':N) (v v':T),
      forall_keys (N.gt k') l -> k' < k ->
      ((k,v) = (k',v') \/ In (k,v) l \/ In (k,v) r) ->
      In (k,v) r.
  Proof.
    pose N.gt_lt as T1. pose N.lt_irrefl as T2. pose N.lt_asymm as T3.
    intros l r k k' v v' l_all_lt k_gt H. destruct H as [H|[H|H]].
    - inversion H. subst k'. absurd (k < k); auto.
    - rewrite forall_keys_In_iff in l_all_lt. apply l_all_lt in H.
      simpl in *. absurd (k < k'); auto.
    - assumption.
  Qed.

  Theorem In_inv_head :
    forall (l r:avl_tree T) (k:N) (v v':T),
      forall_keys (N.gt k) l /\ forall_keys (N.lt k) r ->
      ((k,v) = (k,v') \/ In (k,v) l \/ In (k,v) r) ->
      v = v'.
  Proof.
    pose N.gt_lt as T1. pose N.lt_irrefl as T2. pose N.lt_asymm as T3.
    intros l r k v v' [l_all_lt r_all_gt] H. destruct H as [H|[H|H]].
    - inversion H. auto.
    - rewrite forall_keys_In_iff in l_all_lt. apply l_all_lt in H.
      absurd (k < k); auto.
    - rewrite forall_keys_In_iff in r_all_gt. apply r_all_gt in H.
      absurd (k < k); auto.
  Qed.

End Invariants.

Section Node.

  Variable T : Type.

  (** Calculate the total balance change for this node from the height change 
   * of either the left or the right subtree. 
   * The returned balance change can be applied using [apply_balance_change].
   *)
  Let balance_change (a:sign + sign) : sign :=
    match a with
      | inl s  => s
      | inr s => sign_negate s
    end.

  (** Apply a balance change.
   * Returns the new balance if we don't need to do a rotation.
   * Otherwise, returns true if the left tree is higher or
     false if the right tree is higher.
   *)
  Let apply_balance_change (c:sign) (b:sign) : bool + sign :=
    match c with
      | negative =>
        match b with
          | negative => inl false
          | zero     => inr negative
          | positive => inr zero
        end
      | zero     => inr b
      | positive =>
        match b with
          | negative => inr zero
          | zero => inr positive
          | positive => inl true
        end
    end.

  (** Return the height change of the subtree (discarding which subtree changed). *)
  Let height_change (s:sign + sign) : sign := match s with | inr x => x | inl x => x end.

  (** Rotation for when the right subtree is higher *)
  Let rotate_right (removed:bool) (l:avl_tree T) (p:N * T) (r:avl_tree T)
  : avl_tree T * sign :=
    match r with
      | avl_branch positive (avl_branch rlb rll rlp rlr) rp rr =>
        ( avl_branch
            zero
            (avl_branch (if beq_sign rlb negative then positive else zero) l p rll)
            rlp
            (avl_branch (if beq_sign rlb positive then negative else zero) rlr rp rr)
          , if removed then negative else zero
        )
      | avl_branch b rl rp rr =>
        let b' := if beq_sign b zero then positive else zero in
        ( avl_branch
            b'
            (avl_branch (sign_negate b') l p rl)
            rp
            rr
          , if removed && beq_sign b negative then negative else zero
        )
      | avl_empty =>
        (* This branch should never happen, because if the right subtree has height zero,
         * it cannot be higher than the left subtree.
         * In this case, we still return the tree without doing a rotation, because that
         * way the invariant of the tree is preserved, which makes the proofs simpler.
         *)
        let b := match l with
                   | avl_empty => zero
                   | _ => positive
                 end
        in (avl_branch b l p r, zero)
    end.

  (** Rotation for when the left subtree is higher *)
  Let rotate_left (removed:bool) (l:avl_tree T) (p:N * T) (r:avl_tree T)
  : avl_tree T * sign :=
    match l with
      | avl_branch negative ll lp (avl_branch lrb lrl lrp lrr) =>
        ( avl_branch
            zero
            (avl_branch (if beq_sign lrb negative then positive else zero) ll lp lrl)
            lrp
            (avl_branch (if beq_sign lrb positive then negative else zero) lrr p r)
          , if removed then negative else zero
        )
      | avl_branch b ll lp lr =>
        let b' := if beq_sign zero b then negative else zero in
        ( avl_branch
            b'
            ll
            lp
            (avl_branch (sign_negate b') lr p r)
          , if removed && beq_sign b positive then negative else zero
        )
      | avl_empty =>
        (* See comment for this branch in [rotate_right] *)
        let b := match r with
                   | avl_empty => zero
                   | _         => negative
                 end
        in (avl_branch b avl_empty p r, zero)
    end.

  (* This function recreates a tree node after one of it's subtrees changed.
   *
   * Arguments:
   *
   * - [b] is the balance of the node before the change.
   * - [s] is either [inl c] or [inr c], where [c : sign] is the change in the height
   *   of the left or right subtree respectively (the other subtree's height must stay
   *   the same). [c] is positive if the height increased by 1, zero if it stayed the
   *   same or negative if it decreased by 1.
   * - [l] is the new left subtree.
   * - [p] is the value at the node (should be the same as before the change)
   * - [r] is the new right subtree
   *
   * Given these arguments, the function will compute the new balance and rebalance the
   * tree if necessary. It returns the new tree and the height change for the whole
   * new tree.
   *)
  Definition node (b:sign) (s:sign + sign) (l:avl_tree T) (p:N * T) (r:avl_tree T)
  : avl_tree T * sign :=
    if beq_sign (height_change s) zero
    then
      (* In this case, the subtree height did not change at all so the balance
       * stays the same.
       *)
      (avl_branch b l p r, zero)
    else let hd := height_change s in
       match apply_balance_change (balance_change s) b with
        | inl true  => rotate_left (beq_sign hd negative) l p r
        | inl false => rotate_right (beq_sign hd negative) l p r
        | inr b'    =>
          if beq_sign hd positive && beq_sign b' zero
          then
            (* The subtree height increased, but the balance is now zero. This means
             * that the height of the smaller subtree must have increased (if not, the
             * node would be unbalanced), so the height of the node did not change *)
            (avl_branch b' l p r, zero)
          else
            if beq_sign hd negative && negb (beq_sign b' zero)
            then
              (* The subtree height decreased, and the node's balance is not zero. This
               * means that the balance was zero before, and because we only change
               * one subtree, the height of the node cannot have changed if it is still
               * balanced.
               *)
              (avl_branch b' l p r, zero)
            else
              (* In all other cases, the change in the height of the node is the same
               * as the subtree height change.
               *)
              (avl_branch b' l p r, hd)
       end.
  Global Arguments node : default implicits.

  (** Proof that [rotate_left] preserves the binary_tree_invariant *)
  Lemma rotate_left_binary_tree_invariant :
    forall (b:bool) (p:N * T) (l r:avl_tree T),
      binary_tree_invariant l -> binary_tree_invariant r ->
      forall_keys (N.gt (fst p)) l -> forall_keys (N.lt (fst p)) r ->
      binary_tree_invariant (fst (rotate_left b l p r)).
  Proof.
    pose all_keys_smaller_chain as T1.
    pose all_keys_greater_chain as T2.
    intros b p l r bt_inv_l bt_inv_r l_smaller r_greater.
    destruct l as [lb ll lp lr|].
    - simpl. destruct lb; destruct lr as [lrb lrl lrp lrr|];
          simpl in *;
          rewrite_all N.gt_lt_iff;
          intuition eauto.
    - simpl. auto.
  Qed.

  (** Proof that [rotate_right] preserves the binary_tree_invariant *)
  Lemma rotate_right_binary_tree_invariant :
    forall (b:bool) (p:N * T) (l r:avl_tree T),
      binary_tree_invariant l -> binary_tree_invariant r ->
      forall_keys (N.gt (fst p)) l -> forall_keys (N.lt (fst p)) r ->
      binary_tree_invariant (fst (rotate_right b l p r)).
  Proof.
    pose all_keys_smaller_chain as T1.
    pose all_keys_greater_chain as T2.
    intros b p l r bt_inv_l bt_inv_r l_smaller r_greater.
    destruct r as [rb rl rp rr|].
    - simpl. destruct rb; destruct rl as [rlb rll rlp rlr|];
        simpl in *; simpl in *;
        rewrite_all N.gt_lt_iff; intuition eauto.
    - simpl. auto.
  Qed.

  (** Proof that the result of [rotate_left] contains exactly the same values as it's
   * input tree.
   *)
  Lemma rotate_left_same_elements :
    forall (b:bool) (p p':N * T) (l r:avl_tree T),
      In p' (avl_branch zero l p r) <->
      In p' (fst (rotate_left b l p r)).
  Proof.
    intros b p p' l r.
    destruct l as [lb ll lp lr|].
    - simpl. destruct lb;
        destruct lr as [lrb lrl lrp lrr|];
        simpl in *;
        intuition (subst; assumption || discriminate).
    - simpl. reflexivity.
  Qed.

  (** Like [rotate_left_same_elements], but for [rotate_right] *)
  Lemma rotate_right_same_elements :
    forall (b:bool) (p p':N * T) (l r:avl_tree T),
      In p' (avl_branch zero l p r) <->
      In p' (fst (rotate_right b l p r)).
  Proof.
    intros b p p' l r.
    destruct r as [rb rl rp rr|].
    - simpl. destruct rb;
        destruct rl as [rlb rll rlp rlr|];
        simpl in *;
        intuition (subst; assumption || discriminate).
    - simpl. reflexivity.
  Qed.

  (** Proof that [node] preserves the binary tree invariant. *)
  Theorem node_binary_tree_invariant :
    forall (b:sign) (s:sign + sign) (l r:avl_tree T) (p:N * T),
      binary_tree_invariant l -> binary_tree_invariant r ->
      forall_keys (N.gt (fst p)) l -> forall_keys (N.lt (fst p)) r ->
      binary_tree_invariant (fst (node b s l p r)).
  Proof.
    pose rotate_right_binary_tree_invariant as T1.
    pose rotate_left_binary_tree_invariant as T2.
    intros b s l p v bt_inv_l bt_inv_r l_smaller r_greater. unfold node.
    destruct s as [s|s]; destruct s; destruct b; simpl; auto.
  Qed.

  (** Proof that [node] doesn't change the elements that the tree contains. *)
  Theorem node_same_elements :
    forall (b:sign) (s:sign + sign) (l r:avl_tree T) (p p':N * T),
      p' = p \/ In p' l \/ In p' r <->
      In p' (fst (node b s l p r)).
  Proof.
    Hint Rewrite <- rotate_right_same_elements rotate_left_same_elements : core.
    intros b s l r p p'.
    destruct s as [s|s]; destruct s; destruct b; unfold node; simpl;
    autorewrite with core; simpl; split; trivial.
  Qed.

  (** Proof that node preserves forall_keys (this is the case since it preserves all
   * elements
   *)
  Lemma node_preserve_forall :
    forall (l r:avl_tree T) (p:N * T) (b:sign) (s:sign + sign) (P:N -> Prop),
      forall_keys P l -> forall_keys P r -> P (fst p) ->
      forall_keys P (fst (node b s l p r)).
  Proof.
    Hint Rewrite -> forall_keys_In_iff.
    Hint Rewrite <- node_same_elements.
    intros l r p b s P forall_l forall_r P_k.
    apply forall_keys_In_iff. intros. autorewrite with core in *.
    rewrite_all invert_tuple_eq. intuition (subst; simpl in *; eauto).
  Qed.

  (** This proposition states that the height change returned by a function matches
   * the real height change.
   *)
  Definition height_change_correct (c:sign) (t t':avl_tree T) : Prop :=
    match c with
      | negative => avl_height t = N.succ (avl_height t')
      | zero     => avl_height t = avl_height t'
      | positive => N.succ (avl_height t) = avl_height t'
    end.
  Global Arguments height_change_correct : default implicits.

  (** Proposition to state that either the left or the right subtree changed it's height
   * by the given amount. The other subtree must not have changed at all.
   *)
  Definition changed_height_in (s:sign + sign) (l l' r r':avl_tree T) : Prop :=
    match s with
      | inl c => r = r' /\ height_change_correct c l l'
      | inr c => l = l' /\ height_change_correct c r r'
    end.
  Global Arguments changed_height_in : default implicits.

  Lemma max_succ_id_r :
    forall (n:N), N.max n (N.succ n) = N.succ n.
  Proof.
    Hint Resolve N.le_succ_diag_r.
    intros n. rewrite N.max_r; auto.
  Qed.

  Lemma max_succ_id_l :
    forall (n:N), N.max (N.succ n) n = N.succ n.
  Proof.
    intros. rewrite N.max_comm. apply max_succ_id_r.
  Qed.

  Theorem rotate_right_balance_correct :
    forall (rem:bool) (l r:avl_tree T) (p:N * T),
      N.succ (N.succ (avl_height l)) = avl_height r ->
      balance_correct l -> balance_correct r ->
      balance_correct (fst (rotate_right rem l p r)).
  Proof.
    intros rem l r p heq bal_l bal_r.
    pose max_succ_id_l. pose max_succ_id_r.
    pose N.max_id. pose N.max_comm. pose N.max_assoc.
    destruct r as [rb rl rp rr|].
    - destruct bal_r as [rl_heq [bal_rl bal_rr]]. simpl in *. apply N.succ_inj in heq.
      destruct rb.
      + simpl in *. rewrite <- rl_heq in heq. rewrite max_succ_id_r in heq.
        apply N.succ_inj in heq. repeat split; congruence.
      + simpl in *. rewrite <- rl_heq in heq. rewrite N.max_id in heq.
        repeat split; congruence.
      + destruct rl as [rlb rll rlp rlr|].
        * simpl in *. apply N.succ_inj in rl_heq. rewrite_all <- rl_heq.
          rewrite max_succ_id_l in heq. apply N.succ_inj in heq.
          repeat split; destruct rlb; simpl in *; intuition congruence.
        * simpl in *. exfalso. apply N.neq_0_succ with (avl_height rr). tauto.
    - simpl in *. apply N.neq_succ_0 in heq. tauto.
  Qed.

  Theorem rotate_left_balance_correct :
    forall (rem:bool) (l r:avl_tree T) (p:N * T),
      N.succ (N.succ (avl_height r)) = avl_height l ->
      balance_correct l -> balance_correct r ->
      balance_correct (fst (rotate_left rem l p r)).
  Proof.
    intros rem l r p heq bal_l bal_r. pose max_succ_id_l. pose max_succ_id_r.
    pose N.max_id. pose N.max_comm. pose N.max_assoc.
    destruct l as [lb ll lp lr|].
    - destruct bal_l as [lr_heq [bal_ll bal_lr]]. simpl in *. apply N.succ_inj in heq.
      destruct lb.
      + destruct lr as [lrb lrl lrp lrr|].
        * simpl in *. apply N.succ_inj in lr_heq. rewrite_all <- lr_heq.
          rewrite max_succ_id_r in heq. apply N.succ_inj in heq.
          repeat split; destruct lrb; simpl in *; intuition congruence.
        * simpl in *. exfalso. apply N.neq_succ_0 with (avl_height ll). tauto.
      + simpl in *. rewrite <- lr_heq in heq. rewrite N.max_id in heq.
        repeat split; congruence.
      + simpl in *. rewrite lr_heq in heq. rewrite max_succ_id_l in heq.
        apply N.succ_inj in heq. repeat split; congruence.
    - simpl in *. apply N.neq_succ_0 in heq. contradiction.
  Qed.

  (** Proof that the tree returned by [node] has correct balance values. *)
  Theorem node_balance_correct :
    forall (l l' r r':avl_tree T) (p:N * T) (b:sign) (s:sign + sign),
      changed_height_in s l l' r r' ->
      balance_correct (avl_branch b l p r) ->
      balance_correct l' -> balance_correct r' ->
      balance_correct (fst (node b s l' p r')).
  Proof.
    intros l l' r r' p b s H bal_prev bal_l' bal_r'. unfold node.
    destruct s as [hd|hd];
      simpl in *;
      destruct b; destruct hd; simpl in *;
      try (apply rotate_right_balance_correct || apply rotate_left_balance_correct);
      repeat split;
      try (apply N.succ_inj);
      intuition congruence.
  Qed.

  Theorem rotate_left_rem_height_change_correct :
    forall (l r r':avl_tree T) (p:N * T),
      N.succ (N.succ (avl_height r')) = avl_height l ->
      avl_height r = N.succ (avl_height r') ->
      balance_correct l ->
      height_change_correct (snd (rotate_left true l p r'))
                            (avl_branch positive l p r)
                            (fst (rotate_left true l p r')).
  Proof.
    pose max_succ_id_r. pose N.max_comm. pose N.max_assoc. pose N.max_id.
    pose N.succ_inj_wd. pose max_succ_id_r. pose max_succ_id_l. pose N.succ_max_distr. 
    intros l r r' p l_heq r_heq bal_l. destruct l as [lb ll lp lr|].
    - simpl in *. destruct lb.
      + destruct lr as [lrb lrl lrp lrr|]; simpl in *; intuition congruence.
      + simpl in *. intuition congruence.
      + simpl in *. intuition congruence.
    - simpl in *. intuition congruence.
  Qed.

  Theorem rotate_right_rem_height_change_correct :
    forall (l l' r:avl_tree T) (p:N * T),
      N.succ (N.succ (avl_height l')) = avl_height r ->
      avl_height l = N.succ (avl_height l') ->
      balance_correct r ->
      height_change_correct (snd (rotate_right true l' p r))
                            (avl_branch negative l p r)
                            (fst (rotate_right true l' p r)).
  Proof.
    pose max_succ_id_r. pose N.max_comm. pose N.max_assoc. pose N.max_id.
    pose N.succ_inj_wd. pose max_succ_id_r. pose max_succ_id_l. pose N.succ_max_distr. 
    intros l l' r p l_heq r_heq bal_r. destruct r as [rb rl rp rr|].
    - simpl in *. destruct rb.
      + simpl in *. intuition congruence.
      + simpl in *. intuition congruence.
      + destruct rl as [rlb rll rlp rlr|]; simpl in *; intuition congruence.
    - simpl in *. intuition congruence.
  Qed.

  (** Proposition that the given tree is a result of an insertion that triggered 
   * a rotation operation. For example, an empty tree can never be a result of an
   * insert operation.
   *)
  Definition correct_for_insert (t:avl_tree T) : Prop :=
    match t with
      | avl_branch _ avl_empty _ avl_empty => True
      | avl_branch b l _ r => b <> zero
      | avl_empty          => False
    end.
  Global Arguments correct_for_insert : default implicits.

  Theorem rotate_left_ins_height_change_correct :
    forall (l l' r:avl_tree T) (p:N * T),
      N.succ (N.succ (avl_height r)) = avl_height l' ->
      avl_height l' = N.succ (avl_height l) ->
      correct_for_insert l' -> balance_correct l' ->
      height_change_correct (snd (rotate_left false l' p r))
                            (avl_branch positive l p r)
                            (fst (rotate_left false l' p r)).
  Proof.
    pose max_succ_id_r. pose max_succ_id_l. pose N.max_id. pose N.succ_max_distr. 
    pose N.max_comm. pose N.max_assoc. pose N.succ_inj_wd.
    intros l l' r p l'r_heq l_heq l'_c bal_l'.
    assert (lr_heq := l'r_heq). rewrite l_heq in lr_heq. apply N.succ_inj in lr_heq.
    destruct l' as [l'b l'l l'p l'r|].
    - destruct l'b.
      + destruct l'r as [l'rb l'rl l'rp l'rr|].
        * simpl in *; intuition congruence.
        * simpl in *. exfalso. apply N.neq_succ_0 with (avl_height l'l). tauto.
      + simpl in *. destruct l'l; destruct l'r.
        * exfalso. auto.
        * exfalso. auto.
        * exfalso. auto.
        * simpl in *. exfalso. rewrite N.one_succ in l'r_heq.
          apply N.succ_inj in l'r_heq. apply N.succ_0_discr in l'r_heq. auto.
      + simpl in *. intuition congruence.
    - simpl in *. intuition congruence.
  Qed.

  Theorem rotate_right_ins_height_change_correct :
    forall (l r r':avl_tree T) (p:N * T),
      N.succ (N.succ (avl_height l)) = avl_height r' ->
      avl_height r' = N.succ (avl_height r) ->
      correct_for_insert r' -> balance_correct r' ->
      height_change_correct (snd (rotate_right false l p r'))
                            (avl_branch positive l p r)
                            (fst (rotate_right false l p r')).
  Proof.
    pose max_succ_id_r. pose max_succ_id_l. pose N.max_id. pose N.succ_max_distr. 
    pose N.max_comm. pose N.max_assoc. pose N.succ_inj_wd.
    intros l r r' p lr'_heq r_heq r'_bal_nz bal_r'.
    destruct r' as [r'b r'l r'p r'r|].
    - destruct r'b.
      + simpl in *. intuition congruence.
      + simpl in *. destruct r'l; destruct r'r.
        * exfalso. auto.
        * exfalso. auto.
        * exfalso. auto.
        * simpl in *. rewrite N.one_succ in lr'_heq. apply N.succ_inj in lr'_heq.
          apply N.succ_0_discr in lr'_heq. contradiction.
      + destruct r'l as [r'lb r'll r'lp r'lr|].
        * simpl in *; intuition congruence.
        * simpl in *. exfalso. apply N.neq_0_succ with (avl_height r'r). tauto.
    - simpl in *. intuition congruence.
  Qed.

  (** Apply [correct_for_insert] only to the subtree which changed. *)
  Definition correct_for_insert_in (s:sign + sign) (l r:avl_tree T) : Prop :=
    match s with
      | inl positive => correct_for_insert l
      | inr positive => correct_for_insert r
      | _            => True
    end.
  
  Theorem node_height_change_correct :
    forall (b:sign) (s:sign + sign) (l l' r r':avl_tree T) (p:N * T),
      changed_height_in s l l' r r' ->
      correct_for_insert_in s l' r' ->
      balance_correct (avl_branch b l p r) -> balance_correct l' -> balance_correct r' ->
      height_change_correct (snd (node b s l' p r'))
                            (avl_branch b l p r)
                            (fst (node b s l' p r')).
  Proof.
    pose max_succ_id_r. pose max_succ_id_l. pose N.max_id. pose N.succ_max_distr. 
    pose N.max_comm. pose N.max_assoc. pose N.succ_inj_wd.
    intros b s l l' r r' p ch bal_nz_in bal_t bal_l' bal_r'.
    unfold node. destruct s as [hd|hd];
      destruct hd; destruct b; simpl in *;
      intuition (
          subst;
          try apply rotate_right_rem_height_change_correct;
          try apply rotate_right_ins_height_change_correct;
          try apply rotate_left_rem_height_change_correct;
          try apply rotate_left_ins_height_change_correct;
          congruence).
  Qed.

  Theorem rotate_right_correct_for_insert :
    forall (rem:bool) (l r:avl_tree T) (p:N * T),
      snd (rotate_right rem l p r) = positive ->
      correct_for_insert (fst (rotate_right rem l p r)).
  Proof.
    intros rem l r p H.
    destruct r as [rb rl rp rr|].
    - destruct rl as [rlb rll rlp rlr|]; destruct rem; destruct rb; simpl in *;
      discriminate.
    - discriminate.
  Qed.

  Theorem rotate_left_correct_for_insert :
    forall (rem:bool) (l r:avl_tree T) (p:N * T),
      snd (rotate_left rem l p r) = positive ->
      correct_for_insert (fst (rotate_left rem l p r)).
  Proof.
    intros rem l r p. destruct l as [lb ll lp lr|].
    - destruct rem; destruct lb; destruct lr; discriminate.
    - discriminate.
  Qed.

  Theorem node_correct_for_insert :
    forall (b:sign) (s:sign + sign) (l r:avl_tree T) (p:N * T),
      snd (node b s l p r) = positive ->
      correct_for_insert (fst (node b s l p r)).
  Proof.
    intros b s l r p H.
    pose rotate_right_correct_for_insert. pose rotate_left_correct_for_insert.
    unfold node in *.
    destruct s as [hd|hd]; destruct hd; destruct b; simpl in *;
    (destruct l; destruct r; discriminate || constructor) || auto.
  Qed.

  Theorem rotate_right_height_change_not_positive :
    forall (rem:bool) (l r:avl_tree T) (p:N * T),
      snd (rotate_right rem l p r) <> positive.
  Proof.
    intros rem l r p. unfold rotate_right.
    destruct r as [ [| |] [rlb rll rlp rlr|] rp rr|]; destruct rem; simpl in *;
    discriminate.
  Qed.

  Theorem rotate_left_height_change_not_positive :
    forall (rem:bool) (l r:avl_tree T) (p:N * T),
      snd (rotate_left rem l p r) <> positive.
  Proof.
    intros rem l r p. unfold rotate_left.
    destruct l as [ [| |] ll lp [lrb lrl lrp lrr|]|]; destruct rem; simpl in *;
    discriminate.
  Qed.

  Theorem rotate_right_ins_height_change_not_negative :
    forall (l r:avl_tree T) (p:N * T),
      snd (rotate_right false l p r) <> negative.
  Proof.
    intros l r p.
    destruct r as [ [| |] [rlb rll rlp rlr|] rp rr|]; simpl in *; discriminate.
  Qed.

  Theorem rotate_left_ins_height_change_not_negative :
    forall (l r:avl_tree T) (p:N * T),
      snd (rotate_left false l p r) <> negative.
  Proof.
    intros l r p.
    destruct l as [ [| |] ll lp [lrb lrl lrp lrr|]|]; simpl in *; discriminate.
  Qed.

  Theorem node_height_change_not_negated_left :
    forall (b:sign) (s:sign) (l r:avl_tree T) (p:N * T),
      s <> zero ->
      sign_negate s <> snd (node b (inl s) l p r).
  Proof.
    pose rotate_left_height_change_not_positive.
    pose rotate_right_height_change_not_positive.
    pose rotate_left_ins_height_change_not_negative.
    pose rotate_right_ins_height_change_not_negative.
    intros b s l r p. unfold node.
    destruct s; destruct b; simpl; auto; try discriminate.
  Qed.

  Theorem node_height_change_not_negated_right :
    forall (b:sign) (s:sign) (l r:avl_tree T) (p:N * T),
      s <> zero ->
      sign_negate s <> snd (node b (inr s) l p r).
  Proof.
    pose rotate_left_height_change_not_positive.
    pose rotate_right_height_change_not_positive.
    pose rotate_left_ins_height_change_not_negative.
    pose rotate_right_ins_height_change_not_negative.
    intros b s l r p. unfold node.
    destruct s; destruct b; simpl; auto; try discriminate.
  Qed.
  
End Node.

Section Insert.

  Variable T : Type.

  Fixpoint avl_insert_go (k:N) (v:T) (t:avl_tree T) : avl_tree T * sign :=
    match t with
      | avl_empty => (avl_branch zero avl_empty (k,v) avl_empty, positive)
      | avl_branch b l (k',v') r =>
        match N.compare k k' with
          | Eq => (avl_branch b l (k,v) r, zero)
          | Lt =>
            let (l', s) := avl_insert_go k v l
            in node b (inl s) l' (k',v') r
          | Gt =>
            let (r', s) := avl_insert_go k v r
            in node b (inr s) l (k',v') r'
        end
    end.

  Definition avl_insert (k:N) (v:T) (t:avl_tree T) : avl_tree T :=
    fst (avl_insert_go k v t).
  Global Arguments avl_insert : default implicits.

  Example avl_insert_ex1 :
    forall a b c : T,
      avl_insert 1 a (avl_insert 2 b (avl_insert 3 c avl_empty)) =
      avl_branch zero
                 (avl_branch zero avl_empty (1,a) avl_empty)
                 (2,b)
                 (avl_branch zero avl_empty (3,c) avl_empty).
  Proof. intros. unfold avl_insert. simpl. reflexivity. Qed.

  Example avl_insert_ex2 :
    forall a b c d : T,
      avl_insert 3 c (avl_insert 4 d (avl_insert 2 b (avl_insert 1 a avl_empty))) =
      avl_branch negative
                 (avl_branch zero avl_empty (1,a) avl_empty)
                 (2,b)
                 (avl_branch positive
                             (avl_branch zero avl_empty (3,c) avl_empty)
                             (4,d)
                             avl_empty).
  Proof. intros. reflexivity. Qed.

  Example avl_insert_ex3 :
    forall a b c d : T,
      avl_insert 3 c (avl_insert 2 b (avl_insert 4 d (avl_insert 1 a avl_empty))) =
      avl_insert 3 c (avl_insert 4 d (avl_insert 2 b (avl_insert 1 a avl_empty))).
  Proof. intros. reflexivity. Qed.

  Theorem insert_In :
    forall (k:N) (v:T) (t:avl_tree T),
      In (k,v) (avl_insert k v t).
  Proof.
    Hint Resolve -> node_same_elements.
    intros k v t. induction t as [b l IHl [k' v'] r IHr|].
    - unfold avl_insert in *. simpl. destruct (N.compare k k').
      + simpl. tauto.
      + destruct (avl_insert_go k v l). auto.
      + destruct (avl_insert_go k v r). auto.
    - simpl. auto.
  Qed.

  Theorem insert_preserve_other :
    forall (k k':N) (v v':T) (t:avl_tree T),
      k <> k' -> (In (k,v) t <-> In (k,v) (avl_insert k' v' t)).
  Proof.
    Hint Rewrite invert_tuple_eq : core.
    Hint Rewrite <- node_same_elements : core.
    intros k k' v v' t ineq. induction t as [b l IHl [k'' v''] r IHr|].
    - unfold avl_insert in *. simpl. destruct (N.compare k' k'') eqn:E.
      + apply N.compare_eq_iff in E. subst k''. simpl. rewrite_all invert_tuple_eq.
        split; intuition (assumption || (exfalso; auto)).
      + destruct (avl_insert_go k' v' l). simpl in *.
        autorewrite with core. rewrite IHl. reflexivity.
      + destruct (avl_insert_go k' v' r). simpl in *.
        autorewrite with core. rewrite IHr. reflexivity.
    - simpl. autorewrite with core. intuition auto.
  Qed.

  Theorem insert_forall_keys :
    forall (k:N) (v:T) (t:avl_tree T) (P:N -> Prop),
      forall_keys P t -> P k -> forall_keys P (avl_insert k v t).
  Proof.
    Hint Resolve <- insert_preserve_other.
    setoid_rewrite forall_keys_In_iff. intros k v t P forall_t for_P [k' v'].
    destruct (N.eq_dec k k'); subst; eauto.
  Qed.

  Theorem insert_binary_tree_invariant :
    forall (k:N) (v:T) (t:avl_tree T),
      binary_tree_invariant t -> binary_tree_invariant (avl_insert k v t).
  Proof.
    Hint Resolve node_binary_tree_invariant insert_forall_keys.
    Hint Resolve -> N.gt_lt_iff.
    Hint Resolve <- N.gt_lt_iff.
    intros k v t bt_inv_t. induction t as [b l IHl [k' v'] r IHr|].
    - unfold avl_insert in *. simpl. destruct (N.compare_spec k k') as [C|C|C].
      + simpl in *. subst k'. auto.
      + destruct (avl_insert_go k v l) as [a s] eqn:X.
        replace a with (avl_insert k v l) in * by (unfold avl_insert; rewrite X; auto).
        simpl in *. intuition auto.
      + destruct (avl_insert_go k v r) as [a s] eqn:X.
        replace a with (avl_insert k v r) in * by (unfold avl_insert; rewrite X; auto).
        simpl in *. intuition auto.
    - simpl. auto.
  Qed.

  Theorem insert_correct_for_insert :
    forall (k:N) (v:T) (t:avl_tree T),
      snd (avl_insert_go k v t) = positive ->
      correct_for_insert (fst (avl_insert_go k v t)).
  Proof.
    intros k v t hd_eq. destruct t as [b l [k' v'] r|].
    - simpl in *. destruct (N.compare_spec k k') as [H|H|H].
      + discriminate.
      + destruct (avl_insert_go k v l) eqn:go_eq. apply node_correct_for_insert.
        assumption.
      + destruct (avl_insert_go k v r) eqn:go_eq. apply node_correct_for_insert.
        assumption.
    - simpl in *. constructor.
  Qed.

  Theorem insert_balance_and_height_correct :
    forall (k:N) (v:T) (t:avl_tree T),
      balance_correct t ->
      balance_correct (fst (avl_insert_go k v t)) /\
      height_change_correct (snd (avl_insert_go k v t))
                            t
                            (fst (avl_insert_go k v t)).
  Proof.
    intros k v t bal_t. unfold avl_insert. induction t as [b l IHl [k' v'] r IHr|].
    - simpl in *. destruct (N.compare_spec k k') as [H|H|H].
      + simpl. tauto.
      + destruct (avl_insert_go k v l) as [l' s] eqn:go_eq. split.
        * apply node_balance_correct with (l := l) (r := r); simpl; tauto.
        * assert (s = positive -> correct_for_insert l').
          { replace l' with (fst (l', s)) by reflexivity.
            rewrite <- go_eq. intros. apply insert_correct_for_insert. rewrite go_eq.
            auto.
          } 
          apply node_height_change_correct; simpl; destruct s; tauto.
      + destruct (avl_insert_go k v r) as [r' s] eqn:go_eq. split.
        * apply node_balance_correct with (l := l) (r := r); simpl; tauto.
        * assert (s = positive -> correct_for_insert r').
          { replace r' with (fst (r', s)) by reflexivity.
            rewrite <- go_eq. intros. apply insert_correct_for_insert. rewrite go_eq.
            auto.
          }
          apply node_height_change_correct; simpl; destruct s; tauto.
    - simpl. auto.
  Qed.

  Theorem insert_balance_correct :
    forall (k:N) (v:T) (t:avl_tree T),
      balance_correct t -> balance_correct (avl_insert k v t).
  Proof.
    intros k v t H. eapply proj1. eapply insert_balance_and_height_correct. assumption.
  Qed.

  Theorem insert_avl_invariant :
    forall (k:N) (v:T) (t:avl_tree T),
      balance_correct t -> avl_invariant (avl_insert k v t).
  Proof.
    intros k v t H.
    destruct insert_balance_and_height_correct with (k := k) (v := v) (t := t).
    - assumption.
    - apply balance_correct_implies_avl_invariant. unfold avl_insert. auto.
  Qed.
  
  Theorem insert_In_inv :
    forall (t:avl_tree T) (k:N) (v v':T),
      binary_tree_invariant t -> In (k, v') (avl_insert k v t) -> v = v'.
  Proof.
    pose N.gt_lt as T1. pose N.lt_irrefl as T2. pose N.lt_gt as T3.
    intros t k v v' bt_inv H. unfold avl_insert in H.
    induction t as [b l IHl [k'' v''] r IHr|].
    - simpl in *.
      destruct (N.compare_spec k k'') as [C|C|C].
      + simpl in *. subst k''. apply In_inv_head in H; intuition eauto.
      + destruct (avl_insert_go k v l) as [l' s] eqn:go_eq.
        rewrite <- node_same_elements in H.
        simpl in *.
        apply In_inv_left in H; intuition eauto.
      + destruct (avl_insert_go k v r) as [r' s] eqn:go_eq.
        rewrite <- node_same_elements in H.
        simpl in *.
        apply In_inv_right in H; intuition eauto.
    - simpl in *. destruct H as [H|[H|H]]; inversion H; auto.
  Qed.

End Insert.

Section Minimum.
  Variable T : Type.

  Fixpoint avl_find_minimum (t:avl_tree T) (def:N * T): (N * T) :=
    match t with
      | avl_empty => def
      | avl_branch lb ll lp lr => avl_find_minimum ll lp
    end.
  Global Arguments avl_find_minimum : default implicits.

  Example avl_find_minimum_ex1 :
    forall a b c d : T,
      avl_find_minimum
        (avl_insert 1 a (avl_insert 2 b (avl_insert 3 c (avl_insert 4 d avl_empty))))
        (5,d)
      = (1,a).
  Proof. intros. reflexivity. Qed.

  Theorem avl_find_minimum_In :
    forall (t:avl_tree T) (def:N * T),
      In (avl_find_minimum t def) t \/ avl_find_minimum t def = def.
  Proof.
    intros t. induction t as [b l IHl p r IHr|].
    - intros def. clear IHr. specialize IHl with p. simpl in *. intuition eauto.
    - intros. simpl. tauto.
  Qed.

  Theorem avl_find_minimum_is_min :
    forall (t:avl_tree T) (def:N * T),
      binary_tree_invariant t ->
      forall_keys (N.le (fst (avl_find_minimum t def))) t.
  Proof.
    intros t def bt_inv. pose N.gt_lt as T1. pose N.lt_le_incl as T2.
    generalize dependent def. induction t as [b l IHl p r IHr|].
    - intros def. clear IHr. simpl. specialize IHl with p. destruct p as [k v].
      simpl in *.
      assert (min_le_k: fst (avl_find_minimum l (k,v)) <= k).
      {
        destruct avl_find_minimum_In with (t := l) (def := (k,v)) as [H|H].
        - rewrite_all forall_keys_In_iff. intuition eauto.
        - rewrite H. reflexivity.
      }
      repeat split.
      + auto.
      + intuition auto.
      + rewrite_all forall_keys_In_iff. intros p in_r. rewrite min_le_k. intuition eauto.
    - simpl. auto.
  Qed.

  Fixpoint avl_remove_minimum_go (b:sign) (l:avl_tree T) (p:N * T) (r:avl_tree T)
  : (avl_tree T * sign) :=
    match l with
      | avl_empty => (r, negative)
      | avl_branch lb ll lp lr =>
        let (l',s) := avl_remove_minimum_go lb ll lp lr
        in node b (inl s) l' p r
    end.
  Global Arguments avl_remove_minimum_go : default implicits.

  Theorem avl_remove_minimum_go_preserve_other :
    forall (l:avl_tree T) (p':N * T) (b:sign) (p:N * T) (r:avl_tree T),
      p' = p \/ In p' l \/ In p' r <->
      (In p' (fst (avl_remove_minimum_go b l p r)) \/ p' = avl_find_minimum l p).
  Proof.
    intros l p'. induction l as [lb ll IHll lp lr IHlr|].
    - intros b p r. simpl in *.
      destruct (avl_remove_minimum_go lb ll lp lr) as [l' s] eqn:rec_eq.
      rewrite <- node_same_elements.
      replace l' with (fst (l', s)) by reflexivity. rewrite <- rec_eq.
      rewrite IHll with (b := lb). tauto.
    - intros. simpl. tauto.
  Qed.

  Theorem avl_remove_minimum_go_subset :
    forall (l:avl_tree T) (p':N * T) (b:sign) (p:N * T) (r:avl_tree T),
      In p' (fst (avl_remove_minimum_go b l p r)) -> p' = p \/ In p' l \/ In p' r.
  Proof.
    intros l p'. induction l as [lb ll IHll lp lr IHlr|].
    - intros b p r. clear IHlr. specialize IHll with lb lp lr. simpl in *.
      destruct (avl_remove_minimum_go lb ll lp lr) as [l' s] eqn:rec_eq.
      replace l' with (fst (l',s)) by reflexivity.
      rewrite <- node_same_elements. intuition auto.
    - intros. simpl. auto.
  Qed.

  Theorem avl_remove_minimum_go_preserve_forall :
    forall (P:N -> Prop) (b:sign) (l:avl_tree T) (p:N * T) (r:avl_tree T),
      P (fst p) /\ forall_keys P l /\ forall_keys P r ->
      forall_keys P (fst (avl_remove_minimum_go b l p r)).
  Proof.
    pose avl_remove_minimum_go_subset as T1.
    intros. rewrite_all forall_keys_In_iff. intros p' in_rm.
    apply avl_remove_minimum_go_subset in in_rm. intuition (subst; eauto).
  Qed.

  Theorem avl_remove_minimum_go_binary_tree_invariant:
    forall (l:avl_tree T) (b:sign) (p:N * T) (r:avl_tree T),
      binary_tree_invariant (avl_branch b l p r) ->
      binary_tree_invariant (fst (avl_remove_minimum_go b l p r)).
  Proof.
    pose node_binary_tree_invariant as T1.
    pose avl_remove_minimum_go_preserve_forall as T2.
    intros l. induction l as [lb ll IHll lp lr IHlr|].
    - intros b p r bt_inv. simpl in *. clear IHlr. specialize IHll with lb lp lr.
      simpl in *. destruct p as [k v]. destruct lp as [lk lv].
      destruct (avl_remove_minimum_go lb ll (lk,lv) lr) as [l' s] eqn:min_eq.
      replace l' with (fst (l',s)) by reflexivity. rewrite_all <- min_eq.
      intuition eauto.
    - intros b [k v] r. simpl in *. tauto.
  Qed.

  Theorem avl_remove_minimum_go_min_not_In :
    forall (l:avl_tree T) (b:sign) (p:N * T) (r:avl_tree T),
      binary_tree_invariant (avl_branch b l p r) ->
      ~In (avl_find_minimum l p) (fst (avl_remove_minimum_go b l p r)).
  Proof.
    pose N.gt_lt as T1.
    intros l. induction l as [lb ll IHll lp lr IHlr|].
    - intros b p r bt_inv H. simpl in *.
      destruct (avl_remove_minimum_go lb ll lp lr) as [l' s] eqn:rec_eq.
      rewrite <- node_same_elements in H. specialize IHll with lb lp lr.
      clear IHlr. replace l' with (fst (l', s)) in H by reflexivity.
      rewrite_all <- rec_eq. rewrite_all forall_keys_In_iff. destruct H as [H|[H|H]].
      + destruct avl_find_minimum_In with (t := ll) (def := lp) as [P|P].
        * apply N.lt_irrefl with (x := fst p). subst. intuition eauto.
        * apply N.lt_irrefl with (x := fst p). rewrite_all P. subst. intuition auto.
      + apply IHll; intuition eauto.
      + destruct avl_find_minimum_In with (t := ll) (def := lp) as [P|P].
        * apply N.lt_asymm with (n := fst p) (m := fst (avl_find_minimum ll lp));
            intuition eauto.
        * rewrite_all P. apply N.lt_asymm with (n := fst lp) (m := fst p);
            intuition eauto.
    - intros b p r inv_bt H. simpl in *. rewrite_all forall_keys_In_iff.
      apply N.lt_irrefl with (x := fst p). intuition eauto.
  Qed.

  Theorem avl_remove_minimum_go_removes_minimum :
    forall (l:avl_tree T) (min_k:N) (b:sign) (p:N * T) (r:avl_tree T),
      binary_tree_invariant (avl_branch b l p r) ->
      forall_keys (N.le min_k) (avl_branch b l p r) ->
      forall_keys (N.lt min_k) (fst (avl_remove_minimum_go b l p r)).
  Proof.
    pose all_keys_greater_chain_eq as T1. pose all_keys_greater_chain as T2.
    pose N.le_lt_trans as T3. pose node_preserve_forall as T4. pose N.gt_lt as T5.
    intros l min_k. induction l as [lb ll IHll lp lr IHlr|].
    - intros b p r bt_inv H. simpl in *. clear IHlr. specialize IHll with lb lp lr.
      destruct (avl_remove_minimum_go lb ll lp lr) as [l' s] eqn:rec_eq.
      replace l' with (fst (l', s)) by reflexivity. rewrite_all <- rec_eq.
      intuition eauto.
    - intros. simpl in *. intuition eauto.
  Qed.

  Theorem avl_remove_minimum_go_all_greater :
    forall (l:avl_tree T) (b:sign) (p:N * T) (r:avl_tree T),
      binary_tree_invariant (avl_branch b l p r) ->
      forall_keys (N.lt (fst (avl_find_minimum l p)))
                  (fst (avl_remove_minimum_go b l p r)).
  Proof.
    pose all_keys_greater_chain_eq as T1. pose all_keys_greater_chain as T2.
    pose N.le_lt_trans as T3. pose node_preserve_forall as T4. pose N.gt_lt as T5.
    pose N.lt_le_incl as T6.
    intros l b p r bt_inv. apply avl_remove_minimum_go_removes_minimum.
    - assumption.
    - simpl.
      destruct avl_find_minimum_In with (t := l) (def := p) as [H|H].
      + simpl in *. repeat split.
        * rewrite_all forall_keys_In_iff. intuition eauto.
        * apply avl_find_minimum_is_min. tauto.
        * rewrite_all forall_keys_In_iff.
          assert (pk_gt: fst (avl_find_minimum l p) <= fst p) by intuition eauto.
          intros p' in_r. intuition eauto.
      + simpl in *. rewrite_all H. repeat split.
        * reflexivity.
        * rewrite <- H. apply avl_find_minimum_is_min. tauto.
        * rewrite_all forall_keys_In_iff. intros p' in_r. intuition eauto.
  Qed.

  Theorem avl_remove_minimum_go_height_change_not_positive :
    forall (l:avl_tree T) (b:sign) (p:N * T) (r:avl_tree T),
      positive <> snd (avl_remove_minimum_go b l p r).
  Proof.
    pose node_height_change_not_negated_left as NHL.
    pose node_height_change_not_negated_right as NHR.
    intros l. induction l as [b' l' IHl' p' r' _|].
    - specialize IHl' with b' p' r'. intros b p r. simpl.
      destruct (avl_remove_minimum_go b' l' p' r') as [l'' s] eqn:go_eq.
      specialize NHL with T b s l'' r p.
      specialize NHR with T b s l'' r p.
      simpl in *. destruct s; intuition (discriminate || eauto).
    - intros. simpl. discriminate.
  Qed.

  Theorem avl_remove_minimum_go_balance_and_height_change_correct :
    forall (l:avl_tree T) (b:sign) (p:N * T) (r:avl_tree T),
      balance_correct (avl_branch b l p r) ->
      balance_correct (fst (avl_remove_minimum_go b l p r)) /\
      height_change_correct (snd (avl_remove_minimum_go b l p r))
                            (avl_branch b l p r)
                            (fst (avl_remove_minimum_go b l p r)).
  Proof.
    intros l. induction l as [b' l' IHl' p' r' IHr'|].
    - intros b p r bal_t. clear IHr'. specialize IHl' with b' p' r'.
      simpl. destruct (avl_remove_minimum_go b' l' p' r') as [l'' s] eqn:go_eq.
      assert (s_not_positive: positive <> s).
      { replace s with (snd (l'', s)) by reflexivity.
        rewrite <- go_eq. apply avl_remove_minimum_go_height_change_not_positive.
      }
      split.
      + apply node_balance_correct with (avl_branch b' l' p' r') r; simpl in *; tauto.
      + apply node_height_change_correct; destruct s; simpl in *;
        intuition (contradiction || tauto).
    - intros. simpl in *. rewrite N.max_0_l. tauto.
  Qed.

  Theorem avl_remove_minimum_go_height_change_correct :
    forall (l r:avl_tree T) (b:sign) (p:N * T) (r:avl_tree T),
      balance_correct (avl_branch b l p r) ->
      height_change_correct (snd (avl_remove_minimum_go b l p r))
                            (avl_branch b l p r)
                            (fst (avl_remove_minimum_go b l p r)).
  Proof.
    pose avl_remove_minimum_go_balance_and_height_change_correct as H.
    intros. edestruct H; eassumption.
  Qed.

  Theorem avl_remove_minimum_go_balance_correct :
    forall (l r:avl_tree T) (b:sign) (p:N * T) (r:avl_tree T),
      balance_correct (avl_branch b l p r) ->
      balance_correct (fst (avl_remove_minimum_go b l p r)).
  Proof.
    intros.
    edestruct avl_remove_minimum_go_balance_and_height_change_correct; eassumption.
  Qed.

End Minimum.

Section Remove.
  Variable T : Type.

  Definition avl_remove_top (b:sign) (l:avl_tree T) (r:avl_tree T) : avl_tree T * sign :=
    match r with
      | avl_empty => (l, negative)
      | avl_branch rb rl rp rr =>
        let (r',s) := avl_remove_minimum_go rb rl rp rr
        in node b (inr s) l (avl_find_minimum rl rp) r'
    end.

  Theorem avl_remove_top_preserve_other :
    forall (b:sign) (l:avl_tree T) (r:avl_tree T) (p:N * T),
      (In p r \/ In p l) <-> In p (fst (avl_remove_top b l r)).
  Proof.
    intros b l r p. destruct r as [rb rl rp rr|] eqn:r_eq.
    - simpl. destruct (avl_remove_minimum_go rb rl rp rr) as [r' s] eqn:rm_min_eq.
      replace r' with (fst (r',s)) by reflexivity. rewrite <- rm_min_eq.
      rewrite <- node_same_elements.
      rewrite avl_remove_minimum_go_preserve_other with (b := rb).
      tauto.
    - subst. simpl. tauto.
  Qed.

  Theorem avl_remove_top_binary_tree_invariant :
    forall (b:sign) (l:avl_tree T) (r:avl_tree T) (k:N),
      forall_keys (N.gt k) l -> forall_keys (N.lt k) r ->
      binary_tree_invariant l -> binary_tree_invariant r ->
      binary_tree_invariant (fst (avl_remove_top b l r)).
  Proof.
    pose node_binary_tree_invariant as T1.
    pose avl_remove_minimum_go_binary_tree_invariant as T2.
    pose avl_remove_minimum_go_subset as T3.
    pose N.gt_lt as T4.
    intros b l r k k_gt_l k_lt_r bt_inv_l bt_inv_r. destruct r as [rb rl rp rr|].
    - simpl in *. destruct (avl_remove_minimum_go rb rl rp rr) as [r' s] eqn:rm_min_eq.
      replace r' with (fst (r', s)) by reflexivity. rewrite_all <- rm_min_eq.
      apply node_binary_tree_invariant.
      + intuition auto.
      + apply avl_remove_minimum_go_binary_tree_invariant. simpl. intuition auto.
      + destruct avl_find_minimum_In with T rl rp as [H|H].
        * rewrite_all forall_keys_In_iff. intros p' in_l.
          apply N.lt_gt. apply N.lt_trans with k; intuition eauto.
        * rewrite H. apply all_keys_smaller_chain with k; intuition eauto.
      + apply avl_remove_minimum_go_all_greater. simpl. intuition eauto.
    - simpl in *. auto.
  Qed.

  Lemma height_change_correct_change_branch_value :
    forall (t l r l' r':avl_tree T) (c b:sign) (p p':N * T),
      height_change_correct c (avl_branch b l' p r') t <->
      height_change_correct c (avl_branch b l' p' r') t.
  Proof.
    intros. destruct c; simpl; reflexivity.
  Qed.
                            

  Theorem avl_remove_top_balance_and_height_correct :
    forall (b:sign) (l:avl_tree T) (r:avl_tree T) (p:N * T) ,
      balance_correct (avl_branch b l p r) ->
      balance_correct (fst (avl_remove_top b l r)) /\
      height_change_correct (snd (avl_remove_top b l r))
                            (avl_branch b l p r)
                            (fst (avl_remove_top b l r)).
  Proof.
    pose avl_remove_minimum_go_height_change_correct as T1.
    pose avl_remove_minimum_go_balance_correct as T2.
    pose node_balance_correct as T3.
    pose node_height_change_correct as T4.
    intros b l r p bal_t. destruct r as [rb rl rp rr|].
    - simpl in *. destruct (avl_remove_minimum_go rb rl rp rr) as [r' s] eqn:min_eq.
      rewrite surjective_pairing in min_eq at 1. inversion min_eq as [[r'_eq s_eq]].
      split.
      + apply node_balance_correct with l (avl_branch rb rl rp rr); simpl in *;
        intuition auto.
      + rewrite height_change_correct_change_branch_value.
        assert (positive <> s)
          by (subst s; apply avl_remove_minimum_go_height_change_not_positive).
        apply T4.
        * simpl. intuition auto.
        * simpl. rewrite s_eq. destruct s; constructor || (exfalso; auto).
        * simpl. tauto.
        * simpl. tauto.
        * simpl. intuition auto.
        * tauto.
        * tauto.
    - simpl in *. rewrite N.max_0_r. tauto.
  Qed.

  Theorem avl_remove_top_height_change_not_positive :
    forall (b:sign) (l r:avl_tree T),
      positive <> snd (avl_remove_top b l r).
  Proof.
    intros b l r. destruct r as [rb rl rp rr|].
    - simpl in *. destruct (avl_remove_minimum_go rb rl rp rr) as [r' s] eqn:min_eq.
      replace positive with (sign_negate negative) by reflexivity.
      assert (s_not_positive: positive <> s).
      { replace s with (snd (r', s)) by reflexivity.
        rewrite <- min_eq. apply avl_remove_minimum_go_height_change_not_positive.
      }
      destruct s.
      + apply node_height_change_not_negated_right. discriminate.
      + simpl. discriminate.
      + exfalso. auto.
    - simpl. discriminate.
  Qed.

  Fixpoint avl_remove_go (k:N) (t:avl_tree T) : avl_tree T * sign :=
    match t with
      | avl_empty => (avl_empty, zero)
      | avl_branch b l (k',v') r =>
        match N.compare k k' with
          | Lt => let (l',s) := avl_remove_go k l in node b (inl s) l' (k',v') r
          | Gt => let (r',s) := avl_remove_go k r in node b (inr s) l (k',v') r'
          | Eq => avl_remove_top b l r
        end
    end.

  Definition avl_remove (k:N) (t:avl_tree T) : avl_tree T := fst (avl_remove_go k t).
  Global Arguments avl_remove : default implicits.


  Example avl_remove_ex1 :
    forall a b c : T,
      avl_remove 2 (avl_insert 1 a (avl_insert 2 b (avl_insert 3 c avl_empty))) =
      avl_branch positive (avl_insert 1 a avl_empty) (3,c) avl_empty.
  Proof. reflexivity. Qed.

  Example avl_remove_ex2 :
    forall a b c d : T,
      avl_remove
        2
        (avl_insert 3 c (avl_insert 4 d (avl_insert 2 b (avl_insert 1 a avl_empty)))) =
      avl_insert 1 a (avl_insert 4 d (avl_insert 3 c avl_empty)).
  Proof. reflexivity. Qed.

  Example avl_remove_ex3 :
    forall a b c d e f g h : T,
      avl_remove
        4
        (avl_branch
           positive
           (avl_branch
              positive
              (avl_branch
                 zero
                 (avl_singleton 1 a)
                 (2,b)
                 (avl_singleton 3 c))
              (4,d)
              (avl_singleton 5 e))
           (6,f)
           (avl_branch negative avl_empty (7,g) (avl_singleton 8 h)))
      = avl_branch
          positive
          (avl_branch
             negative
             (avl_singleton 1 a)
             (2,b)
             (avl_branch positive (avl_singleton 3 c) (5,e) avl_empty))
          (6,f)
          (avl_branch negative avl_empty (7,g) (avl_singleton 8 h)).
  Proof. reflexivity. Qed.

  Theorem remove_not_In :
    forall k v t,
      binary_tree_invariant t ->
      ~In (k,v) (avl_remove k t).
  Proof.
    pose N.le_lt_trans as T1. pose N.gt_lt as T2. pose N.lt_le_incl as T3.
    pose N.lt_irrefl as T4. pose N.lt_le_trans as T5. pose N.lt_gt as T6.
    intros k v t bt_inv_t. induction t as [b l IHl p r IHr|].
    - unfold avl_remove. simpl. destruct p as [k' v'] eqn:peq.
      destruct (N.compare_spec k k') as [C|C|C].
      + intros H. rewrite <- avl_remove_top_preserve_other in H. simpl in *.
        rewrite_all forall_keys_In_iff. subst k. apply N.lt_irrefl with k'.
        replace k' with (fst (k', v)) by reflexivity. intuition eauto.
      + destruct (avl_remove_go k l) as [l' s] eqn:rec_eq.
        replace l' with (fst (l', s)) by reflexivity.
        rewrite <- rec_eq. unfold avl_remove in *. rewrite <- node_same_elements.
        rewrite invert_tuple_eq. intros H. unfold not in *. simpl in *.
        rewrite_all forall_keys_In_iff.
        intuition (subst; eauto).
      + destruct (avl_remove_go k r) as [r' s] eqn:rec_eq.
        replace r' with (fst (r',s)) by reflexivity.
        rewrite <- rec_eq. unfold avl_remove in *. rewrite <- node_same_elements.
        rewrite invert_tuple_eq. intros H. unfold not in *. simpl in *.
        rewrite_all forall_keys_In_iff.
        intuition (subst; (eapply N.lt_irrefl; eauto) || eauto).
    - simpl. auto.
  Qed.

  Theorem remove_preserve_other :
    forall (p:N * T) (k:N) (t:avl_tree T),
      (In p t <-> (In p (avl_remove k t) \/ (fst p = k /\ In p t))).
  Proof.
    intros. unfold avl_remove. induction t as [b l IHl [k' v'] r IHr|].
    - simpl. destruct (N.compare_spec k k') as [C|C|C].
      + rewrite <- avl_remove_top_preserve_other.
        split; intuition (subst; auto).
      + destruct (avl_remove_go k l) as [l' s] eqn:rec_eq.
        rewrite <- node_same_elements. replace l' with (fst (l', s)) by reflexivity.
        rewrite IHl. tauto.
      + destruct (avl_remove_go k r) as [r' s] eqn:rec_eq.
        rewrite <- node_same_elements. replace r' with (fst (r', s)) by reflexivity.
        rewrite IHr. tauto.
    - simpl. tauto.
  Qed.

  Theorem remove_subset :
    forall (p:N * T) (k:N) (t:avl_tree T),
      In p (avl_remove k t) -> In p t.
  Proof.
    intros. rewrite remove_preserve_other with (k := k). tauto.
  Qed.

  Theorem remove_preserve_forall :
    forall (P:N -> Prop) (k:N) (t:avl_tree T),
      forall_keys P t -> forall_keys P (avl_remove k t).
  Proof.
    Hint Resolve remove_subset.
    intros P k t H. rewrite_all forall_keys_In_iff. intros p in_rm.
    eauto.
  Qed.

  Theorem remove_binary_tree_invariant :
    forall (k:N) (t:avl_tree T),
      binary_tree_invariant t -> binary_tree_invariant (avl_remove k t).
  Proof.
    Hint Resolve avl_remove_top_binary_tree_invariant node_binary_tree_invariant
         remove_preserve_forall.
    intros k t bt_inv. unfold avl_remove. induction t as [b l IHl [k' v'] r IHr|].
    - simpl. destruct (N.compare_spec k k') as [C|C|C].
      + subst k'. simpl in *. intuition eauto.
      + destruct (avl_remove_go k l) as [l' s] eqn:rec_eq.
        replace l' with (fst (l', s)) by reflexivity. rewrite_all <- rec_eq.
        simpl in *. fold (avl_remove k l) in *. intuition eauto.
      + destruct (avl_remove_go k r) as [r' s] eqn:rec_eq.
        replace r' with (fst (r', s)) by reflexivity. rewrite_all <- rec_eq.
        simpl in *. fold (avl_remove k r) in *. intuition eauto.
    - simpl. constructor.
  Qed.

  Theorem remove_height_change_not_positive :
    forall (k:N) (t:avl_tree T),
      positive <> snd (avl_remove_go k t).
  Proof.
    intros k t. induction t as [b l IHl [k' v'] r IHr|].
    - simpl. destruct (N.compare_spec k k') as [C|C|C].
      + simpl. apply avl_remove_top_height_change_not_positive.
      + destruct (avl_remove_go k l) as [l' s] eqn:go_eq.
        simpl in *.
        replace positive with (sign_negate negative) by reflexivity.
        destruct s.
        * apply node_height_change_not_negated_left. discriminate.
        * simpl. discriminate.
        * exfalso. auto.
      + destruct (avl_remove_go k r) as [r' s] eqn:go_eq.
        simpl in *.
        replace positive with (sign_negate negative) by reflexivity.
        destruct s.
        * apply node_height_change_not_negated_right. discriminate.
        * simpl. discriminate.
        * exfalso. auto.
    - simpl. discriminate.
  Qed.

  Theorem remove_balance_and_height_correct :
    forall (k:N) (t:avl_tree T),
      balance_correct t ->
      balance_correct (fst (avl_remove_go k t)) /\
      height_change_correct (snd (avl_remove_go k t))
                            t
                            (fst (avl_remove_go k t)).
  Proof.
    intros k t bal_t. induction t as [b l IHl [k' v'] r IHr|].
    - simpl in *.  destruct (N.compare_spec k k') as [C|C|C].
      + subst k'. apply avl_remove_top_balance_and_height_correct. auto.
      + destruct (avl_remove_go k l) as [l' s] eqn:go_eq. split.
        * apply node_balance_correct with l r; simpl in *; tauto.
        * assert (s_not_positive: positive <> s).
          { replace s with (snd (l', s)) by reflexivity.
            rewrite <- go_eq.
            apply remove_height_change_not_positive.
          }
          apply node_height_change_correct; simpl in *;
          tauto || (destruct s; auto || (exfalso; auto)).
      + destruct (avl_remove_go k r) as [r' s] eqn:go_eq. split.
        * apply node_balance_correct with l r; simpl in *; tauto.
        * assert (s_not_positive: positive <> s).
          { replace s with (snd (r',s)) by reflexivity.
            rewrite <- go_eq.
            apply remove_height_change_not_positive.
          }
          apply node_height_change_correct; simpl in *;
          tauto || (destruct s; auto || (exfalso; auto)).
    - simpl. auto.
  Qed.

  Theorem remove_balance_correct :
    forall (t:avl_tree T) (k:N),
      balance_correct t -> balance_correct (avl_remove k t).
  Proof.
    intros t k H.
    eapply remove_balance_and_height_correct in H.
    intuition eassumption.
  Qed.

End Remove.

Section Contains.

  Definition contains {T:Type} (k:N) (p:T -> Prop) (t:avl_tree T) :=
    exists v, In (k,v) t /\ p v.

  Definition in_domain {T:Type} (k:N) (t:avl_tree T) : Prop :=
    exists v, In (k,v) t.

  Theorem In_contains :
    forall (T:Type) (k:N) (P:T -> Prop) (v:T) (t:avl_tree T),
      In (k,v) t -> P v -> contains k P t.
  Proof.
    intros T k p v t H P. unfold contains. eauto.
  Qed.

  Theorem In_in_domain :
    forall (T:Type) (t:avl_tree T) (k:N) (v:T), In (k,v) t -> in_domain k t.
  Proof.
    intros T t k v H. unfold in_domain. exists v. assumption.
  Qed.

End Contains.

Section Lookup.

  Variable T : Type.

  Fixpoint avl_lookup (k:N) (t:avl_tree T) : option T :=
    match t with
      | avl_empty => None
      | avl_branch _ l (k',v) r =>
        match N.compare k k' with
          | Lt => avl_lookup k l
          | Gt => avl_lookup k r
          | Eq => Some v
        end
    end.
  Global Arguments avl_lookup : default implicits.

  Example avl_lookup_ex1 :
    forall a b c d : T,
      avl_lookup
        4
        (avl_insert 3 c (avl_insert 4 d (avl_insert 2 b (avl_insert 1 a avl_empty))))
      = Some d.
  Proof. reflexivity. Qed.

  Example avl_lookup_ex2 :
    forall a b c d : T,
      avl_lookup
        5
        (avl_insert 3 c (avl_insert 4 d (avl_insert 2 b (avl_insert 1 a avl_empty))))
      = None.
  Proof. reflexivity. Qed.  

  Theorem lookup_In :
    forall (k:N) (v:T) (t:avl_tree T), avl_lookup k t = Some v -> In (k,v) t.
  Proof.
    intros k v t.
    induction t as [b l IHl [k' v'] r IHr|].
    - simpl. destruct (N.compare_spec k k') as [C|C|C].
      + injection 1. intros. subst. tauto.
      + intuition auto.
      + intuition auto.
    - simpl. discriminate 1.
  Qed.

  Theorem lookup_not_In :
    forall (t:avl_tree T) (k:N),
      binary_tree_invariant t -> avl_lookup k t = None -> ~in_domain k t.
  Proof.
    intros t k bt_inv H. unfold in_domain. intros A.
    induction t as [b l IHl [k' v'] r IHr|].
    - simpl in *. destruct A as [v [A|[A|A]]].
      + inversion A. subst.  rewrite N.compare_refl in H. discriminate.
      + rewrite_all forall_keys_In_iff.
        replace (k ?= k') with Lt in H.
        * intuition eauto.
        * symmetry.  apply N.compare_lt_iff. apply N.gt_lt_iff.
          destruct bt_inv as [bt_inv _]. apply bt_inv with (p := (k,v)); auto.
      + rewrite_all forall_keys_In_iff.
        replace (k ?= k') with Gt in H.
        * intuition eauto.
        * symmetry. apply N.compare_gt_iff.
          destruct bt_inv as [_ [bt_inv _]]. apply bt_inv with (p := (k,v)); auto.
    - simpl in *. destruct A. assumption.
  Qed.

  Theorem In_lookup :
    forall (t:avl_tree T) (k:N) (v:T),
      binary_tree_invariant t -> In (k,v) t -> avl_lookup k t = Some v.
  Proof.
    intros t k v bt_inv H. induction t as [b l IHl [k' v'] r IHr|].
    - simpl in *. destruct (N.compare_spec k k') as [C|C|C].
      + subst k'. apply In_inv_head in H; subst; tauto.
      + apply In_inv_left in H; tauto.
      + apply In_inv_right in H; tauto.
    - inversion H.
  Qed.

  Theorem In_lookup_iff :
    forall (t:avl_tree T) (k:N) (v:T),
      binary_tree_invariant t -> (In (k,v) t <-> avl_lookup k t = Some v).
  Proof.
    pose In_lookup as T1. pose lookup_In as T2.
    intros t k v bt_inv. split; auto.
  Qed.



  Theorem In_eq :
    forall (t:avl_tree T) (k:N) (v v':T),
      binary_tree_invariant t ->
      In (k,v) t -> In (k, v') t -> v = v'.
  Proof.
    intros t k v v' bt_inv. rewrite ?In_lookup_iff.
    - intros P Q. rewrite P in Q. inversion Q. reflexivity.
    - assumption.
    - assumption.
  Qed.

End Lookup.

Section Update.
  Variable T : Type.

  Definition avl_update (k:N) (f:T -> T) (t:avl_tree T) :=
    match avl_lookup k t with
      | None => t
      | Some v => avl_insert k (f v) t
    end.
  Global Arguments avl_update : default implicits.

  Theorem update_preserve_other :
    forall (t:avl_tree T) (k:N) (f:T -> T) (p:N * T),
      fst p <> k -> (In p t <-> In p (avl_update k f t)).
  Proof.
    pose insert_preserve_other as T1.
    intros t k f p k_ineq. unfold avl_update. destruct p.
    destruct (avl_lookup k t); auto || reflexivity.
  Qed.

  Theorem update_In_inv :
    forall (t:avl_tree T) (k:N) (f:T -> T) (v:T),
      binary_tree_invariant t ->
      (In (k,v) (avl_update k f t) <-> (exists x, In (k,x) t /\ f x = v)).
  Proof.
    pose lookup_In as T1. pose insert_In_inv as T2. pose insert_In as T3.
    intros t k f v bt_inv. unfold avl_update.
    destruct (avl_lookup k t) as [x|] eqn:lookup.
    - simpl. split.
      + eauto.
      + destruct 1 as [x' [in_t fe]]. apply In_lookup in in_t.
        * rewrite lookup in in_t. inversion in_t. subst. auto.
        * assumption.
    - simpl. split.
      + rewrite In_lookup_iff. 
        * rewrite lookup. discriminate 1.
        * assumption.
      + destruct 1 as [x [in_t fe]]. apply In_lookup in in_t.
        * rewrite in_t in lookup. discriminate.
        * assumption.
  Qed.

  Theorem update_binary_tree_invariant :
    forall (t:avl_tree T) (k:N) (f:T -> T),
      binary_tree_invariant t -> binary_tree_invariant (avl_update k f t).
  Proof.
    intros t k f bt_inv_t. unfold avl_update. pose insert_binary_tree_invariant as T1.
    destruct (avl_lookup k t); auto.
  Qed.

  Theorem update_balance_correct :
    forall (t:avl_tree T) (k:N) (f:T -> T),
      balance_correct t -> balance_correct (avl_update k f t).
  Proof.
    intros t k f bt_inv_t. unfold avl_update. pose insert_balance_correct as T1.
    destruct (avl_lookup k t); auto.
  Qed.

End Update.

Section InsertMerge.
  Variable T : Type.
  
  Definition avl_insert_merge (k:N) (f:T -> T) (def:T) (t:avl_tree T) : avl_tree T :=
    avl_insert k (match avl_lookup k t with | Some v => f v | None => def end) t.
  Global Arguments avl_insert_merge : default implicits.

  Theorem insert_merge_contains :
    forall (t:avl_tree T) (k:N) (f:T -> T) (def:T) (P:T -> Prop),
      binary_tree_invariant t ->
      (~in_domain k t -> P def) ->
      (forall v, In (k,v) t -> P (f v)) -> contains k P (avl_insert_merge k f def t).
  Proof.
    intros t k f def P bt_inv Pdef Pf. unfold contains. unfold avl_insert_merge.
    pose lookup_In. pose insert_In. pose lookup_not_In.
    destruct (avl_lookup k t) as [v|] eqn:lookup.
    - exists (f v). split; auto.
    - apply lookup_not_In in lookup; eauto.
  Qed.

  Theorem insert_merge_In_inv :
    forall (t:avl_tree T) (k:N) (v def:T) (f:T -> T),
      binary_tree_invariant t ->
      In (k,v) (avl_insert_merge k f def t) ->
      (~in_domain k t /\ v = def) \/ (contains k (fun x => f x = v) t).
  Proof.
    pose lookup_In as T1. pose lookup_not_In as T2.
    intros t k v def f bt_inv in_merge.
    unfold avl_insert_merge in in_merge. unfold contains.
    apply insert_In_inv in in_merge.
    - destruct (avl_lookup k t) as [v'|] eqn:lookup; eauto.
    - assumption.
  Qed.

  Theorem insert_merge_preserve_other :
    forall (t:avl_tree T) (k:N) (f:T -> T) (def:T) (p:N * T),
      k <> fst p -> (In p t <-> In p (avl_insert_merge k f def t)).
  Proof.
    pose insert_preserve_other. destruct p. unfold avl_insert_merge. auto.
  Qed.

  Theorem insert_merge_binary_tree_invariant :
    forall (t:avl_tree T) (k:N) (f:T -> T) (def:T),
      binary_tree_invariant t -> binary_tree_invariant (avl_insert_merge k f def t).
  Proof.
    pose insert_binary_tree_invariant as T1.
    intros t k f def inv_t. unfold avl_insert_merge. auto.
  Qed.

  Theorem insert_merge_balance_correct :
    forall (t:avl_tree T) (k:N) (f:T -> T) (def:T),
      balance_correct t -> balance_correct (avl_insert_merge k f def t).
  Proof.
    pose insert_balance_correct as T1.
    intros t k f def bal_t. unfold avl_insert_merge. auto.
  Qed.

End InsertMerge.

Require List.
Open Scope list.

Section Elems.
  Variable T : Type.
        
  Fixpoint avl_elems (t:avl_tree T) : list (N * T) :=
    match t with
      | avl_empty => nil
      | avl_branch _ l e r => e :: avl_elems l ++ avl_elems r
    end.
  Global Arguments avl_elems : default implicits.

  Theorem elems_In_iff :
    forall (t:avl_tree T) (p:N * T),
      List.In p (avl_elems t) <-> In p t.
  Proof.
    intros t p. induction t as [b l IHl tp r IHr|].
    - simpl. rewrite <- IHr. rewrite <- IHl. rewrite List.in_app_iff.
      assert (H: (tp = p) <-> (p = tp)) by (split; intros; subst; reflexivity).
      rewrite H. reflexivity.
    - reflexivity.
  Qed.
End Elems.

Section Filter.
  Variable T : Type.

  Fixpoint avl_remove_many (ks:list N) (t:avl_tree T) : avl_tree T :=
    match ks with
      | nil     => t
      | k :: kt => avl_remove k (avl_remove_many kt t)
    end.

  Theorem remove_many_subset :
    forall (ks:list N) (t:avl_tree T) (p:N * T),
      In p (avl_remove_many ks t) -> In p t.
  Proof.
    intros ks t p in_remove. pose remove_subset.
    induction ks as [|k kt IH]; eauto.
  Qed.

  Theorem remove_many_binary_tree_invariant :
    forall (ks:list N) (t:avl_tree T) (k:N) (v:T),
      binary_tree_invariant t -> binary_tree_invariant (avl_remove_many ks t).
  Proof.
    intros ks t k v. pose remove_binary_tree_invariant. induction ks; simpl; auto.
  Qed.

  Theorem remove_many_balance_correct :
    forall (ks:list N) (t:avl_tree T) (k:N) (v:T),
      balance_correct t -> balance_correct (avl_remove_many ks t).
  Proof.
    intros ks t k v H.
    induction ks as [|kh kt IH].
    - simpl. auto.
    - eapply remove_balance_and_height_correct in IH. simpl in *.
      unfold avl_remove. intuition eassumption.
  Qed.

  Theorem remove_many_not_In :
    forall (ks:list N) (t:avl_tree T) (k:N) (v:T),
      binary_tree_invariant t -> In (k,v) (avl_remove_many ks t) -> ~(List.In k ks).
  Proof.
    intros ks t k v bt_inv in_remove. induction ks as [|k' kt IH].
    - simpl. auto.
    - simpl.
      pose remove_not_In as T1. pose remove_many_binary_tree_invariant as T2.
      pose remove_subset as T3. unfold not in *.
      destruct 1; simpl in *; subst; eauto.
  Qed.

  Theorem remove_many_preserve_other :
    forall (ks:list N) (t:avl_tree T) (k:N) (v:T),
      ~(List.In k ks) -> (In (k,v) t <-> In (k,v) (avl_remove_many ks t)).
  Proof.
    intros ks t k v not_in_ks. induction ks as [|k' kt IH].
    - simpl. reflexivity.
    - simpl in *. assert (H:k <> k') by (intros eq; symmetry in eq; tauto).
      rewrite IH by tauto. rewrite remove_preserve_other with (k := k'). simpl.
      split.
      + destruct 1; assumption || exfalso; tauto.
      + tauto.
  Qed.

  Definition avl_filter (f:N -> T -> bool) (t:avl_tree T) : avl_tree T :=
    avl_remove_many
      (List.map (fun (p:N*T) => let (k,v) := p in k)
      (List.filter (fun (p:N*T) => let (k,v) := p in negb (f k v)) (avl_elems t))) t.
  Global Arguments avl_filter : default implicits.

  Theorem filter_subset :
    forall (t:avl_tree T) (p:N * T) (f:N -> T -> bool),
      In p (avl_filter f t) -> In p t.
  Proof.
    unfold avl_filter.
    intros t p f. apply remove_many_subset.
  Qed.

  Theorem filter_predicate_true :
    forall (t:avl_tree T) (k:N) (v:T) (f:N -> T -> bool),
      binary_tree_invariant t -> In (k,v) (avl_filter f t) -> f k v = true.
  Proof.
    unfold avl_filter. intros t k v f bt_inv in_filter.
    assert (in_t := in_filter). apply remove_many_subset in in_t.
    destruct (f k v) eqn:fe.
    - reflexivity.
    - apply remove_many_not_In in in_filter.
      + rewrite List.in_map_iff in in_filter. 
        exfalso. apply in_filter. exists (k,v). split.
        * reflexivity.
        * apply List.filter_In. rewrite elems_In_iff. rewrite fe. simpl. tauto.
      + assumption.
  Qed.

  Theorem filter_In :
    forall (f:N -> T -> bool) (t:avl_tree T) (k:N) (v:T),
      binary_tree_invariant t -> ((f k v = true /\ In (k,v) t) <-> In (k,v) (avl_filter f t)).
  Proof.
    intros f t k v bt_inv. split.
    - destruct 1 as [ft in_t]. unfold avl_filter. apply remove_many_preserve_other.
      + intros H. rewrite List.in_map_iff in H. destruct H as [[k' v'] H].
        rewrite List.filter_In in H. destruct H as [keq [k'_in_t fe]].
        subst k'. replace v' with v in *.
        * rewrite ft in fe. discriminate.
        * apply elems_In_iff in k'_in_t. eapply In_eq in in_t; eauto.
      + auto.
    - pose filter_subset as T1. pose filter_predicate_true as T2. eauto.
  Qed.

  Theorem filter_binary_tree_invariant :
    forall (f:N -> T -> bool) (t:avl_tree T) (k:N) (v:T),
      binary_tree_invariant t -> binary_tree_invariant (avl_filter f t).
  Proof.
    pose remove_many_binary_tree_invariant. unfold avl_filter. auto.
  Qed.

  Theorem filter_balance_correct :
    forall (f:N -> T -> bool) (t:avl_tree T) (k:N) (v:T),
      balance_correct t -> balance_correct (avl_filter f t).
  Proof.
    pose remove_many_balance_correct. unfold avl_filter. auto.
  Qed.
End Filter.

Section Map.
  Variable A B : Type.
  
  Fixpoint avl_map (f:N -> A -> B) (t:avl_tree A) : avl_tree B :=
    match t with
      | avl_empty => avl_empty
      | avl_branch b l (k,v) r => avl_branch b (avl_map f l) (k, f k v) (avl_map f r)
    end.
  Global Arguments avl_map : default implicits.

  Theorem map_updates_all :
    forall (t:avl_tree A) (f:N -> A -> B) (k:N) (v:A),
      In (k,v) t -> In (k,f k v) (avl_map f t).
  Proof.
    intros t f k v in_t. induction t as [b l IHl [k' v'] r IHr|].
    - simpl in *. rewrite invert_tuple_eq in in_t. intuition (subst; auto).
    - contradiction.
  Qed.

  Theorem In_map_iff :
    forall (f:N -> A -> B) (t:avl_tree A) (b:B) (k:N),
      In (k, b) (avl_map f t) <-> exists a : A, b = f k a /\ In (k,a) t.
  Proof.
    intros f t b k. induction t as [tb tl tlIH [tk tv] tr trIH|].
    - simpl in *. rewrite tlIH. rewrite trIH. rewrite invert_tuple_eq.
      split.
      + destruct 1 as [H|[H|H]]; destruct H; subst; intuition eauto.
      + destruct 1 as [a H]. rewrite invert_tuple_eq in H. intuition (subst; eauto).
    - simpl. split; destruct 1; intuition contradiction.
  Qed.

  Theorem map_preserve_domain :
    forall (t:avl_tree A) (f:N -> A -> B) (k:N),
      in_domain k t <-> in_domain k (avl_map f t).
  Proof.
    pose In_in_domain as T1. pose map_updates_all as T2.
    split.
    - destruct 1. eauto.
    - unfold in_domain. destruct 1 as [v in_map]. apply In_map_iff in in_map as [a H].
      intuition eauto.
  Qed.

  Theorem map_forall_keys :
    forall (f:N -> A -> B) (t:avl_tree A) (P:N -> Prop),
      forall_keys P t <-> forall_keys P (avl_map f t).
  Proof.
    intros f t P. induction t as [b l IHl [k v] r IHr|].
    - simpl in *. rewrite IHl. rewrite IHr. reflexivity.
    - simpl. reflexivity.
  Qed.

  Theorem map_binary_tree_invariant :
    forall (f:N -> A -> B) (t:avl_tree A),
      binary_tree_invariant t -> binary_tree_invariant (avl_map f t).
  Proof.
    intros f t bt_inv_t. induction t as [b l IHl [k v] r IHr|].
    - simpl in *. rewrite <- ?map_forall_keys. intuition auto.
    - simpl. auto.
  Qed.

  Theorem map_height_unchanged :
    forall (f:N -> A -> B) (t:avl_tree A), avl_height t = avl_height (avl_map f t).
  Proof.
    intros f t. induction t as [b l IHl [k v] r IHr|].
    - simpl in *. congruence.
    - auto.
  Qed.

  Theorem map_balanced_with :
    forall (f g:N -> A -> B) (l r:avl_tree A) (b:sign),
      balanced_with A b l r <-> balanced_with B b (avl_map f l) (avl_map g r).
  Proof.
    pose map_height_unchanged as T1.
    intros f g l r b. unfold balanced_with. destruct b; split; congruence.
  Qed.

  Theorem map_balance_correct :
    forall (f:N -> A -> B) (t:avl_tree A),
      balance_correct t -> balance_correct (avl_map f t).
  Proof.
    intros f t bal_t. induction t as [b l IHl [k v] r IHr|].
    - simpl in *. rewrite <- map_balanced_with. tauto.
    - simpl. auto.
  Qed.
End Map.
