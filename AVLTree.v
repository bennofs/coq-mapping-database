Require Import NArith.
Require Import Bool.
Require Import String.
Definition admit {T:Type} : T. Admitted.

Open Scope N.

Inductive sign : Type :=
  | negative : sign
  | zero : sign
  | positive : sign.

Definition sign_negate (a:sign) : sign :=
  match a with
    | negative => positive
    | zero     => zero
    | positive => negative
  end.

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

Inductive avl_tree (T:Type) : Type :=
  (* A branch consists of a balance, the left subtree, the key + value and the
   * right subtree. The balance if [positive] if the left subtree's height is greater
   * than the height of the right subtree. If the heights are the same, the balance is
   * [zero], otherwise it will be [negative].
   *)
  | avl_branch : sign -> avl_tree T -> N * T -> avl_tree T -> avl_tree T
  | avl_empty  : avl_tree T.
Arguments avl_branch [T] _ _ _ _.
Arguments avl_empty [T].

Fixpoint In {T:Type} (v:N * T) (t:avl_tree T) : Prop :=
  match t with
    | avl_empty => False
    | avl_branch _ l v' r => v = v' \/ In v l \/ In v r
  end.

Definition avl_singleton {T:Type} (k:N) (v:T) : avl_tree T :=
  avl_branch zero avl_empty (k,v) avl_empty.

Theorem not_In_empty : forall (T:Type) (k:N) (v:T), ~In (k,v) avl_empty.
Proof. intros. destruct 1. Qed.

Section Height.

  Variable T : Type.

  Fixpoint avl_height (t:avl_tree T) : N :=
    match t with
      | avl_empty => 0
      | avl_branch _ l _ r => N.max (avl_height l) (avl_height r) + 1
    end.

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
      | avl_branch _ l (k,_) r => f k /\ forall_keys f l /\ forall_keys f r
    end.
  Global Arguments forall_keys : default implicits.

  Definition all_keys_smaller (k:N) (t:avl_tree T) : Prop := forall_keys (N.gt k) t.
  Definition all_keys_greater (k:N) (t:avl_tree T) : Prop := forall_keys (N.lt k) t.
  Global Arguments all_keys_smaller : default implicits.
  Global Arguments all_keys_greater : default implicits.

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

  Lemma invert_tuple_eq :
    forall (A B:Type) (a a':A) (b b':B),
      (a,b) = (a',b') <-> a = a' /\ b = b'.
  Proof. split; inversion 1; subst; auto. Qed.

  Theorem forall_keys_In_iff :
    forall (P:N -> Prop) (t:avl_tree T),
      forall_keys P t <-> (forall k v, In (k,v) t -> P k).
  Proof.
    intros P t. induction t as [b l IHl [k v] r IHr|].
    - simpl. rewrite IHl. rewrite IHr. setoid_rewrite invert_tuple_eq.
      split; intuition (subst; eauto).
    - split; simpl; intuition auto.
  Qed.

  Fixpoint binary_tree_invariant (t:avl_tree T) : Prop :=
    match t with
      | avl_empty => True
      | avl_branch _ l (k,_) r =>
        all_keys_smaller k l /\ all_keys_greater k r /\
        binary_tree_invariant l /\ binary_tree_invariant r
    end.
  Global Arguments binary_tree_invariant : default implicits.

End Invariants.

Section Node.

  Variable T : Type.

  (* Calculate the balance change from the height change of a subtree. *)
  Let balance_change (a:sign + sign) : sign :=
    match a with
      | inl s  => s
      | inr s => sign_negate s
    end.

  (* Apply a balance change.
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

  (* Return the height change of the subtree (discarding which subtree changed). *)
  Let height_change (s:sign + sign) : sign := match s with | inr x => x | inl x => x end.

  (* Rotation for when the right subtree is higher *)
  Let rotate_right (removed:bool) (l:avl_tree T) (p:N * T) (r:avl_tree T)
  : avl_tree T * sign :=
    match r with
      | avl_branch positive (avl_branch rlb rll rlp rlr) rp rr =>
        ( avl_branch
            zero
            (avl_branch (sign_negate rlb) l p rll)
            rlp
            (avl_branch (sign_negate rlb) rlr rp rr)
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

  (* Rotation for when the left subtree is higher *)
  Let rotate_left (removed:bool) (l:avl_tree T) (p:N * T) (r:avl_tree T)
  : avl_tree T * sign :=
    match l with
      | avl_branch negative ll lp (avl_branch lrb lrl lrp lrr) =>
        ( avl_branch
            zero
            (avl_branch (sign_negate lrb) ll lp lrl)
            lrp
            (avl_branch (sign_negate lrb) lrr p r)
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

  Lemma rotate_left_binary_tree_invariant :
    forall (b:bool) (k:N) (v:T) (l r:avl_tree T),
      binary_tree_invariant l -> binary_tree_invariant r ->
      all_keys_smaller k l -> all_keys_greater k r ->
      binary_tree_invariant (fst (rotate_left b l (k,v) r)).
  Proof.
    Hint Resolve all_keys_smaller_chain all_keys_greater_chain.
    intros b k v l r bt_inv_l bt_inv_r l_smaller r_greater.
    destruct l as [lb ll [lk lv] lr|].
    - simpl. destruct lb; destruct lr as [lrb lrl [lrk lrkv] lrr|];
          simpl in *; unfold all_keys_smaller, all_keys_greater in *; simpl in *;
          rewrite_all N.gt_lt_iff;
          intuition eauto.
    - simpl. auto.
  Qed.

  Lemma rotate_right_binary_tree_invariant :
    forall (b:bool) (k:N) (v:T) (l r:avl_tree T),
      binary_tree_invariant l -> binary_tree_invariant r ->
      forall_keys (N.gt k) l -> forall_keys (N.lt k) r ->
      binary_tree_invariant (fst (rotate_right b l (k,v) r)).
  Proof.
    Hint Resolve all_keys_smaller_chain all_keys_greater_chain.
    intros b k v l r bt_inv_l bt_inv_r l_smaller r_greater.
    destruct r as [rb rl [rk rv] rr|].
    - simpl. destruct rb; destruct rl as [rlb rll [rlk rlkv] rlr|];
        simpl in *; unfold all_keys_greater, all_keys_smaller in *; simpl in *;
        rewrite_all N.gt_lt_iff; intuition eauto.
    - simpl. auto.
  Qed.

  Lemma rotate_left_same_elements :
    forall (b:bool) (k k':N) (v v':T) (l r:avl_tree T),
      In (k',v') (avl_branch zero l (k,v) r) <->
      In (k',v') (fst (rotate_left b l (k,v) r)).
  Proof.
    intros b k k' v v' l r.
    destruct l as [lb ll [lk lv] lr|].
    - simpl. destruct lb;
        destruct lr as [lrb lrl [lrk lrv] lrr|];
        simpl in *; rewrite_all invert_tuple_eq;
        intuition (subst; assumption || discriminate).
    - simpl. reflexivity.
  Qed.

  Lemma rotate_right_same_elements :
    forall (b:bool) (k k':N) (v v':T) (l r:avl_tree T),
      In (k',v') (avl_branch zero l (k,v) r) <->
      In (k',v') (fst (rotate_right b l (k,v) r)).
  Proof.
    intros b k k' v v' l r.
    destruct r as [rb rl [rk rv] rr|].
    - simpl. destruct rb;
        destruct rl as [rlb rll [rlk rlv] rlr|];
        simpl in *; rewrite_all invert_tuple_eq;
        intuition (subst; assumption || discriminate).
    - simpl. reflexivity.
  Qed.

  Theorem node_binary_tree_invariant :
    forall (b:sign) (s:sign + sign) (l r:avl_tree T) (k:N) (v:T),
      binary_tree_invariant l -> binary_tree_invariant r ->
      forall_keys (N.gt k) l -> forall_keys (N.lt k) r ->
      binary_tree_invariant (fst (node b s l (k,v) r)).
  Proof.
    Hint Resolve rotate_right_binary_tree_invariant rotate_left_binary_tree_invariant.
    intros b s l r k v bt_inv_l bt_inv_r l_smaller r_greater. unfold node.
    destruct s as [s|s]; destruct s; destruct b; simpl; auto.
  Qed.

  Theorem node_same_elements :
    forall (b:sign) (s:sign + sign) (l r:avl_tree T) (k k':N) (v v':T),
      (k',v') = (k,v) \/ In (k',v') l \/ In (k',v') r <->
      In (k',v') (fst (node b s l (k,v) r)).
  Proof.
    Hint Rewrite <- invert_tuple_eq rotate_right_same_elements rotate_left_same_elements : core.
    intros b s l r k k' v v'.
    destruct s as [s|s]; destruct s; destruct b; unfold node; simpl;
    autorewrite with core; simpl; intuition (subst; auto).
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
    setoid_rewrite forall_keys_In_iff. intros k v t P forall_t for_P k' v'.
    destruct (N.eq_dec k k'); subst; eauto.
  Qed.

  Theorem insert_binary_tree_invariant :
    forall (k:N) (v:T) (t:avl_tree T),
      binary_tree_invariant t -> binary_tree_invariant (avl_insert k v t).
  Proof.
    Hint Resolve node_binary_tree_invariant insert_forall_keys.
    Hint Resolve -> N.gt_lt_iff.
    Hint Resolve <- N.gt_lt_iff.
    Hint Unfold all_keys_greater all_keys_smaller.
    intros k v t bt_inv_t. induction t as [b l IHl [k' v'] r IHr|].
    - unfold avl_insert in *. simpl. destruct (N.compare_spec k k') as [C|C|C].
      + simpl in *. subst k'. auto.
      + destruct (avl_insert_go k v l) as [a s] eqn:X.
        replace a with (avl_insert k v l) in * by (unfold avl_insert; rewrite X; auto).
        simpl in *. autounfold in *. intuition auto.
      + destruct (avl_insert_go k v r) as [a s] eqn:X.
        replace a with (avl_insert k v r) in * by (unfold avl_insert; rewrite X; auto).
        simpl in *. autounfold in *. intuition auto.
    - simpl. auto.
  Qed.

End Insert.

Section Remove.
  Variable T : Type.

  Fixpoint avl_remove_minimum_go (b:sign) (l:avl_tree T) (p:N * T) (r:avl_tree T)
  : (N * T) * (avl_tree T * sign) :=
    match l with
      | avl_empty => (p, (r, negative))
      | avl_branch lb ll lp lr =>
        match avl_remove_minimum_go lb ll lp lr with
          | (pm, (l', s)) => (pm, node b (inl s) l' p r)
        end
    end.

  Example avl_remove_minimum_go_ex1 :
    forall a b c d : T,
      avl_remove_minimum_go
        negative
        (avl_branch zero avl_empty (1,a) avl_empty)
        (2,b)
        (avl_branch positive
                    (avl_branch zero avl_empty (3,c) avl_empty)
                    (4,d)
                    avl_empty) =
      ((1,a), (avl_branch
                 zero
                 (avl_branch zero avl_empty (2,b) avl_empty)
                 (3,c)
                 (avl_branch zero avl_empty (4,d) avl_empty)
               , negative)).
  Proof. intros. reflexivity. Qed.

  Fixpoint avl_remove_go (k:N) (t:avl_tree T) : avl_tree T * sign :=
    match t with
      | avl_empty => (avl_empty, zero)
      | avl_branch b l (k',v') r =>
        match N.compare k k' with
          | Lt => let (l',s) := avl_remove_go k l in node b (inl s) l' (k',v') r
          | Gt => let (r',s) := avl_remove_go k r in node b (inr s) l (k',v') r'
          | Eq =>
            match r with
              | avl_empty => (l, negative)
              | avl_branch rb rl rp rr =>
                let '(p', (r',s)) := avl_remove_minimum_go rb rl rp rr in
                node b (inr s) l p' r'
            end
        end
    end.

  Definition avl_remove (k:N) (t:avl_tree T) : avl_tree T := fst (avl_remove_go k t).

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
End Remove.

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

End Lookup.