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

Section Empty.
  Variable T : Type.

  Theorem not_In_empty : forall (k:N) (v:T), ~In (k,v) avl_empty.
  Proof. intros.  destruct 1. Qed.
End Empty.

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
  Let rotate_right (removed:bool) (l:avl_tree T) (p:N * T) (r:avl_tree T) :=
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
      | avl_empty => (avl_empty, zero)
    end.

  (* Rotation for when the left subtree is higher *)
  Let rotate_left (removed:bool) (l:avl_tree T) (p:N * T) (r:avl_tree T) :=
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
          , if removed then negative else zero
        )
      | avl_empty => (avl_empty, zero)
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
            match l with
              | avl_empty => (r, negative)
              | avl_branch lb ll lp lr =>
                let '(p', (l',s)) := avl_remove_minimum_go lb ll lp lr in
                node b (inl s) l' p' r
            end
        end
    end.

  Definition avl_remove (k:N) (t:avl_tree T) : avl_tree T := fst (avl_remove_go k t).

  Example avl_remove_ex1 :
    forall a b c : T,
      avl_remove 2 (avl_insert 1 a (avl_insert 2 b (avl_insert 3 c avl_empty))) =
      avl_branch negative avl_empty (1,a) (avl_insert 3 c avl_empty).
  Proof. reflexivity. Qed.

  Example avl_remove_ex2 :
    forall a b c d : T,
      avl_remove
        2
        (avl_insert 3 c (avl_insert 4 d (avl_insert 2 b (avl_insert 1 a avl_empty)))) =
      avl_insert 1 a (avl_insert 4 d (avl_insert 3 c avl_empty)).
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