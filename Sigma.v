(** * Binary tries wrapped in a sigma type to enforce extensionality *)

(* Author: Xavier Leroy, Collège de France and Inria.
   Copyright: Inria.
   License: BSD-3-Clause. *)

From Coq Require Import PArith Program.Equality.
From Tries Require Original.

Set Implicit Arguments.

Module PTree.

Import Original.PTree.

(** ** Representation of tries *)

(** We start with the two-constructor representation of binary tries
    from module [Original] and work out a well-formedness criterion
    that, in the end, suffices to ensures extensionality. *)

(** A trivially empty node is the subtree [Node Leaf None Leaf].
    It contains no values, and is extensionally equivalent to [Leaf],
    but structurally different.  Well-formed trees are those that
    contain no trivially empty nodes. *)

Definition not_trivially_empty {A} (l: tree A) (o: option A) (r: tree A) :=
  match l, o, r with
  | Leaf, None, Leaf => False
  | _, _, _ => True
  end.

Lemma not_trivially_empty_left: forall A (l: tree A) (o: option A) (r: tree A),
  l <> Leaf -> not_trivially_empty l o r.
Proof.
  intros; red. destruct l; auto. congruence.
Qed.

Lemma not_trivially_empty_val: forall A (l: tree A) (a: A) (r: tree A),
  not_trivially_empty l (Some a) r.
Proof.
  intros; red. destruct l; auto.
Qed.

Lemma not_trivially_empty_right: forall A (l: tree A) (o: option A) (r: tree A),
  r <> Leaf -> not_trivially_empty l o r.
Proof.
  intros; red. destruct l; auto. destruct o; auto. destruct r; auto.
Qed.

(** The [wf m] predicate states that the tree [m] is well formed,
    in the sense that all nodes it contains are not trivially empty. *)

Inductive wf {A} : tree A -> Prop :=
  | wf_leaf: wf Leaf
  | wf_node: forall l o r,
      wf l -> wf r -> not_trivially_empty l o r ->
      wf (Node l o r).

(** Our type [t A] of extensional tries is a sigma type:
    it consists of pairs of an original trie [m] and a proof of [wf m]. *)

Definition t (A: Type) := { m : tree A | wf m }.

(** ** Basic operations: [empty], [get], [set], [remove] *)

(** The operations over the sigma type [t A] are derived from those of the
    original implementation of binary tries, complemented with proofs
    of well-formedness. *)

Definition empty (A: Type) : t A :=
  exist _ (Original.PTree.empty A) wf_leaf.

Definition get (A: Type) (i: positive) (m: t A) : option A :=
  Original.PTree.get i (proj1_sig m).

(** We prove that well-formedness is preserved by the [set] operation:
    it cannot create a trivially empty node. *)

Lemma set_not_leaf: forall (A: Type) (v: A) i m, Original.PTree.set i v m <> Leaf.
Proof.
  destruct i, m; simpl; congruence.
Qed.

Lemma wf_set: forall (A: Type) (v: A) i m, wf m -> wf (Original.PTree.set i v m).
Proof.
  induction i; destruct 1; simpl;
  auto using wf_leaf, wf_node, not_trivially_empty_left, not_trivially_empty_right, not_trivially_empty_val, set_not_leaf.
Qed.

Definition set (A: Type) (i: positive) (v: A) (m: t A) : t A :=
  exist _ (Original.PTree.set i v (proj1_sig m))
          (wf_set v i (proj2_sig m)).

(** The [Node'] smart constructor never creates a trivially empty node
    either. *)

Lemma wf_Node': forall A (l: tree A) (o: option A) (r: tree A),
  wf l -> wf r -> wf (Node' l o r).
Proof.
  destruct l, o, r; intros; simpl; constructor; simpl; auto.
Qed.

(** It follows that the [remove] operation preserves well-formedness. *)

Lemma wf_remove:
  forall (A: Type) (m: tree A), wf m -> forall i, wf (Original.PTree.remove i m).
Proof.
  induction 1; intros; simpl.
- constructor.
- destruct i; auto using wf_Node'.
Qed.

Definition remove (A: Type) (i: positive) (m: t A) : t A :=
  exist _ (Original.PTree.remove i (proj1_sig m))
          (wf_remove (proj2_sig m) i).

(** ** Good variable properties for the basic operations *)

(** The characterizations of [empty], [set] and [remove] in terms of
    [get] queries carry over directly from those of the 
    original implementation. *)

Theorem gempty:
  forall (A: Type) (i: positive), get i (empty A) = None.
Proof. reflexivity. Qed.

Theorem gss:
  forall (A: Type) (i: positive) (x: A) (m: t A), get i (set i x m) = Some x.
Proof.
  intros; destruct m as [m wf]. apply Original.PTree.gss.
Qed.

Theorem gso:
  forall (A: Type) (i j: positive) (x: A) (m: t A),
  i <> j -> get i (set j x m) = get i m.
Proof.
  intros; destruct m as [m wf]. apply Original.PTree.gso; auto.
Qed.

Theorem grs:
  forall (A: Type) (i: positive) (m: t A), get i (remove i m) = None.
Proof.
  intros; destruct m as [m wf]. apply Original.PTree.grs.
Qed.

Theorem gro:
  forall (A: Type) (i j: positive) (m: t A),
  i <> j -> get i (remove j m) = get i m.
Proof.
  intros; destruct m as [m wf]. apply Original.PTree.gro; auto.
Qed.

(** ** Extensionality property *)

(** We first show that for well-formed tries, equivalence implies equality.
    In other words, the well-formedness criterion rules out all the cases
    where the original implementation of tries fails the extensionality property. *)

Lemma extensionality_empty:
  forall A (m: tree A),
  wf m -> (forall i, Original.PTree.get i m = None) -> m = Leaf.
Proof.
  induction 1; simpl; intros E.
- auto.
- assert (l = Leaf). { apply IHwf1. intros. apply (E (xO i)). }
  assert (r = Leaf). { apply IHwf2. intros. apply (E (xI i)). }
  destruct o eqn:O.
  specialize (E xH). discriminate.
  subst l r. simpl in H1. tauto. 
Qed.

Lemma extensionality_rec:
  forall A (m1: tree A), wf m1 -> forall (m2: tree A), wf m2 ->
  (forall i, Original.PTree.get i m1 = Original.PTree.get i m2) ->
  m1 = m2.
Proof.
  induction 1.
- intros m2 WF2 E. symmetry. apply extensionality_empty; auto.
  intros. symmetry. apply E.
- destruct 1; intros E.
  + apply extensionality_empty. constructor; auto.
    intros. apply E.
  + f_equal.
    * apply IHwf1; auto. intros. apply (E (xO i)).
    * apply (E xH).
    * apply IHwf2; auto. intros. apply (E (xI i)).
Qed.

(** To show that two values of type [t A] are equal, it is not enough to show that
    their data parts (first projections [proj1_sig]) are equal, which follows
    from the [extensionality_rec] lemma above: we must also show that their proof parts
    (second projections [proj2_sig]) are equal too.

    To this end, we need to show the unique proof property for the [wf m] predicate:
    two proofs of [wf m] are always equal.  We could just assert
    the proof irrelevance axiom and the result would follow trivially.
    However, we also have a proof without axioms. *)
  
Lemma not_trivially_empty_unique_proofs:
  forall A (l: tree A) (o: option A) (r: tree A) (p1 p2: not_trivially_empty l o r),
  p1 = p2.
Proof.
  unfold not_trivially_empty; intros.
  destruct l, o, r, p1, p2; auto.
Qed.

Lemma wf_unique_proofs:
  forall A (m: tree A) (p1 p2: wf m), p1 = p2.
Proof.
  induction m; intros; dependent destruction p1; dependent destruction p2.
- auto.
- f_equal; auto using not_trivially_empty_unique_proofs.
Qed.

(** The desired extensionality property follows. *)

Theorem extensionality:
  forall A (m1 m2: t A),
  (forall i, get i m1 = get i m2) -> m1 = m2.
Proof.
  intros A [m1 p1] [m2 p2] E.
  assert (m1 = m2) by (apply extensionality_rec; auto).
  subst m2.
  assert (p1 = p2) by (apply wf_unique_proofs).
  subst p2.
  auto.
Qed.

End PTree.
