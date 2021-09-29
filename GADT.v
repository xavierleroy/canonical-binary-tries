(** * Binary tries using a GADT to enforce extensionality *)

(* Author: Xavier Leroy, Collège de France and Inria.
   Copyright: Inria.
   License: BSD-3-Clause. *)

From Coq Require Import PArith.

Set Implicit Arguments.

Module PTree.

(** ** Representation of tries *)

(** We start with the two-constructor representation of binary tries
    from module [Original] and add a parameter of type [kind] to the datatype,
    indicating whether the binary trie is empty or nonempty. *)

Inductive kind : Type := Empty | Nonempty.
  
(** As in the [Sigma] implementation, we want to exclude trivially empty nodes
    [Node l None r] where both subtrees [l] and [r] are empty.
    Unlike in the [Sigma] implementation, we express this criterion
    indirectly, using the kinds [kl] of [l] and [kr] of [r]. *)

Definition not_trivially_empty {A} (kl: kind) (o: option A) (kr: kind) :=
  match kl, o, kr with
  | Empty, None, Empty => False
  | _, _, _ => True
  end.

Lemma not_trivially_empty_left: forall A (o: option A) (kr: kind),
  not_trivially_empty Nonempty o kr.
Proof.
  intros; red; auto.
Qed.

Lemma not_trivially_empty_val: forall A (kl: kind) (a: A) (kr: kind),
  not_trivially_empty kl (Some a) kr.
Proof.
  intros; red. destruct kl; auto.
Qed.

Lemma not_trivially_empty_right: forall A (kl: kind) (o: option A),
  not_trivially_empty kl o Nonempty.
Proof.
  intros; red. destruct kl; auto. destruct o; auto.
Qed.

(** The representation type for tries, with the extra parameter of
    type kind that classifies tries as empty or nonempty.  In the
    [Node] case, we add a proof that the node is not trivially empty. *)

Inductive tree (A : Type) : kind -> Type :=
  | Leaf : tree A Empty
  | Node : forall (kl kr: kind) (l: tree A kl) (o: option A) (r: tree A kr),
                  not_trivially_empty kl o kr -> tree A Nonempty.

Arguments Leaf {A}.
Arguments Node [A kl kr].

(** The type of tries (empty or nonempty) is a dependent sum of
    an empty/nonempty kind and a representation of that kind.
    In other words, we quantify existentially over the kind. *)

Definition t (A: Type) := { k : kind & tree A k }.
  
(** ** Basic operations: [empty], [get], [set], [remove] *)

Definition empty (A : Type) : t A := existT _ Empty (@Leaf A).

(** Operations such as [get] are typically split in two functions:
    a function [get'] that works over type [tree A k] and is polymorphic
    over the kind [k], and a wrapper function [get] that deals with the
    existential quantification over the kind [k]. *)

Fixpoint get' (A : Type) (k: kind) (i : positive) (m : tree A k) {struct i} : option A :=
    match m with
    | Leaf => None
    | Node l o r _ =>
        match i with
        | xH => o
        | xO ii => get' ii l
        | xI ii => get' ii r
        end
    end.

Definition get (A: Type) (i : positive) (m : t A) : option A :=
  match m with existT _ k m => get' i m end.
  
(** [set'] has a lovely result type [tree A Nonempty], proving that the result
    is never the empty trie. *)

Fixpoint set' (A : Type) (k: kind) (i : positive) (v : A) (m : tree A k) {struct i} : tree A Nonempty :=
    match m with
    | Leaf =>
        match i with
        | xH => Node Leaf (Some v) Leaf (not_trivially_empty_val _ _ _)
        | xO ii => Node (set' ii v Leaf) None Leaf (not_trivially_empty_left _ _)
        | xI ii => Node Leaf None (set' ii v Leaf) (not_trivially_empty_right _ _)
        end
    | Node l o r _ =>
        match i with
        | xH => Node l (Some v) r (not_trivially_empty_val _ _ _)
        | xO ii => Node (set' ii v l) o r (not_trivially_empty_left _ _)
        | xI ii => Node l o (set' ii v r) (not_trivially_empty_right _ _)
        end
    end.

Definition set (A: Type) (i: positive) (v: A) (m: t A) : t A :=
  match m with existT _ _ m => existT _ Nonempty (set' i v m) end.
  
(** This is the smart constructor [Node'] that combines any two subtrees
    and optional value into a well-formed value of type [t A]. *)

Definition Node' (A: Type) (kl kr: kind) (l: tree A kl) (o: option A) (r: tree A kr) : t A :=
  match o with
  | Some v as o' => existT _ Nonempty (Node l o' r (not_trivially_empty_val _ _ _))
  | None =>
      match l with
      | Node _ _ _ _ as l' =>
          existT _ Nonempty (Node l' None r (not_trivially_empty_left _ _))
      | Leaf =>
          match r with
          | Node _ _ _ _ as r' =>
              existT _ Nonempty (Node Leaf None r' (not_trivially_empty_right _ _))
          | Leaf =>
              existT _ Empty Leaf
          end
      end
  end.

(** Sometimes, one of the subtrees has type [t A] instead of [tree A k]. *)

Definition Node'l (A: Type) kr (l: t A) (o: option A) (r: tree A kr) : t A :=
  match l with existT _ _ ll => Node' ll o r end.

Definition Node'r (A: Type) kl (l: tree A kl) (o: option A) (r: t A) : t A :=
  match r with existT _ _ rr => Node' l o rr end.

(** The [remove] function makes good use of these smart constructors. *)

Fixpoint remove' (A : Type) (k: kind) (i : positive) (m : tree A k) {struct i} : t A :=
  match i with
  | xH =>
      match m with
      | Leaf => empty A
      | Node l o r _ => Node' l None r
      end
  | xO ii =>
      match m with
      | Leaf => empty A
      | Node l o r _ => Node'l (remove' ii l) o r
      end
  | xI ii =>
      match m with
      | Leaf => empty A
      | Node l o r _ => Node'r l o (remove' ii r)
      end
end.

Definition remove (A : Type) (i : positive) (m : t A) : t A :=
  match m with existT _ _ m => remove' i m end.

(** ** Good variable properties for the basic operations *)

Lemma gleaf:
  forall (A : Type) (i : positive), get' i (Leaf : tree A Empty) = None.
Proof. destruct i; auto. Qed.

Theorem gempty:
  forall (A: Type) (i: positive), get i (empty A) = None.
Proof. intros. apply gleaf. Qed.
  
Lemma gss':
  forall (A: Type) (i: positive) (x: A)  (k: kind) (m: tree A k),
  get' i (set' i x m) = Some x.
Proof.
  induction i; destruct m; simpl; auto.
Qed.

Theorem gss:
  forall (A: Type) (i: positive) (x: A) (m: t A), get i (set i x m) = Some x.
Proof.
  intros. destruct m as [k m]; simpl. apply gss'.
Qed.

Lemma gso':
  forall (A: Type) (i j: positive) (x: A) k (m: tree A k),
  i <> j -> get' i (set' j x m) = get' i m.
Proof.
  induction i; intros; destruct j; destruct m; simpl;
  try rewrite <- (gleaf A i); auto; try apply IHi; congruence.
Qed.

Theorem gso:
  forall (A: Type) (i j: positive) (x: A) (m: t A),
  i <> j -> get i (set j x m) = get i m.
Proof.
  intros. destruct m as [k m]; simpl. apply gso'; auto.
Qed.
  
Lemma gnode':
  forall (A: Type) kl (l: tree A kl) kr (r: tree A kr) o i,
  get i (Node' l o r) =
  match i with xH => o | xO i => get' i l | xI i => get' i r end.
Proof.
  intros. unfold Node'.
  destruct o; [ | destruct l; [ destruct r | ]];
  destruct i; simpl; rewrite ? gleaf; auto.
Qed.

Lemma gnode'l:
  forall (A: Type) (l: t A) kr (r: tree A kr) o i,
  get i (Node'l l o r) =
  match i with xH => o | xO i => get i l | xI i => get' i r end.
Proof.
  intros. destruct l as [kl l]; simpl. apply gnode'.
Qed.

Lemma gnode'r:
  forall (A: Type) kl (l: tree A kl) (r: t A) o i,
  get i (Node'r l o r) =
  match i with xH => o | xO i => get' i l | xI i => get i r end.
Proof.
  intros. destruct r as [kr r]; simpl. apply gnode'.
Qed.

Lemma grs':
  forall (A: Type) (i: positive) k (m: tree A k), get i (remove' i m) = None.
Proof.
Local Opaque Node'.
  induction i; destruct m; simpl remove'; auto; rewrite ?gleaf, ?gnode', ?gnode'l, ?gnode'r; auto.
Qed.
  
Theorem grs:
  forall (A: Type) (i: positive) (m: t A), get i (remove i m) = None.
Proof.
  intros. destruct m as [k m]. apply grs'.
Qed.

Lemma gro':
  forall (A: Type) (i j: positive) k (m: tree A k),
  i <> j -> get i (remove' j m) = get' i m.
Proof.
  induction i; intros; destruct j; destruct m; simpl remove';
  rewrite ?gnode', ?gnode'l, ?gnode'r, ?gleaf; auto; simpl.
  apply IHi; congruence.
  apply IHi; congruence.
  congruence.
Qed.

Theorem gro:
  forall (A: Type) (i j: positive) (m: t A),
  i <> j -> get i (remove j m) = get i m.
Proof.
  intros. destruct m as [k m]. apply gro'; auto.
Qed.

(** ** The extensionality property *)  

(** This is the key lemma to show extensionality: a value of type [tree A k]
    that contains no data (all [get'] queries return [None])
    is equal to [Leaf], and moreover its kind [k] is [Empty]. *)

Lemma extensionality_empty:
  forall (A: Type) k (m: tree A k),
    (forall i, get' i m = None) ->
    exists E: k = Empty, eq_rect _ _ m _ E = Leaf.
Proof.
  induction m; intros G.
- exists refl_equal; auto.
- destruct IHm1 as (E1 & F1). { intros; apply (G (xO i)). }
  destruct IHm2 as (E2 & F2). { intros; apply (G (xI i)). }
  assert (o = None). { apply (G xH). }
  subst kl kr o. elim n.
Qed.

(** As in the [Sigma] implementation, we also need the "uniqueness of
    proofs" property for the [not_trivially_empty] predicate.  We
    could assume the proof irrelevance axiom and get it for free, but
    it's not hard to show the property without using axioms. *)

Lemma not_trivially_empty_unique_proofs:
  forall A kl (o: option A) kr (p1 p2: not_trivially_empty kl o kr),
  p1 = p2.
Proof.
  unfold not_trivially_empty; intros.
  destruct kl, o, kr, p1, p2; auto.
Qed.

(** It follows that two trees that are equivalent (all [get'] queries agree)
    have the same kind and are equal.  The subtle point here is that the
    two trees cannot be assumed to have the same kind, otherwise the
    induction does not go through.  *)

Lemma extensionality_rec:
  forall (A: Type) k1 (m1: tree A k1) k2 (m2: tree A k2),
    (forall i, get' i m1 = get' i m2) ->
    exists E: k1 = k2, eq_rect _ _ m1 _ E = m2.
Proof.
  induction m1 as [ | kl1 kr1 l1 LREC o1 r1 RREC NT1].
  - intros. destruct (extensionality_empty m2) as (E1 & E2).
    { intros. rewrite <- H. apply gleaf. }
    subst k2. simpl in E2. subst m2. exists refl_equal; auto.
  - destruct m2 as [ | kl2 kr2 l2 o2 r2 NT2]; intros SAME.
    + apply extensionality_empty.
      intros. rewrite SAME. apply gleaf.
    + destruct (LREC kl2 l2) as (EL & FL).  { intros. apply (SAME (xO i)). }
      destruct (RREC kr2 r2) as (ER & FR).  { intros. apply (SAME (xI i)). }
      assert (o1 = o2). { apply (SAME xH). }
      subst kl2 kr2. simpl in FL. simpl in FR. subst l2 o2 r2.
      assert (NT1 = NT2). { apply not_trivially_empty_unique_proofs. }
      subst NT2. 
      exists refl_equal; auto.
  Qed.

Theorem extensionality:
  forall (A: Type) (m1: t A) (m2: t A),
  (forall i, get i m1 = get i m2) ->
  m1 = m2.
Proof.
  intros. destruct m1 as [k1 m1], m2 as [k2 m2]; simpl in *.
  destruct (extensionality_rec m1 m2) as (E1 & E2). auto.
  subst k2. simpl in E2. subst m2. auto.
Qed.

End PTree.
