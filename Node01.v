(** * A variant on the original, non-extensional binary tries *)

(* Authors: Xavier Leroy and Damien Doligez, Inria.
   Copyright: Inria.
   License: BSD-3-Clause. *)

(** This is a variant of the [Original] implementation of binary tries,
    differing only in the way tree nodes are represented:
    instead of a single [Node] constructor carrying an optional value,
    we have two constructors, [Node0] carrying no value and [Node1]
    carrying a value.  This provides minor performance improvements
    over the [Original] implementation, but not as much as the [Canonical]
    implementation.  The lack of extensionality is still there. *)

From Coq Require Import PArith.

Set Implicit Arguments.

Module PTree.

(** ** Representation of tries *)

Inductive tree (A: Type) : Type :=
  | Leaf: tree A
  | Node0: tree A -> tree A -> tree A
  | Node1: tree A -> A -> tree A -> tree A.

Arguments Leaf {A}.
Arguments Node0 [A].
Arguments Node1 [A].

Definition t := tree.

(** Smart constructor that avoids creating nodes that contain no data. *)

Definition Node0' {A} (l: tree A) (r: tree A): tree A :=
  match l, r with
  | Leaf, Leaf => Leaf
  | _, _ => Node0 l r
  end.

Definition Node {A} (l: tree A) (x: option A) (r: tree A): tree A :=
  match x, l, r with
  | None, Leaf, Leaf => Leaf
  | None, _, _ => Node0 l r
  | Some v, _, _ => Node1 l v r
  end.

(** ** Basic operations: [empty], [get], [set], [remove] *)

Definition empty (A: Type) : tree A := Leaf.

Fixpoint get (A: Type) (i: positive) (m: tree A) {struct m} : option A :=
  match m with
  | Leaf => None
  | Node0 l r =>
      match i with
      | xH => None
      | xO ii => get ii l
      | xI ii => get ii r
      end
  | Node1 l x r =>
      match i with
      | xH => Some x
      | xO ii => get ii l
      | xI ii => get ii r
      end
  end.

Fixpoint set (A: Type) (i: positive) (v: A) (m: tree A) {struct i} : tree A :=
  match m with
  | Leaf =>
      match i with
      | xH => Node1 Leaf v Leaf
      | xO ii => Node0 (set ii v Leaf) Leaf
      | xI ii => Node0 Leaf (set ii v Leaf)
      end
  | Node0 l r =>
      match i with
      | xH => Node1 l v r
      | xO ii => Node0 (set ii v l) r
      | xI ii => Node0 l (set ii v r)
      end
  | Node1 l x r =>
      match i with
      | xH => Node1 l v r
      | xO ii => Node1 (set ii v l) x r
      | xI ii => Node1 l x (set ii v r)
      end
  end.

Fixpoint remove (A: Type) (i: positive) (m: tree A) {struct m} : tree A :=
  match m with
  | Leaf => Leaf
  | Node0 l r =>
      match i with
      | xH => Node0 l r
      | xO ii => Node0' (remove ii l) r
      | xI ii => Node0' l (remove ii r)
      end
  | Node1 l x r =>
      match i with
      | xH => Node0' l r
      | xO ii => Node1 (remove ii l) x r
      | xI ii => Node1 l x (remove ii r)
      end
  end.

(** ** Good variable properties for the basic operations *)

(** The following equations specify the [empty], [set] and [remove]
    operations in terms of [get] queries.  For example,
    [gempty] characterizes [empty] as the trie that always responds
    "not found" to a [get]. *)

Theorem gempty:
  forall {A} (i: positive), get i (empty A) = None.
Proof.
  auto.
Qed.

Theorem gss:
  forall {A} (i: positive) (x: A) (m: tree A), get i (set i x m) = Some x.
Proof.
  induction i; destruct m; simpl; auto.
Qed.

Theorem gso:
  forall {A} (i j: positive) (x: A) (m: tree A),
  i <> j -> get i (set j x m) = get i m.
Proof.
  induction i; intros; destruct j; destruct m; simpl; auto; try apply IHi; congruence.
Qed.

Lemma gNode0':
  forall {A} (i: positive) (l: tree A) (r: tree A),
  get i (Node0' l r) = match i with xH => None | xO j => get j l | xI j => get j r end.
Proof.
  intros. destruct l, r; simpl; auto. destruct i; auto.
Qed.

Lemma gNode:
  forall {A} (i: positive) (l: tree A) (x: option A) (r: tree A),
  get i (Node l x r) = match i with xH => x | xO j => get j l | xI j => get j r end.
Proof.
  intros. destruct l, x, r; simpl; auto. destruct i; auto.
Qed.

Theorem grs:
  forall {A} (i: positive) (m: tree A), get i (remove i m) = None.
Proof.
  induction i; destruct m; simpl; auto; rewrite gNode0'; simpl; auto.
Qed.

Theorem gro:
  forall {A} (i j: positive) (m: tree A),
  i <> j -> get i (remove j m) = get i m.
Proof.
  induction i; destruct j, m; intros; simpl; auto;
  rewrite ? gNode0'; simpl; auto; try apply IHi; congruence.
Qed.

(** ** Collective operations over tries *)

Section MAP_FILTER.

Variables A B: Type.

Definition option_map (f: A -> option B) (o: option A): option B :=
  match o with None => None | Some a => f a end.

Fixpoint map_filter (f: A -> option B) (m: tree A) : tree B :=
  match m with
  | Leaf => Leaf
  | Node0 l r => Node0' (map_filter f l) (map_filter f r)
  | Node1 l x r => Node (map_filter f l) (f x) (map_filter f r)
  end.

Lemma gmap_filter:
  forall (f: A -> option B) (m: tree A) (i: positive),
  get i (map_filter f m) = option_map f (get i m).
Proof.
  induction m; intros; simpl.
  - auto.
  - rewrite gNode0'. destruct i; auto.
  - rewrite gNode. destruct i; auto.
Qed.

End MAP_FILTER.

Section COMBINE.

Variables A B C: Type.
Variable f: option A -> option B -> option C.
Hypothesis f_None_None: f None None = None.

Fixpoint combine (m1: tree A) (m2: tree B): tree C :=
  match m1, m2 with
  | Leaf, _ => map_filter (fun b => f None (Some b)) m2
  | _, Leaf => map_filter (fun a => f (Some a) None) m1
  | Node0 l1 r1, Node0 l2 r2 => Node0' (combine l1 l2) (combine r1 r2)
  | Node0 l1 r1, Node1 l2 x2 r2 => Node (combine l1 l2) (f None (Some x2)) (combine r1 r2)
  | Node1 l1 x1 r1, Node0 l2 r2 => Node (combine l1 l2) (f (Some x1) None) (combine r1 r2)
  | Node1 l1 x1 r1, Node1 l2 x2 r2 => Node (combine l1 l2) (f (Some x1) (Some x2)) (combine r1 r2)
  end.

Lemma gcombine:
  forall (m1: tree A) (m2: tree B) (i: positive),
  get i (combine m1 m2) = f (get i m1) (get i m2).
Proof.
  assert (L: forall i m, get i (map_filter (fun a => f (Some a) None) m) = f (get i m) None).
  { intros. rewrite gmap_filter. destruct (get i m); auto. }
  assert (R: forall i m, get i (map_filter (fun b => f None (Some b)) m) = f None (get i m)).
  { intros. rewrite gmap_filter. destruct (get i m); auto. }
  Local Opaque map_filter.
  induction m1; intros; simpl; auto; destruct m2; rewrite ? L; auto;
  rewrite ? gNode0', ? gNode; destruct i; simpl; auto.
Qed.

End COMBINE.

End PTree.
