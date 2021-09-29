(** * The original, non-extensional binary tries *)

(* Authors: Xavier Leroy and Damien Doligez, Inria.
   Copyright: Inria.
   License: BSD-3-Clause. *)

(** This implementation of binary tries is taken from the Maps module
    of CompCert version 3.9, 
    https://compcert.org/doc-3.9/html/compcert.lib.Maps.html
    Several operations were omitted, and some proofs were tightened.
*)

From Coq Require Import PArith.

Set Implicit Arguments.

Module PTree.

(** ** Representation of tries *)

Inductive tree (A: Type) : Type :=
  | Leaf: tree A
  | Node: tree A -> option A -> tree A -> tree A.

Arguments Leaf {A}.
Arguments Node [A].

Definition t := tree.

(** A smart constructor that avoids creating nodes that contain no data. *)

Definition Node' {A} (l: tree A) (x: option A) (r: tree A): tree A :=
  match l, x, r with
  | Leaf, None, Leaf => Leaf
  | _, _, _ => Node l x r
  end.

(** ** Basic operations: [empty], [get], [set], [remove] *)

Definition empty (A: Type) : tree A := Leaf.

Fixpoint get (A: Type) (i: positive) (m: tree A) {struct m} : option A :=
  match m with
  | Leaf => None
  | Node l o r =>
      match i with
      | xH => o
      | xO ii => get ii l
      | xI ii => get ii r
      end
  end.

Fixpoint set (A: Type) (i: positive) (v: A) (m: tree A) {struct i} : tree A :=
  match m with
  | Leaf =>
      match i with
      | xH => Node Leaf (Some v) Leaf
      | xO ii => Node (set ii v Leaf) None Leaf
      | xI ii => Node Leaf None (set ii v Leaf)
      end
  | Node l o r =>
      match i with
      | xH => Node l (Some v) r
      | xO ii => Node (set ii v l) o r
      | xI ii => Node l o (set ii v r)
      end
  end.

Fixpoint remove (A: Type) (i: positive) (m: tree A) {struct m} : tree A :=
  match m with
  | Leaf => Leaf
  | Node l o r =>
      match i with
      | xH => Node' l None r
      | xO ii => Node' (remove ii l) o r
      | xI ii => Node' l o (remove ii r)
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

Lemma gNode':
  forall {A} (i: positive) (l: tree A) (x: option A) (r: tree A),
  get i (Node' l x r) = match i with xH => x | xO j => get j l | xI j => get j r end.
Proof.
  intros. destruct l, x, r; simpl; auto. destruct i; auto.
Qed.

Theorem grs:
  forall {A} (i: positive) (m: tree A), get i (remove i m) = None.
Proof.
  induction i; destruct m; simpl; auto; rewrite gNode'; simpl; auto.
Qed.

Theorem gro:
  forall {A} (i j: positive) (m: tree A),
  i <> j -> get i (remove j m) = get i m.
Proof.
  induction i; destruct j, m; intros; simpl; auto;
  rewrite gNode'; simpl; auto; try apply IHi; congruence.
Qed.

(** ** Collective operations over tries *)

(** The [map_filter] operation combines a "map" (apply a function to
    every value of a trie) and a "filter" (keep only the values
    that satisy a given predicate).  The function [f] being mapped
    has type [A -> option B].  A value [a] in the input trie
    becomes a value [b] in the output trie if [f a = Some b]
    and is absent in the output trie if [f a = None]. *)

Section MAP_FILTER.

Variables A B: Type.

Definition option_map (f: A -> option B) (o: option A): option B :=
  match o with None => None | Some a => f a end.

Fixpoint map_filter (f: A -> option B) (m: tree A) : tree B :=
  match m with
  | Leaf => Leaf
  | Node l o r => Node' (map_filter f l) (option_map f o) (map_filter f r)
  end.

Lemma gmap_filter:
  forall (f: A -> option B) (m: tree A) (i: positive),
  get i (map_filter f m) = option_map f (get i m).
Proof.
  induction m; intros; simpl.
  - auto.
  - rewrite gNode'. destruct i; auto.
Qed.

End MAP_FILTER.

(** The [combine] operation traverses two tries in parallel,
    applying a function [f: option A -> option B -> option C]
    at each node to build the resulting trie. *)

Section COMBINE.

Variables A B C: Type.
Variable f: option A -> option B -> option C.
Hypothesis f_None_None: f None None = None.

Fixpoint combine (m1: tree A) (m2: tree B): tree C :=
  match m1, m2 with
  | Leaf, _ => map_filter (fun b => f None (Some b)) m2
  | _, Leaf => map_filter (fun a => f (Some a) None) m1
  | Node l1 o1 r1, Node l2 o2 r2 => Node' (combine l1 l2) (f o1 o2) (combine r1 r2)
  end.

Lemma gcombine:
  forall (m1: tree A) (m2: tree B) (i: positive),
  get i (combine m1 m2) = f (get i m1) (get i m2).
Proof.
  Local Opaque map_filter.
  induction m1; intros.
- simpl. rewrite gmap_filter. destruct (get i m2); auto.
- destruct m2; simpl combine.
  + rewrite gmap_filter. destruct (get i (Node m1_1 o m1_2)); auto.
  + rewrite gNode'; simpl. destruct i; auto.
Qed.

End COMBINE.

End PTree.
