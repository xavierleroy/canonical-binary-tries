(** * Binary Patricia tries *)

(* Author: Xavier Leroy, Collège de France and Inria.
   Copyright: Inria.
   License: BSD-3-Clause. *)

(** Inspired by section 12.3 of "Functional algorithms, verified!"
    by T. Nipkow et al. *)

From Coq Require Import PArith.
From Tries Require Original.

Module O := Original.PTree.

Set Implicit Arguments.

(** ** Operations on positive numbers viewed as lists of bits *)

(** Concatenation. *)

Fixpoint app (p q: positive) : positive :=
  match p with
  | xH => q
  | xO p => xO (app p q)
  | xI p => xI (app p q)
  end.

Lemma app_xH: forall p, app p xH = p.
Proof.
  induction p; simpl; congruence.
Qed.

Lemma app_assoc: forall p q r, app (app p q) r = app p (app q r).
Proof.
  induction p; intros; simpl; auto; rewrite IHp; auto.
Qed.

Lemma app_inj: forall p q1 q2, app p q1 = app p q2 -> q1 = q2.
Proof.
  induction p; simpl; intros; auto; apply IHp; congruence.
Qed.

(** Viewing positive numbers as lists of bits, check that p is a prefix of q,
    and if so return the remainder of q. *)

Fixpoint prefix (p q: positive) {struct p} : option positive :=
  match p, q with
  | xH, _ => Some q
  | xO p, xO q => prefix p q
  | xI p, xI q => prefix p q
  | _, _ => None
  end.

Lemma prefix_charact: forall p q r,
  prefix p q = Some r <-> q = app p r.
Proof.
  induction p; intros; simpl.
- split; intros.
  + destruct q; try discriminate. apply IHp in H. congruence.
  + subst q. apply IHp. auto.
- split; intros.
  + destruct q; try discriminate. apply IHp in H. congruence.
  + subst q. apply IHp. auto.
- intuition congruence.
Qed.

Lemma prefix_app: forall p1 p2 i,
  prefix (app p1 p2) i =
    match prefix p1 i with
    | None => None
    | Some i1 => prefix p2 i1
    end.
Proof.
  intros. destruct (prefix p1 i) as [i1 | ] eqn:P1.
- apply prefix_charact in P1.
  destruct (prefix (app p1 p2) i) as [i2 | ] eqn:P2.
  + apply prefix_charact in P2.
    symmetry. apply prefix_charact. apply app_inj with p1. 
    rewrite <- app_assoc. congruence.
  + destruct (prefix p2 i1) as [i2 | ] eqn:P3; auto.
    apply prefix_charact in P3. subst i1. rewrite <- app_assoc in P1. apply prefix_charact in P1. congruence.
- destruct (prefix (app p1 p2) i) as [i1 | ] eqn: P; auto.
  apply prefix_charact in P. rewrite app_assoc in P. apply prefix_charact in P. congruence.
Qed.

(** Viewing positive numbers as lists of bits, find the longest common prefix
    between p and q.  Also return the suffixes. *)

Fixpoint common (p q: positive) {struct p} : positive * positive * positive :=
  match p, q with
  | xO p, xO q => let '(c, p', q') := common p q in (xO c, p', q')
  | xI p, xI q => let '(c, p', q') := common p q in (xI c, p', q')
  | _, _ => (xH, p, q)
  end.

Definition disagree (p q: positive) : Prop :=
  match p, q with
  | xO _, xO _ => False
  | xI _, xI _ => False
  | _, _ => True
  end.

Lemma common_charact: forall p q,
  let '(c, p', q') := common p q in
  p = app c p' /\ q = app c q' /\ disagree p' q'.
Proof.
  induction p; destruct q; simpl; auto.
- specialize (IHp q). destruct (common p q) as [[c p'] q']. simpl. intuition congruence. 
- specialize (IHp q). destruct (common p q) as [[c p'] q']. simpl. intuition congruence. 
Qed.

Module PTree.

(** ** Representation of Patricia tries *)

Inductive tree (A: Type) : Type :=
  | Leaf: tree A
  | Node: positive -> tree A -> option A -> tree A -> tree A.

(** In [Node p l x r], the [p] argument represents the list of bits that
    lead to this node.  The node is, then, a branch point, with
    an optional value [x] and a left subtree [l] and a right subtree [r],
    as in the other binary tries. *)

Arguments Leaf {A}.
Arguments Node [A].

Definition t := tree.

(** Smart constructor: avoids creating empty nodes and nodes where the
    prefix is not maximal. *)

Definition Node' (A: Type) (p: positive) (l: tree A) (x: option A) (r: tree A) : tree A :=
  match l, x, r with
  | Leaf, None, Leaf => Leaf
  | Node p1 l1 x1 r1, None, Leaf => Node (app p (xO p1)) l1 x1 r1
  | Leaf, None, Node p2 l2 x2 r2 => Node (app p (xI p2)) l2 x2 r2
  | _, _, _ => Node p l x r
  end.

(** ** Basic operations: [empty], [get], [set], [remove] *)

Definition empty (A: Type) : tree A := Leaf.

Fixpoint get (A: Type) (i: positive) (m: tree A) {struct m} : option A :=
  match m with
  | Leaf => None
  | Node p l x r =>
      match prefix p i with
      | None => None
      | Some xH => x
      | Some (xO ii) => get ii l
      | Some (xI ii) => get ii r
      end
  end.

Definition singleton (A: Type) (i: positive) (v: A) : tree A :=
  Node i Leaf (Some v) Leaf.

Fixpoint set (A: Type) (i: positive) (v: A) (m: tree A) {struct m} : tree A :=
  match m with
  | Leaf => singleton i v
  | Node p l x r =>
      match common p i with
      | (_, xH, xH) => Node p l (Some v) r
      | (_, xH, xO ii) => Node p (set ii v l) x r
      | (_, xH, xI ii) => Node p l x (set ii v r)
      | (c, xO pp, xH) => Node c (Node pp l x r) (Some v) Leaf
      | (c, xI pp, xH) => Node c Leaf (Some v) (Node pp l x r)
      | (c, xO pp, xI ii) => Node c (Node pp l x r) None (singleton ii v)
      | (c, xI pp, xO ii) => Node c (singleton ii v) None (Node pp l x r)
      | _ => Leaf   (*r never happens *)
      end
  end.

Fixpoint remove (A: Type) (i: positive) (m: tree A) {struct m} : tree A :=
  match m with
  | Leaf => Leaf
  | Node p l x r =>
      match prefix p i with
      | None => m
      | Some xH => Node' p l None r
      | Some (xO ii) => Node' p (remove ii l) x r
      | Some (xI ii) => Node' p l x (remove ii r)
      end
  end.

(** ** Relating Patricia trees with binary tries *)

(** As in "Functional algorithms, verified!", we transport some of the
    results for plain binary tries to Patricia binary tries via the
    following translation functions. *)

(** [transl m] produces the plain trie equivalent to the given Patricia
    trie.  No attempt is made to eliminate redundant nodes. *)

Fixpoint addpref {A: Type} (p: positive) (m: O.tree A) : O.tree A :=
  match p with
  | xH => m
  | xO pp => O.Node (addpref pp m) None O.Leaf
  | xI pp => O.Node O.Leaf None (addpref pp m)
  end.

Fixpoint transl {A: Type} (m: tree A) : O.tree A :=
  match m with
  | Leaf => O.Leaf
  | Node p l x r => addpref p (O.Node (transl l) x (transl r))
  end.

(** [transl' m] is similar but replaces empty nodes by leaves. *)

Fixpoint addpref' {A: Type} (p: positive) (m: O.tree A) : O.tree A :=
  match p with
  | xH => m
  | xO pp => O.Node' (addpref' pp m) None O.Leaf
  | xI pp => O.Node' O.Leaf None (addpref' pp m)
  end.

Fixpoint transl' {A: Type} (m: tree A) : O.tree A :=
  match m with
  | Leaf => O.Leaf
  | Node p l x r => addpref' p (O.Node' (transl' l) x (transl' r))
  end.

(** We now show commutation diagrams between the operations over Patricia tries
    and the same operations over the corresponding binary tries. *)

Lemma transl_get:
  forall {A: Type} (m: tree A) i,
  get i m = O.get i (transl m).
Proof.
  induction m; simpl.
- intros. auto.
- induction p as [ pp | pp | ]; simpl; intros; destruct i; auto.
Qed.

Lemma transl_singleton: forall {A: Type} (v: A) i,
  transl (singleton i v) = O.set i v O.Leaf.
Proof.
  unfold singleton; induction i; simpl; auto; f_equal; auto.
Qed.

Remark o_set_app: forall {A} (v: A) c i p t,
  O.set (app c i) v (addpref (app c p) t) = addpref c (O.set i v (addpref p t)).
Proof.
  induction c; simpl; intros; auto; f_equal; auto.
Qed.

Lemma transl_set:
  forall {A: Type} (v: A) (m: tree A) i,
  transl (set i v m) = O.set i v (transl m).
Proof.
  induction m; simpl.
- intros. apply transl_singleton.
- intros i. 
  generalize (common_charact p i). destruct (common p i) as [[c pp] ii] eqn:C.
  intros (E1 & E2 & DIS). rewrite E1, E2.
  rewrite o_set_app.
  destruct pp as [ pp | pp | ]; destruct ii as [ ii | ii | ]; simpl; try (elim DIS); auto.
  + f_equal. f_equal. apply transl_singleton.
  + f_equal. f_equal. apply transl_singleton.
  + rewrite app_xH. f_equal. f_equal. apply IHm2.
  + rewrite app_xH. f_equal. f_equal. apply IHm1.
  + rewrite app_xH. auto.
Qed.

Lemma gNode': forall {A} i p l (x: option A) r,
  get i (Node' p l x r) =
    match prefix p i with
    | None => None
    | Some xH => x
    | Some (xO ii) => get ii l
    | Some (xI ii) => get ii r
    end.
Proof.
  intros. destruct l, x, r; auto.
- destruct (prefix p i) as [[] | ]; auto.
- simpl. rewrite prefix_app. destruct (prefix p i) as [ii | ]; auto.
  simpl. destruct ii; auto. 
- simpl. rewrite prefix_app. destruct (prefix p i) as [ii | ]; auto.
  simpl. destruct ii; auto.
Qed.

Lemma transl'_get:
  forall {A: Type} (m: tree A) i,
  get i m = O.get i (transl' m).
Proof.
  Local Opaque O.Node'.
  induction m; simpl.
- intros. auto.
- induction p as [ pp | pp | ]; simpl; intros; rewrite O.gNode'; destruct i; auto.
Qed.

Lemma o_remove_node': forall {A: Type} i (l: O.tree A) x r,
  O.remove i (O.Node' l x r) =
    match i with
    | xH => O.Node' l None r
    | xO i => O.Node' (O.remove i l) x r
    | xI i => O.Node' l x (O.remove i r)
    end.
Proof.
  intros.
  assert (E: l = O.Leaf /\ x = None /\ r = O.Leaf \/ O.Node' l x r = O.Node l x r).
  { destruct l, x, r; auto. }
  destruct E as [(E1 & E2 & E3) | E]. 
  - subst l x r. simpl. destruct i; auto.
  - rewrite E; destruct i; simpl; auto.
Qed.

Lemma o_remove_notpref: forall {A} (m: O.tree A) p i,
  prefix p i = None -> O.remove i (addpref' p m) = addpref' p m.
Proof.
  Local Opaque O.Node'.
  induction p; intros.
- destruct i; simpl in *; rewrite o_remove_node'; f_equal; auto.
- destruct i; simpl in *; rewrite o_remove_node'; f_equal; auto.
- discriminate.
Qed.

Lemma o_remove_app: forall {A} p i (m: O.tree A),
  O.remove (app p i) (addpref' p m) = addpref' p (O.remove i m).
Proof.
  induction p; simpl; intros.
- rewrite o_remove_node'. f_equal; auto.
- rewrite o_remove_node'. f_equal; auto.
- auto.
Qed.

Lemma addpref'_app: forall {A} p q (m: O.tree A),
  addpref' (app p q) m = addpref' p (addpref' q m).
Proof.
  induction p; simpl; intros.
- f_equal; auto.
- f_equal; auto.
- auto.
Qed.

Lemma transl'_node': forall {A} p (l: tree A) x r,
  transl' (Node' p l x r) = addpref' p (O.Node' (transl' l) x (transl' r)).
Proof.
  intros. destruct l, x, r; auto.
- simpl. induction p; simpl; rewrite <- ? IHp; auto.
- simpl. rewrite addpref'_app. auto.
- simpl. rewrite addpref'_app. auto.
Qed.

Lemma transl_remove:
  forall {A: Type} (m: tree A) i,
  transl' (remove i m) = O.remove i (transl' m).
Proof.
  induction m; simpl; intros.
- auto.
- destruct (prefix p i) as [ii | ] eqn:P.
  + apply prefix_charact in P. subst i. rewrite o_remove_app.
    destruct ii; rewrite transl'_node', o_remove_node'; f_equal; auto; f_equal; auto.
  + rewrite o_remove_notpref by auto. auto.
Qed.

(** ** Good variable properties for the basic operations *)

(** Obtained by transporting the good variable properties for 
    plain binary tries. *)

Theorem gempty:
  forall {A} (i: positive), get i (empty A) = None.
Proof.
  auto.
Qed.

Theorem gss:
  forall {A} (i: positive) (x: A) (m: tree A), get i (set i x m) = Some x.
Proof.
  intros. rewrite transl_get, transl_set. apply O.gss.
Qed.

Theorem gso:
  forall {A} (i j: positive) (x: A) (m: tree A), i <> j -> get i (set j x m) = get i m.
Proof.
  intros. rewrite ! transl_get, transl_set. apply O.gso; auto.
Qed.

Theorem grs:
  forall {A} (i: positive) (m: tree A), get i (remove i m) = None.
Proof.
  intros. rewrite transl'_get, transl_remove. apply O.grs. 
Qed.

Theorem gro:
  forall {A} (i j: positive) (m: tree A),
  i <> j -> get i (remove j m) = get i m.
Proof.
  intros. rewrite ! transl'_get, transl_remove. apply O.gro; auto.
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
  | Node p l o r => Node' p (map_filter f l) (option_map f o) (map_filter f r)
  end.

Lemma gmap_filter:
  forall (f: A -> option B) (m: tree A) (i: positive),
  get i (map_filter f m) = option_map f (get i m).
Proof.
  induction m; intros; simpl.
  - auto.
  - rewrite gNode'. destruct (prefix p i) as [i'|]; auto. destruct i'; auto.
Qed.

End MAP_FILTER.

(** The [combine] operation traverses two tries in parallel,
    applying a function [f: option A -> option B -> option C]
    at each node to build the resulting trie. *)

Section COMBINE.

Variables A B C: Type.
Variable f: option A -> option B -> option C.
Hypothesis f_None_None: f None None = None.

Let combine_r := map_filter (fun b => f None (Some b)).
Let combine_l := map_filter (fun a => f (Some a) None).

Fixpoint combine (m1: tree A) (m2: tree B): tree C :=
  match m1 with
  | Leaf => combine_r m2
  | Node p1 l1 o1 r1 =>
      let fix combi (p1: positive) (m2: tree B) : tree C :=
        match m2, p1 with
        | Leaf, _ => combine_l (Node p1 l1 o1 r1)
        | Node xH l2 o2 r2, xH => Node' xH (combine l1 l2) (f o1 o2) (combine r1 r2)
        | Node xH l2 o2 r2, xO p1 => Node' xH (combi p1 l2) (f None o2) (combine_r r2)
        | Node xH l2 o2 r2, xI p1 => Node' xH (combine_r l2) (f None o2) (combi p1 r2)
        | Node (xO p2) l2 o2 r2, xH => Node' xH (combine l1 (Node p2 l2 o2 r2)) (f o1 None) (combine_l r1)
        | Node (xO p2) l2 o2 r2, xO p1 => Node' xH (combi p1 (Node p2 l2 o2 r2)) None Leaf
        | Node (xO p2) l2 o2 r2, xI p1 => Node' xH (combine_r (Node p2 l2 o2 r2)) None (combine_l (Node p1 l1 o1 r1))
        | Node (xI p2) l2 o2 r2, xH => Node' xH (combine_l l1) (f o1 None) (combine r1 (Node p2 l2 o2 r2))
        | Node (xI p2) l2 o2 r2, xO p1 => Node' xH (combine_l (Node p1 l1 o1 r1)) None (combine_r (Node p2 l2 o2 r2))
        | Node (xI p2) l2 o2 r2, xI p1 => Node' xH Leaf None (combi p1 (Node p2 l2 o2 r2))
        end
      in combi p1 m2
  end.

Lemma gcombine_l: forall i m1, get i (combine_l m1) = f (get i m1) None.
Proof.
  unfold combine_l; intros. rewrite gmap_filter. destruct (get i m1); auto.
Qed.

Lemma gcombine_r: forall i m2, get i (combine_r m2) = f None (get i m2).
Proof.
  unfold combine_r; intros. rewrite gmap_filter. destruct (get i m2); auto.
Qed.

Lemma gNode'1: forall {A} i l (x: option A) r,
  get i (Node' xH l x r) =
    match i with xH => x | xO ii => get ii l | xI ii => get ii r end.
Proof.
  intros. rewrite gNode'. auto.
Qed.

Lemma gcombine:
  forall (m1: tree A) (m2: tree B) (i: positive),
  get i (combine m1 m2) = f (get i m1) (get i m2).
Proof.
  Local Opaque map_filter.
  Local Opaque Node'.
  induction m1; simpl; intros.
- apply gcombine_r.
- rename m1_1 into l1, o into o1, m1_2 into r1. revert m2 i.
  induction p; destruct m2 as [ | p2 l2 o2 r2]; intros; try (apply gcombine_l); destruct p2 as [ p2 | p2 | ]; rewrite ? gNode'1.
  + destruct i; auto. rewrite IHp; auto.
  + destruct i; rewrite ? gcombine_l, ? gcombine_r; auto.
  + destruct i; rewrite ? gcombine_r; auto. rewrite IHp; auto.
  + destruct i; rewrite ? gcombine_l, ? gcombine_r; auto.
  + destruct i; auto. rewrite IHp; auto.
  + destruct i; rewrite ? gcombine_r; auto. rewrite IHp; auto.
  + destruct i; rewrite ? gcombine_l; auto. rewrite IHm1_2; auto.
  + destruct i; rewrite ? gcombine_l; auto. rewrite IHm1_1; auto.
  + destruct i; auto. rewrite IHm1_2; auto. rewrite IHm1_1; auto.
Qed.

End COMBINE.

End PTree.

