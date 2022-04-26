
(** * Finite Modular Maps : AVL Trees *)

(** Author : Pierre Letouzey (Université de Paris - INRIA),
    adapted from earlier works in Coq Standard Library, see README.md.
    Licence : LGPL 2.1, see file LICENSE. *)

(** This module implements maps using AVL trees.
    It follows the implementation from Ocaml's standard library.

    See the comments at the beginning of MSetAVL for more details.

    Note that we only prove here that the operations below preserve
    the binary search tree invariant ([Bst], a.k.a [Ok] predicate here),
    but *not* the AVL balancing invariant. Indeed, the former is enough
    to implement the desired interface [S], and ensure observational
    correctness. And proceeding this way is quite lighter. For the
    proofs of AVL balancing, see [Tries.MMaps.AVLproofs].
*)

From Coq Require Import Bool PeanoNat BinInt FunInd Int.
From Coq Require Import Orders OrdersFacts OrdersLists.
From Tries.MMaps Require Import Utils Interface OrdList GenTree.

Local Set Implicit Arguments.
Local Unset Strict Implicit.
(* For nicer extraction, we create inductive principles only when needed *)
Local Unset Elimination Schemes.

(** * The Raw functor

   Functor of pure functions + separate proofs of invariant
   preservation *)

Module MakeRaw (Import I:Int)(K: OrderedType) <: Raw.S K.

(** ** Generic trees instantiated with integer height *)

(** We reuse a generic definition of trees where the information
    parameter is a [Int.t]. Functions like mem or fold are also
    provided by this generic functor. *)

Include Tries.MMaps.GenTree.Ops K I.
Import GenTree.PairNotations. (* #1 and #2 for fst and snd *)
Local Open Scope lazy_bool_scope.
Local Open Scope Int_scope.
Local Notation int := I.t.

Section Elt.
Variable elt : Type.
Local Notation t := (tree elt).
Implicit Types l r m : t.
Implicit Types e : elt.

(** * Basic functions on trees: height and cardinal *)

Definition height (m : t) : int :=
  match m with
  | Leaf _ => 0
  | Node h _ _ _ _ => h
  end.

(** * Singleton set *)

Definition singleton x e := Node 1 (Leaf _) x e (Leaf _).

(** * Helper functions *)

(** [create l x r] creates a node, assuming [l] and [r]
    to be balanced and [|height l - height r| <= 2]. *)

Definition create l x e r :=
   Node (max (height l) (height r) + 1) l x e r.

(** [bal l x e r] acts as [create], but performs one step of
    rebalancing if necessary, i.e. assumes [|height l - height r| <= 3]. *)

Definition assert_false := create.

Definition bal l x d r :=
  let hl := height l in
  let hr := height r in
  if (hr+2) <? hl then
    match l with
     | Leaf _ => assert_false l x d r
     | Node _ ll lx ld lr =>
       if (height lr) <=? (height ll) then
         create ll lx ld (create lr x d r)
       else
         match lr with
          | Leaf _ => assert_false l x d r
          | Node _ lrl lrx lrd lrr =>
              create (create ll lx ld lrl) lrx lrd (create lrr x d r)
         end
    end
  else
    if (hl+2) <? hr then
      match r with
       | Leaf _ => assert_false l x d r
       | Node _ rl rx rd rr =>
         if (height rl) <=? (height rr) then
            create (create l x d rl) rx rd rr
         else
           match rl with
            | Leaf _ => assert_false l x d r
            | Node _ rll rlx rld rlr =>
                create (create l x d rll) rlx rld (create rlr rx rd rr)
           end
      end
    else
      create l x d r.

(** * Insertion *)

Fixpoint add x d m :=
  match m with
    | Leaf _ => Node 1 (Leaf _) x d (Leaf _)
    | Node h l y d' r =>
      match K.compare x y with
        | Eq => Node h l y d r
        | Lt => bal (add x d l) y d' r
        | Gt => bal l y d' (add x d r)
      end
  end.

(** * Extraction of minimum binding

  Morally, [remove_min] is to be applied to a non-empty tree
  [t = Node l x e r h]. Since we can't deal here with [assert false]
  for [t=Leaf], we pre-unpack [t] (and forget about [h]).
*)

Fixpoint remove_min l x d r : t*(key*elt) :=
  match l with
    | Leaf _ => (r,(x,d))
    | Node lh ll lx ld lr =>
       let (l',m) := remove_min ll lx ld lr in
       (bal l' x d r, m)
  end.

(** * Appending two disjoint maps of similar heights

  [append t1 t2] builds the union of [t1] and [t2] assuming all keys
  of [t1] to be smaller than all keys of [t2], and
  [|height t1 - height t2| <= 2].

  This was named [merge] in the initial Set implementation.
*)

Definition append s1 s2 :=
  match s1,s2 with
    | Leaf _, _ => s2
    | _, Leaf _ => s1
    | _, Node h2 l2 x2 d2 r2 =>
      let '(s2',(x,d)) := remove_min l2 x2 d2 r2 in
      bal s1 x d s2'
  end.

(** * Deletion *)

Fixpoint remove x m := match m with
  | Leaf _ => Leaf _
  | Node h l y d r =>
      match K.compare x y with
         | Eq => append l r
         | Lt => bal (remove x l) y d r
         | Gt => bal l y d (remove x r)
      end
   end.

(** * join

    Same as [bal] but does not assume anything regarding heights of [l]
    and [r].
*)

Fixpoint join l : key -> elt -> t -> t :=
  match l with
    | Leaf _ => add
    | Node lh ll lx ld lr => fun x d =>
       fix join_aux (r:t) : t := match r with
          | Leaf _ => add x d l
          | Node rh rl rx rd rr =>
            if rh+2 <? lh then bal ll lx ld (join lr x d r)
            else if lh+2 <? rh then bal (join_aux rl) rx rd rr
            else create l x d r
          end
  end.

(** * Splitting

    [split x m] returns a triple [(l, o, r)] where
    - [l] is the set of elements of [m] that are [< x]
    - [r] is the set of elements of [m] that are [> x]
    - [o] is the result of [find x m].
*)

Record triple := Triple { t_left:t; t_opt:option elt; t_right:t }.

Fixpoint split x m : triple := match m with
  | Leaf _ => Triple (Leaf _) None (Leaf _)
  | Node h l y d r =>
     match K.compare x y with
      | Lt => let (ll,o,rl) := split x l in Triple ll o (join rl y d r )
      | Eq => Triple l (Some d) r
      | Gt => let (rl,o,rr) := split x r in Triple (join l y d rl) o rr
     end
 end.

(** * Concatenation

   Same as [append] but does not assume anything about heights.
*)

Definition concat m1 m2 :=
   match m1, m2 with
      | Leaf _, _ => m2
      | _ , Leaf _ => m1
      | _, Node _ l2 x2 d2 r2 =>
            let (m2',xd) := remove_min l2 x2 d2 r2 in
            join m1 xd#1 xd#2 m2'
   end.

(** Filter and partition *)

Fixpoint filter (f:key->elt->bool) m :=
  match m with
  | Leaf _ => Leaf _
  | Node _ l x e r =>
    let l' := filter f l in
    let r' := filter f r in
    if f x e then join l' x e r' else concat l' r'
  end.

Fixpoint partition (f:key->elt->bool) m :=
  match m with
  | Leaf _ => (Leaf _, Leaf _)
  | Node _ l x e r =>
    let '(l1,l2) := partition f l in
    let '(r1,r2) := partition f r in
    if f x e then
      (join l1 x e r1, concat l2 r2)
    else
      (concat l1 r1, join l2 x e r2)
  end.

End Elt.
Local Notation "t #l" := (t_left t) (at level 9, format "t '#l'").
Local Notation "t #o" := (t_opt t) (at level 9, format "t '#o'").
Local Notation "t #r" := (t_right t) (at level 9, format "t '#r'").

(** * Map with removal *)

Fixpoint mapo (elt elt' : Type)(f : key -> elt -> option elt')(m : t elt)
  : t elt' :=
  match m with
   | Leaf _ => Leaf _
   | Node _ l x d r =>
      match f x d with
       | Some d' => join (mapo f l) x d' (mapo f r)
       | None => concat (mapo f l) (mapo f r)
      end
  end.

(** * Generalized merge

  Suggestion by B. Gregoire: a [merge] function with specialized
  arguments that allows bypassing some tree traversal. Instead of one
  [f0] of type [key -> option elt -> option elt' -> option elt''],
  we ask here for:
  - [f] which is a specialisation of [f0] when first option isn't [None]
  - [mapl] treats a [tree elt] with [f0] when second option is [None]
  - [mapr] treats a [tree elt'] with [f0] when first option is [None]

  The idea is that [mapl] and [mapr] can be instantaneous (e.g.
  the identity or some constant function).
*)

Section GMerge.
Variable elt elt' elt'' : Type.
Variable f : key -> elt -> option elt' -> option elt''.
Variable mapl : t elt -> t elt''.
Variable mapr : t elt' -> t elt''.

Fixpoint gmerge m1 m2 :=
 match m1, m2 with
  | Leaf _, _ => mapr m2
  | _, Leaf _ => mapl m1
  | Node h1 l1 x1 d1 r1, _ =>
     let (l2',o2,r2') := split x1 m2 in
     match f x1 d1 o2 with
      | Some e => join (gmerge l1 l2') x1 e (gmerge r1 r2')
      | None => concat (gmerge l1 l2') (gmerge r1 r2')
     end
 end.

End GMerge.

(** * Merge

    The [merge] function of the Map interface can be implemented
    via [gmerge] and [mapo].
*)

Section Merge.
Variable elt elt' elt'' : Type.
Variable f : key -> option elt -> option elt' -> option elt''.

Definition merge : t elt -> t elt' -> t elt'' :=
 gmerge
   (fun k d o => f k (Some d) o)
   (mapo (fun k d => f k (Some d) None))
   (mapo (fun k d' => f k None (Some d'))).

End Merge.

(** * Correctness proofs *)

Include Tries.MMaps.GenTree.Props K I.
Import Ind.

Local Infix "∈" := In (at level 70).
Local Infix "==" := K.eq (at level 70).
Local Infix "<" := lessthan.
Local Notation "m @ x ↦ e" := (MapsTo x e m)
 (at level 9, format "m '@' x  '↦'  e").

Functional Scheme bal_ind := Induction for bal Sort Prop.
Functional Scheme add_ind := Induction for add Sort Prop.
Functional Scheme remove_min_ind := Induction for remove_min Sort Prop.
Functional Scheme append_ind := Induction for append Sort Prop.
Functional Scheme remove_ind := Induction for remove Sort Prop.
Functional Scheme concat_ind := Induction for concat Sort Prop.
Functional Scheme split_ind := Induction for split Sort Prop.
Functional Scheme mapo_ind := Induction for mapo Sort Prop.
Functional Scheme gmerge_ind := Induction for gmerge Sort Prop.

(** * Automation and dedicated tactics. *)

Local Hint Constructors tree MapsTo Bst : map.
Local Hint Unfold Ok Bst_Ok In : map.
Local Hint Immediate F.eq_sym : map.
Local Hint Resolve F.eq_refl : map.
Local Hint Resolve above_notin above_trans below_notin below_trans : map.
Local Hint Resolve above_leaf below_leaf : map.

(* Function/Functional Scheme can't deal with internal fix.
   Let's do its job by hand: *)

Ltac join_tac l x d r :=
 revert x d r;
 induction l as [| lh ll _ lx ld lr Hlr];
   [ | intros x d r; induction r as [| rh rl Hrl rx rd rr _]; unfold join;
     [ | destruct (rh+2 <? lh) eqn:LT;
       [ match goal with |- context [ bal ?u ?v ?w ?z ] =>
           replace (bal u v w z)
           with (bal ll lx ld (join lr x d (Node rh rl rx rd rr))); [ | auto]
         end
       | destruct (lh+2 <? rh) eqn:LT';
         [ match goal with |- context [ bal ?u ?v ?w ?z ] =>
             replace (bal u v w z)
             with (bal (join (Node lh ll lx ld lr) x d rl) rx rd rr); [ | auto]
           end
         | ] ] ] ]; intros.

Ltac cleansplit :=
  simpl; cleanf; invok;
  match goal with
  | E:split _ _ = Triple ?l ?o ?r |- _ =>
    change l with ((Triple l o r)#l); rewrite <- ?E;
    change o with ((Triple l o r)#o); rewrite <- ?E;
    change r with ((Triple l o r)#r); rewrite <- ?E
  | _ => idtac
  end.

Section Elt.
Variable elt:Type.
Implicit Types x y : K.t.
Implicit Types m r : t elt.

(** * Helper functions *)

Global Instance create_ok l x e r `{!Ok l, !Ok r} :
 l < x -> x < r -> Ok (create l x e r).
Proof.
 unfold create; autok.
Qed.

Lemma create_in l x e r y :
  y ∈ (create l x e r) <-> y == x \/ y ∈ l \/ y ∈ r.
Proof.
 unfold create. intuition_in.
Qed.

Lemma create_bindings l x e r :
 bindings (create l x e r) = bindings l ++ (x,e) :: bindings r.
Proof.
 apply bindings_node.
Qed.

Global Instance bal_ok l x e r `{!Ok l, !Ok r} :
 l < x -> x < r -> Ok (bal l x e r).
Proof.
 functional induction (bal l x e r); intros; cleanf; invok; invlt;
 repeat apply create_ok; rewrite ?above_node, ?below_node; intuition;
 intro; rewrite create_in; intuition; order.
Qed.

Lemma bal_mapsto l x e r y e' :
 MapsTo y e' (bal l x e r) <-> MapsTo y e' (create l x e r).
Proof.
 functional induction (bal l x e r); intros; cleanf;
 unfold assert_false, create; intuition_m.
Qed.

Lemma bal_in l x e r y :
 y ∈ (bal l x e r) <-> y == x \/ y ∈ l \/ y ∈ r.
Proof.
 unfold In. setoid_rewrite bal_mapsto. unfold create.
 setoid_rewrite node_mapsto. firstorder. exists e; firstorder.
Qed.

Lemma bal_find l x e r y `{!Ok l, !Ok r} :
 l < x -> x < r -> find y (bal l x e r) = find y (create l x e r).
Proof.
 functional induction (bal l x e r); intros; cleanf; trivial;
 invok; invlt; simpl;
 repeat case K.compare_spec; intuition; order.
Qed.

Lemma bal_bindings l x e r :
 bindings (bal l x e r) = bindings (create l x e r).
Proof.
 functional induction (bal l x e r); intros; cleanf; auto.
Qed.

(** singleton *)

Lemma singleton_spec x (e:elt) : bindings (singleton x e) = (x,e)::nil.
Proof.
 unfold singleton. now rewrite bindings_node.
Qed.

Global Instance singleton_ok x (e:elt) : Ok (singleton x e).
Proof.
 unfold singleton. autok.
Qed.

(** * Insertion *)

Lemma add_in m x y e :
 y ∈ (add x e m) <-> y == x \/ y ∈ m.
Proof.
 functional induction (add x e m); auto; intros; cleanf;
 rewrite ?bal_in; intuition_in. setoid_replace y with x; auto.
Qed.

Lemma add_lt m x e y : m < y -> x < y -> add x e m < y.
Proof.
 intros ? ? z. rewrite add_in. destruct 1; order.
Qed.

Lemma add_gt m x e y : y < m -> y < x -> y < add x e m.
Proof.
 intros ? ? z. rewrite add_in. destruct 1; order.
Qed.
Local Hint Resolve add_lt add_gt : map.

Global Instance add_ok m x e `{!Ok m} : Ok (add x e m).
Proof.
 functional induction (add x e m); intros; cleanf; invok; autok.
Qed.

Lemma add_spec1 m x e `{!Ok m} : find x (add x e m) = Some e.
Proof.
 functional induction (add x e m); simpl; intros; cleanf; trivial.
 - now rewrite F.compare_refl.
 - invok. rewrite bal_find; autok.
   simpl. case K.compare_spec; try order; auto.
 - invok. rewrite bal_find; autok.
   simpl. case K.compare_spec; try order; auto.
Qed.

Lemma add_spec2 m x y e `{!Ok m} : ~ x == y ->
 find y (add x e m) = find y m.
Proof.
 functional induction (add x e m); simpl; intros; cleanf; trivial.
 - case K.compare_spec; trivial; order.
 - case K.compare_spec; trivial; order.
 - invok. rewrite bal_find by autok. simpl. now rewrite IHt0.
 - invok. rewrite bal_find by autok. simpl. now rewrite IHt0.
Qed.

Lemma add_find m x y e `{!Ok m} :
 find y (add x e m) =
  match K.compare y x with Eq => Some e | _ => find y m end.
Proof.
 case K.compare_spec; intros E.
 - apply find_spec; autok. rewrite E. apply find_spec; autok.
   now apply add_spec1.
 - apply add_spec2; trivial; order.
 - apply add_spec2; trivial; order.
Qed.

Lemma add_below_bindings x e m :
  x < m ->
  bindings (add x e m) = (x, e) :: bindings m.
Proof.
 functional induction (add x e m); simpl; intros; cleanf; trivial;
 invlt; try (intuition; order).
 rewrite bal_bindings. unfold create. rewrite !bindings_node.
 now rewrite IHt0.
Qed.

Lemma add_above_bindings x e m :
  m < x ->
  bindings (add x e m) = bindings m ++ (x,e) :: nil.
Proof.
 functional induction (add x e m); simpl; intros; cleanf; trivial;
 invlt; try (intuition; order).
 rewrite bal_bindings. unfold create. rewrite !bindings_node.
 rewrite app_ass. f_equal. simpl. f_equal. intuition.
Qed.

(** * Extraction of minimum binding *)

Definition RemoveMin m res :=
 match m with
 | Leaf _ => False
 | Node h l x e r => remove_min l x e r = res
 end.

Lemma RemoveMin_step l x e r h m' p :
 RemoveMin (Node h l x e r) (m',p) ->
 (l = Leaf _ /\ m' = r /\ p = (x,e) \/
  exists m0, RemoveMin l (m0,p) /\ m' = bal m0 x e r).
Proof.
 simpl. destruct l as [|lh ll lx le lr]; simpl.
 - intros [= <- <-]. now left.
 - destruct (remove_min ll lx le lr) as (l',p').
   intros [= <- <-]. right. now exists l'.
Qed.

Lemma remove_min_mapsto m m' p : RemoveMin m (m',p) ->
 forall y e,
 MapsTo y e m <-> (y == p#1 /\ e = p#2) \/ MapsTo y e m'.
Proof.
 revert m'.
 induction m as [|h l IH x d r _]; [destruct 1|].
 intros m' R. apply RemoveMin_step in R.
 destruct R as [(->,(->,->))|[m0 (R,->)]]; intros y e; simpl.
 - intuition_m. subst. now constructor.
 - rewrite bal_mapsto. unfold create. specialize (IH _ R y e).
   intuition_m.
Qed.

Lemma remove_min_in m m' p : RemoveMin m (m',p) ->
 forall y, y ∈ m <-> y == p#1 \/ y ∈ m'.
Proof.
 intros H y. unfold In. assert (H' := remove_min_mapsto H y).
 firstorder. exists (p#2). rewrite H'. now left.
Qed.

Lemma remove_min_lt m m' p : RemoveMin m (m',p) ->
 forall y, m < y -> m' < y.
Proof.
 intros R y L z Hz. apply L. apply (remove_min_in R). now right.
Qed.
Local Hint Resolve remove_min_lt : map.

Lemma remove_min_gt m m' p `{!Ok m} : RemoveMin m (m',p) ->
 p#1 < m'.
Proof.
 revert m'.
 induction m as [|h l IH x e r _]; [destruct 1|].
 intros m' R. invok. apply RemoveMin_step in R.
 destruct R as [(_,(->,->))|[m0 (R,->)]]; auto.
 assert (p#1 < m0) by now apply IH.
 assert (p#1 ∈ l) by (apply (remove_min_in R); now left).
 intros z. rewrite bal_in. intuition; order.
Qed.

Global Instance remove_min_ok m m' p `{!Ok m} : RemoveMin m (m',p) -> Ok m'.
Proof.
 revert m'.
 induction m as [|h l IH x e r _]; [destruct 1|].
 intros m' R. invok. apply RemoveMin_step in R.
 destruct R as [(_,(->,->))|[m0 (R,->)]]; eauto with *.
Qed.

Lemma remove_min_find m m' p `{!Ok m} : RemoveMin m (m',p) ->
 forall y,
 find y m =
   match K.compare y p#1 with
    | Eq => Some p#2
    | Lt => None
    | Gt => find y m'
   end.
Proof.
 revert m'.
 induction m as [|h l IH x e r _]; [destruct 1|].
 intros m' R y. invok.
 apply RemoveMin_step in R.
 destruct R as [(->,(->,->))|[m0 (R,->)]]; auto.
 assert (Ok m0) by now apply remove_min_ok in R.
 assert (p#1 < m0) by now apply remove_min_gt in R.
 assert (m0 < x) by now apply (remove_min_lt R).
 assert (p#1 ∈ l) by (apply (remove_min_in R); now left).
 simpl in *.
 rewrite (IH _ _ R), bal_find by trivial. clear IH. simpl.
 do 2 case K.compare_spec; trivial; order.
Qed.

Lemma remove_min_bindings m m' p : RemoveMin m (m',p) ->
 bindings m = p :: bindings m'.
Proof.
 revert m'.
 induction m as [|h l IH x e r _]; [destruct 1|].
 intros m' R.
 apply RemoveMin_step in R.
 destruct R as [(->,(->,->))|[m0 (R,->)]]; auto.
 rewrite bal_bindings, create_bindings, bindings_node.
 now rewrite (IH _ R).
Qed.

(** * Merging two trees *)

Ltac factor_remove_min m R := match goal with
 | h:int, H:remove_min ?l ?x ?e ?r = ?p |- _ =>
   assert (R:RemoveMin (Node h l x e r) p) by exact H;
   set (m:=Node h l x e r) in *; clearbody m; clear H l x e r
end.

Lemma append_mapsto m1 m2 y e :
 MapsTo y e (append m1 m2) <-> MapsTo y e m1 \/ MapsTo y e m2.
Proof.
 functional induction (append m1 m2); intros; try factornode m1.
 - intuition_m.
 - intuition_m.
 - factor_remove_min l R. rewrite bal_mapsto, (remove_min_mapsto R).
   simpl. unfold create; intuition_m. subst. now constructor.
Qed.

Lemma append_in m1 m2 y :
  y ∈ (append m1 m2) <-> y ∈ m1 \/ y ∈ m2.
Proof.
 unfold In. setoid_rewrite append_mapsto. firstorder.
Qed.

Global Instance append_ok m1 m2 `{!Ok m1, !Ok m2} : m1 < m2 ->
 Ok (append m1 m2).
Proof.
 functional induction (append m1 m2); intros B12; trivial.
 factornode m1. factor_remove_min l R.
 apply bal_ok; eauto with *.
 - intros z Hz. apply B12; trivial. rewrite (remove_min_in R). now left.
 - now apply (remove_min_gt R).
Qed.

(** * Deletion *)

Lemma remove_in m x y `{!Ok m} :
 y ∈ remove x m <-> ~ y == x /\ y ∈ m.
Proof.
 functional induction (remove x m); simpl; intros; cleanf; invok;
  rewrite ?append_in, ?bal_in, ?IHt; intuition_in; order.
Qed.

Lemma remove_lt m x y `{!Ok m} : m < y -> remove x m < y.
Proof.
 intros ? z. rewrite remove_in by trivial. destruct 1; order.
Qed.

Lemma remove_gt m x y `{!Ok m} : y < m -> y < remove x m.
Proof.
 intros ? z. rewrite remove_in by trivial. destruct 1; order.
Qed.
Local Hint Resolve remove_gt remove_lt : map.

Global Instance remove_ok m x `{!Ok m} : Ok (remove x m).
Proof.
 functional induction (remove x m); simpl; intros; cleanf; invok; autok.
 apply append_ok; eauto using between.
Qed.

Lemma remove_spec1 m x `{!Ok m} : find x (remove x m) = None.
Proof.
 intros. apply not_find_iff; autok. rewrite remove_in; intuition.
Qed.

Lemma remove_spec2 m x y `{!Ok m} : ~ x == y ->
 find y (remove x m) = find y m.
Proof.
 functional induction (remove x m); simpl; intros; cleanf; invok; autok.
 - case K.compare_spec; intros; try order;
   rewrite find_mapsto_equiv; eauto using append_ok, between;
    intros; rewrite append_mapsto; intuition; order.
 - rewrite bal_find by autok. simpl. case K.compare_spec; auto.
 - rewrite bal_find by autok. simpl. case K.compare_spec; auto.
Qed.

(** * join *)

Lemma join_in l x d r y :
 y ∈ (join l x d r) <-> y == x \/ y ∈ l \/ y ∈ r.
Proof.
 join_tac l x d r.
 - simpl join. rewrite add_in; intuition_in.
 - rewrite add_in; intuition_in.
 - rewrite bal_in, Hlr. clear Hlr Hrl. intuition_in.
 - rewrite bal_in, Hrl. clear Hlr Hrl. intuition_in.
 - apply create_in.
Qed.

Global Instance join_ok l x d r :
 Ok (create l x d r) -> Ok (join l x d r).
Proof.
  join_tac l x d r; unfold create in *; invok; invok; invlt; autok.
  - simpl. autok.
  - apply bal_ok; auto.
    + apply Hlr; ok; intuition.
    + intro. rewrite join_in; intuition_in; order.
  - apply bal_ok; auto.
    + apply Hrl; ok; intuition.
    + intro. rewrite join_in; intuition_in; order.
  - ok; intuition.
Qed.

Lemma join_find l x d r y :
 Ok (create l x d r) ->
 find y (join l x d r) = find y (create l x d r).
Proof.
 unfold create at 1.
 join_tac l x d r; trivial.
 - simpl in *. invok.
   rewrite add_find; trivial.
   case K.compare_spec; intros; trivial.
   apply not_find_iff; auto. intro. order.
 - clear Hlr. factornode l. simpl. invok.
   rewrite add_find by auto.
   case K.compare_spec; intros; trivial.
   apply not_find_iff; auto. intro. order.
 - clear Hrl LT. factornode r. invok; invlt;
   rewrite bal_find; autok; simpl.
   + rewrite Hlr by (ok; intuition). simpl.
     do 2 (case K.compare_spec; intuition; try order).
   + apply join_ok, create_ok; ok; intuition.
   + intro. rewrite join_in. intuition; order.
 - clear Hlr LT LT'. factornode l. invok; invlt;
   rewrite bal_find; autok; simpl.
   + rewrite Hrl by (ok; intuition). simpl.
     do 2 (case K.compare_spec; intuition; try order).
   + apply join_ok, create_ok; ok; intuition.
   + intro. rewrite join_in. intuition; order.
Qed.

Lemma join_bindings l x d r :
 Ok (create l x d r) ->
 bindings (join l x d r) = bindings (create l x d r).
Proof.
 unfold create at 1.
 join_tac l x d r; trivial.
 - simpl in *. invok.
   rewrite create_bindings. now apply add_below_bindings.
 - clear Hlr. factornode l. invok.
   rewrite create_bindings. now apply add_above_bindings.
 - clear Hrl LT. factornode r. invok; invlt.
   rewrite bal_bindings, !create_bindings, bindings_node.
   rewrite app_ass; simpl. f_equal. f_equal.
   now rewrite Hlr, create_bindings by (ok; intuition).
 - clear Hlr LT LT'. factornode l. invok; invlt.
   rewrite bal_bindings, !create_bindings, bindings_node.
   now rewrite Hrl, create_bindings, app_ass by (ok; intuition).
Qed.

(** * split *)

Lemma split_in_l0 m x y : y ∈ (split x m)#l -> y ∈ m.
Proof.
  functional induction (split x m); cleansplit;
  rewrite ?join_in; intuition_in.
Qed.

Lemma split_in_r0 m x y : y ∈ (split x m)#r -> y ∈ m.
Proof.
  functional induction (split x m); cleansplit;
  rewrite ?join_in; intuition_in.
Qed.

Lemma split_in_l m x y `{!Ok m} :
 (y ∈ (split x m)#l <-> y ∈ m /\ y < x).
Proof.
  functional induction (split x m); intros; cleansplit;
  rewrite ?join_in, ?IHt; intuition_in; order.
Qed.

Lemma split_in_r m x y `{!Ok m} :
 (y ∈ (split x m)#r <-> y ∈ m /\ x < y).
Proof.
  functional induction (split x m); intros; cleansplit;
  rewrite ?join_in, ?IHt; intuition_in; order.
Qed.

Lemma split_in_o m x : (split x m)#o = find x m.
Proof.
  functional induction (split x m); intros; cleansplit; auto.
Qed.

Lemma split_lt_l m x `{!Ok m} : (split x m)#l < x.
Proof.
  intro. rewrite split_in_l; intuition; order.
Qed.

Lemma split_lt_r m x y : m < y -> (split x m)#r < y.
Proof.
  intros ? z Hz. apply split_in_r0 in Hz. order.
Qed.

Lemma split_gt_r m x `{!Ok m} : x < (split x m)#r.
Proof.
  intro. rewrite split_in_r; intuition; order.
Qed.

Lemma split_gt_l m x y : y < m -> y < (split x m)#l.
Proof.
  intros ? z Hz. apply split_in_l0 in Hz. order.
Qed.
Local Hint Resolve split_lt_l split_lt_r split_gt_l split_gt_r : map.

Global Instance split_ok_l m x `{!Ok m} : Ok (split x m)#l.
Proof.
  functional induction (split x m); intros; cleansplit; intuition.
Qed.

Global Instance split_ok_r m x `{!Ok m} : Ok (split x m)#r.
Proof.
  functional induction (split x m); intros; cleansplit; intuition.
Qed.

Lemma split_find m x y `{!Ok m} :
 find y m = match K.compare y x with
              | Eq => (split x m)#o
              | Lt => find y (split x m)#l
              | Gt => find y (split x m)#r
            end.
Proof.
 functional induction (split x m); intros; cleansplit.
 - now case K.compare.
 - repeat case K.compare_spec; trivial; order.
 - simpl in *. rewrite join_find, IHt0; autok.
   simpl. repeat case K.compare_spec; trivial; order.
 - rewrite join_find, IHt0; autok.
   simpl; repeat case K.compare_spec; trivial; order.
Qed.

(** * Concatenation *)

Lemma concat_in m1 m2 y :
 y ∈ (concat m1 m2) <-> y ∈ m1 \/ y ∈ m2.
Proof.
 functional induction (concat m1 m2); intros; try factornode m1.
 - intuition_in.
 - intuition_in.
 - factor_remove_min m2 R.
   rewrite join_in, (remove_min_in R); simpl; intuition.
Qed.

Global Instance concat_ok m1 m2 `{!Ok m1, !Ok m2} : m1 < m2 ->
 Ok (concat m1 m2).
Proof.
  functional induction (concat m1 m2); intros LT; auto;
  try factornode m1.
  factor_remove_min m2 R.
  apply join_ok, create_ok; auto.
  - now apply remove_min_ok in R.
  - intros y Hy. apply LT; trivial. rewrite (remove_min_in R); now left.
  - now apply (remove_min_gt R).
Qed.

Definition oelse {A} (o1 o2:option A) :=
  match o1 with
  | Some x => Some x
  | None => o2
  end.

Lemma concat_find m1 m2 y `{!Ok m1, !Ok m2} : m1 < m2 ->
 find y (concat m1 m2) = oelse (find y m2) (find y m1).
Proof.
 functional induction (concat m1 m2); intros B; auto; try factornode m1.
 - destruct (find y m2); auto.
 - factor_remove_min m2 R.
   assert (m1 < xd#1).
   { intros z Hz. apply B; trivial.
     rewrite (remove_min_in R). now left. }
   rewrite join_find; simpl; auto.
   + rewrite (remove_min_find R y).
     case K.compare_spec; intros; auto.
     destruct (find y m2'); trivial.
     simpl. symmetry. apply not_find_iff; eautom.
   + apply create_ok; eauto with *. now apply (remove_min_gt R).
Qed.

Lemma concat_bindings m1 m2 `{!Ok m1, !Ok m2} : m1 < m2 ->
 bindings (concat m1 m2) = bindings m1 ++ bindings m2.
Proof.
 functional induction (concat m1 m2); intros B; auto; try factornode m1.
 - symmetry. apply app_nil_r.
 - factor_remove_min m2 R.
   assert (m1 < xd#1).
   { intros z Hz. apply B; trivial.
     rewrite (remove_min_in R). now left. }
   rewrite join_bindings, create_bindings.
   + f_equal. rewrite (remove_min_bindings R). f_equal. now destruct xd.
   + apply create_ok; eauto with *. now apply (remove_min_gt R).
Qed.

(** Filter and partition *)

Lemma filter_in_inv f (m:t elt) x : x ∈ filter f m -> x ∈ m.
Proof.
 induction m as [|h l IHl y d r IHr]; simpl; auto.
 case (f y d); rewrite ?join_in, ?concat_in; intuition_in.
Qed.

Global Instance filter_ok f (m:t elt) `(!Ok m) : Ok (filter f m).
Proof.
 induction m as [|h l IHl x e r IHr]; simpl; autok.
 invok. case (f x e).
 - apply join_ok, create_ok; autok;
   intros y Hy; apply filter_in_inv in Hy; eauto.
 - apply concat_ok; autok. intros y Hy z Hz.
   apply filter_in_inv in Hy; apply filter_in_inv in Hz.
   transitivity x; eauto.
Qed.

Lemma filter_spec f m `(!Ok m) :
 bindings (filter f m) = List.filter (fun '(k,e) => f k e) (bindings m).
Proof.
 induction m; simpl; auto; invok.
 rewrite bindings_node, !filter_app. simpl. destruct f.
 - rewrite join_bindings, create_bindings. f_equal; auto. f_equal; auto.
   apply create_ok; autok;
    intros y Hy; apply filter_in_inv in Hy; eauto.
 - rewrite concat_bindings; autok. f_equal; auto.
   intros y Hy z Hz. apply filter_in_inv in Hy; apply filter_in_inv in Hz.
   transitivity t1; eauto.
Qed.

Lemma partition_fst f (m:t elt) : fst (partition f m) = filter f m.
Proof.
 induction m as [|h l IHl x e r IHr]; simpl; auto.
 rewrite <- IHl, <-IHr.
 now destruct (partition f l), (partition f r), f.
Qed.

Lemma partition_snd f (m:t elt) :
  snd (partition f m) = filter (fun k e => negb (f k e)) m.
Proof.
 induction m as [|h l IHl x e r IHr]; simpl; auto.
 rewrite <- IHl, <-IHr.
 now destruct (partition f l), (partition f r), f.
Qed.

Instance partition_ok1 f (m:t elt) : Ok m -> Ok (fst (partition f m)).
Proof.
 rewrite partition_fst; eauto with *.
Qed.

Instance partition_ok2 f (m:t elt) : Ok m -> Ok (snd (partition f m)).
Proof.
 rewrite partition_snd; eauto with *.
Qed.

Lemma partition_spec f m `(!Ok m) :
 prodmap (@bindings _) (partition f m) =
  List.partition (fun '(k,e) => f k e) (bindings m).
Proof.
 rewrite partition_filter.
 rewrite (surjective_pairing (partition f m)).
 rewrite partition_fst, partition_snd. unfold prodmap. f_equal.
 - apply filter_spec; auto.
 - rewrite filter_spec; auto.
   f_equiv. now intros (k,e) ? <-.
Qed.

End Elt.

Section Mapo.
Variable elt elt' : Type.
Variable f : key -> elt -> option elt'.

Lemma mapo_in m x :
 x ∈ (mapo f m) ->
 exists y d, y == x /\ MapsTo x d m /\ f y d <> None.
Proof.
functional induction (mapo f m); simpl; auto.
- intuition_in.
- rewrite join_in; intros [H|[H|H]].
  + exists x0, d. do 2 (split; autom). congruence.
  + destruct (IHt0 H) as (y & e & ? & ? & ?). exists y, e. autom.
  + destruct (IHt1 H) as (y & e & ? & ? & ?). exists y, e. autom.
- rewrite concat_in; intros [H|H].
  + destruct (IHt0 H) as (y & e & ? & ? & ?). exists y, e. autom.
  + destruct (IHt1 H) as (y & e & ? & ? & ?). exists y, e. autom.
Qed.

Lemma mapo_lt m x : m < x -> mapo f m < x.
Proof.
  intros H y Hy. destruct (mapo_in Hy) as (y' & e & ? & ? & ?). order.
Qed.

Lemma mapo_gt m x : x < m -> x < mapo f m.
Proof.
  intros H y Hy. destruct (mapo_in Hy) as (y' & e & ? & ? & ?). order.
Qed.
Local Hint Resolve mapo_lt mapo_gt : map.

Global Instance mapo_ok m `{!Ok m} : Ok (mapo f m).
Proof.
functional induction (mapo f m); simpl; autok; invok.
- apply join_ok, create_ok; autok.
- apply concat_ok; eauto using between with map.
Qed.

Ltac nonify e :=
 replace e with (@None elt) by
  (symmetry; rewrite not_find_iff; auto; intro; order).

Definition obind {A B} (o:option A) (f:A->option B) :=
  match o with Some a => f a | None => None end.

Lemma mapo_find m x `{!Ok m} :
  exists y, y == x /\
            find x (mapo f m) = obind (find x m) (f y).
Proof.
functional induction (mapo f m); simpl; auto; invok.
- now exists x.
- rewrite join_find; auto.
  + simpl. case K.compare_spec; simpl; intros.
    * now exists x0.
    * destruct IHt0 as (y' & ? & ?); auto.
      exists y'; split; trivial.
    * destruct IHt1 as (y' & ? & ?); auto.
      exists y'; split; trivial.
  + constructor; chok; auto using mapo_lt, mapo_gt with *.
- rewrite concat_find; autok.
  + destruct IHt1 as (y' & ? & ->); auto.
    destruct IHt0 as (y'' & ? & ->); auto.
    case K.compare_spec; simpl; intros.
    * nonify (find x r). nonify (find x l). simpl. now exists x0.
    * nonify (find x r). now exists y''.
    * nonify (find x l). exists y'. split; trivial.
      destruct (find x r); simpl; trivial.
      now destruct (f y' e).
  + apply between with x0; autom.
Qed.

End Mapo.

Section Gmerge.
Variable elt elt' elt'' : Type.
Variable f0 : key -> option elt -> option elt' -> option elt''.
Variable f : key -> elt -> option elt' -> option elt''.
Variable mapl : t elt -> t elt''.
Variable mapr : t elt' -> t elt''.
Hypothesis f0_f : forall x d o, f x d o = f0 x (Some d) o.
Hypothesis mapl_ok : forall m, Ok m -> Ok (mapl m).
Hypothesis mapr_ok : forall m', Ok m' -> Ok (mapr m').
Hypothesis mapl_f0 : forall x m, Ok m ->
 exists y, y == x /\
           find x (mapl m) = obind (find x m) (fun d => f0 y (Some d) None).
Hypothesis mapr_f0 : forall x m, Ok m ->
 exists y, y == x /\
           find x (mapr m) = obind (find x m) (fun d => f0 y None (Some d)).

Notation gmerge := (gmerge f mapl mapr).

Lemma gmerge_in m m' y `{!Ok m, !Ok m'} :
  y ∈ (gmerge m m') -> y ∈ m \/ y ∈ m'.
Proof.
  functional induction (gmerge m m'); intros H;
  try factornode m2; invok.
  - right. apply find_in.
    generalize (in_find H).
    destruct (@mapr_f0 y m2) as (y' & ? & ->); trivial.
    intros A B. rewrite B in A. now elim A.
  - left. apply find_in.
    generalize (in_find H).
    destruct (@mapl_f0 y m2) as (y' & ? & ->); trivial.
    intros A B. rewrite B in A. now elim A.
  - rewrite join_in in *. revert IHt2 IHt0 H. cleansplit.
    generalize (@split_ok_l _ m2 x1 _) (@split_ok_r _ m2 x1 _).
    rewrite split_in_r, split_in_l; intuition_in.
  - rewrite concat_in in *. revert IHt2 IHt0 H; cleansplit.
    generalize (@split_ok_l _ m2 x1 _) (@split_ok_r _ m2 x1 _).
    rewrite split_in_r, split_in_l; intuition_in.
Qed.

Lemma gmerge_lt m m' x `{!Ok m, !Ok m'} :
  m < x -> m' < x -> gmerge m m' < x.
Proof.
  intros ? ? y Hy. apply gmerge_in in Hy; intuition_in; order.
Qed.

Lemma gmerge_gt m m' x `{!Ok m, !Ok m'} :
  x < m -> x < m' -> x < gmerge m m'.
Proof.
  intros ? ? y Hy. apply gmerge_in in Hy; intuition_in; order.
Qed.
Local Hint Resolve gmerge_lt gmerge_gt : map.
Local Hint Resolve split_ok_l split_ok_r split_lt_l split_gt_r : map.

Global Instance gmerge_ok m m' `{!Ok m, !Ok m'} : Ok (gmerge m m').
Proof.
  functional induction (gmerge m m'); auto; factornode m2; invok;
  (apply join_ok, create_ok || apply concat_ok);
  revert IHt2 IHt0; cleansplit; intuition.
  apply between with x1; autom.
Qed.

Lemma oelse_none_r {A} (o:option A) : oelse o None = o.
Proof. now destruct o. Qed.

Ltac nonify e :=
 let E := fresh "E" in
 let U := fresh "U" in
 assert (E : e = None);
   [ rewrite not_find_iff; autok; intro U;
     try apply gmerge_in in U; intuition_in; order
   | rewrite E; clear E ].

Lemma gmerge_find m m' x `{!Ok m, !Ok m'} :
 x ∈ m \/ x ∈ m' ->
 exists y, y == x /\
           find x (gmerge m m') = f0 y (find x m) (find x m').
Proof.
  functional induction (gmerge m m');
  try factornode m2; invok; rewrite ?in_node, ?in_leaf.
  - intros [[ ]|H].
    destruct (@mapr_f0 x m2) as (y,(Hy,E)); trivial.
    exists y; split; trivial.
    rewrite E. simpl. apply in_find in H; trivial.
    destruct (find x m2); simpl; intuition.
  - intros [H|[ ]].
    destruct (@mapl_f0 x m2) as (y,(Hy,E)); trivial.
    exists y; split; trivial.
    rewrite E. simpl. apply in_find in H; trivial.
    destruct (find x m2); simpl; intuition.
  - generalize (@split_ok_l _ m2 x1 _) (@split_ok_r _ m2 x1 _).
    rewrite (@split_find _ m2 x1 x); autok.
    rewrite e1 in *; simpl in *. intros.
    rewrite join_find by (cleansplit; constructor; autok).
    simpl. case K.compare_spec; intros.
    + exists x1. split; autom. now rewrite <- e3, f0_f.
    + apply IHt2; autom. clear IHt2 IHt0.
      cleansplit; rewrite split_in_l; trivial.
      intuition_in; order.
    + apply IHt0; auto. clear IHt2 IHt0.
      cleansplit; rewrite split_in_r; trivial.
      intuition_in; order.
  - generalize (@split_ok_l _ m2 x1 _) (@split_ok_r _ m2 x1 _).
    rewrite (@split_find _ m2 x1 x); autok.
    pose proof (@split_lt_l _ m2 x1 _).
    pose proof (@split_gt_r _ m2 x1 _).
    rewrite e1 in *; simpl in *. intros.
    rewrite concat_find by (try apply between with x1; autok).
    case K.compare_spec; intros.
    + clear IHt0 IHt2.
      exists x1. split; autom. rewrite <- f0_f, e2.
      nonify (find x (gmerge r1 r2')).
      nonify (find x (gmerge l1 l2')). trivial.
    + nonify (find x (gmerge r1 r2')).
      simpl. apply IHt2; auto. clear IHt2 IHt0.
      intuition_in; try order.
      right. cleansplit. now apply split_in_l.
    + nonify (find x (gmerge l1 l2')). simpl.
      rewrite oelse_none_r.
      apply IHt0; auto. clear IHt2 IHt0.
      intuition_in; try order.
      right. cleansplit. now apply split_in_r.
Qed.

End Gmerge.

Section Merge.
Variable elt elt' elt'' : Type.
Variable f : key -> option elt -> option elt' -> option elt''.

Global Instance merge_ok m m' `{!Ok m, !Ok m'} : Ok (merge f m m').
Proof.
unfold merge; intros.
apply gmerge_ok with f;
 auto using mapo_ok, mapo_find.
Qed.

Lemma merge_spec1 m m' x `{!Ok m, !Ok m'} :
 x ∈ m \/ x ∈ m' ->
 exists y, y == x /\
           find x (merge f m m') = f y (find x m) (find x m').
Proof.
  unfold merge; intros.
  edestruct (gmerge_find (f0:=f)) as (y,(Hy,E));
    eauto using mapo_ok.
  - reflexivity.
  - intros. now apply mapo_find.
  - intros. now apply mapo_find.
Qed.

Lemma merge_spec2 m m' x `{!Ok m, !Ok m'} :
  x ∈ (merge f m m') -> x ∈ m \/ x ∈ m'.
Proof.
unfold merge; intros.
eapply gmerge_in with (f0:=f); try eassumption;
 auto using mapo_ok, mapo_find.
Qed.

End Merge.
End MakeRaw.

(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we need
   to encapsulate everything into a type of binary search trees. *)

Module IntMake (I:Int)(K: OrderedType) <: Interface.S K.
 Module Raw := MakeRaw I K.
 Include Raw.Pack K Raw.
End IntMake.

(* For concrete use inside Coq, we propose an instantiation of [Int] by [Z]. *)

Module Make (K:OrderedType) <: S K := IntMake(Z_as_Int)(K).
