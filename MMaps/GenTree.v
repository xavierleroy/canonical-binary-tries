(** * MSets.GenTree : maps via generic trees

    This module factorizes common parts in implementations
    of finite maps as AVL trees and as Red-Black trees. The nodes
    of the trees defined here include an generic information
    parameter, that will be the height in AVL trees and the color
    in Red-Black trees. Without more details here about these
    information parameters, trees here are not known to be
    well-balanced, but simply binary-search-trees.

    The operations we could define and prove correct here are the
    ones that do not modify the informations on the nodes :

     - empty is_empty
     - find mem
     - equal compare
     - fold cardinal bindings
     - map mapi
*)

From Coq Require Import Bool PeanoNat BinInt FunInd.
From Coq Require Import Orders OrdersFacts OrdersLists.
From Tries.MMaps Require Import Comparisons Interface OrdList.

Local Open Scope list_scope.
Local Open Scope lazy_bool_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(* For nicer extraction, we create induction principles
   only when needed *)
Local Unset Elimination Schemes.

Module PairNotations.
Notation "s #1" := (fst s) (at level 9, format "s '#1'").
Notation "s #2" := (snd s) (at level 9, format "s '#2'").
End PairNotations.

Module Type InfoTyp.
 Parameter t : Set.
End InfoTyp.

(** * Ops : the pure functions *)

Module Type Ops (K:OrderedType)(Info:InfoTyp).

Definition key := K.t.

Section Elt.

Variable elt : Type.

(** * Trees *)

Inductive tree  : Type :=
| Leaf : tree
| Node : Info.t -> tree -> K.t -> elt -> tree -> tree.

Definition t := tree.

(** ** The empty map and emptyness test *)

Definition empty := Leaf.

Definition is_empty t :=
 match t with
 | Leaf => true
 | _ => false
 end.

(** ** Membership test *)

(** The [mem] function is deciding membership. It exploits the
    binary search tree invariant to achieve logarithmic complexity. *)

Fixpoint mem x t :=
 match t with
 | Leaf => false
 | Node _ l k _ r =>
   match K.compare x k with
     | Lt => mem x l
     | Eq => true
     | Gt => mem x r
   end
 end.

Fixpoint find x m : option elt :=
  match m with
    |  Leaf => None
    |  Node _ l y v r =>
       match K.compare x y with
         | Eq => Some v
         | Lt => find x l
         | Gt => find x r
       end
   end.

(** ** Minimal, maximal, arbitrary bindings *)

Fixpoint min_binding (t : tree) : option (key * elt) :=
 match t with
 | Leaf => None
 | Node _ Leaf x e r => Some (x,e)
 | Node _ l x e r => min_binding l
 end.

Fixpoint max_binding (t : tree) : option (key * elt) :=
  match t with
  | Leaf => None
  | Node _ l x e Leaf => Some (x,e)
  | Node _ l x e r => max_binding r
  end.

Definition choose := min_binding.

(** ** Iteration on elements *)

Fixpoint fold {A: Type} (f: key -> elt -> A -> A) (t: tree) (base: A) : A :=
  match t with
  | Leaf => base
  | Node _ l x e r => fold f r (f x e (fold f l base))
 end.

Fixpoint bindings_aux acc s :=
  match s with
   | Leaf => acc
   | Node _ l x e r => bindings_aux ((x,e) :: bindings_aux acc r) l
  end.

Definition bindings := bindings_aux nil.

Fixpoint rev_bindings_aux acc s :=
  match s with
   | Leaf => acc
   | Node _ l x e r => rev_bindings_aux ((x,e) :: rev_bindings_aux acc l) r
  end.

Definition rev_bindings := rev_bindings_aux nil.

Fixpoint cardinal (s : tree) : nat :=
  match s with
   | Leaf => 0
   | Node _ l _ _ r => S (cardinal l + cardinal r)
  end.

Fixpoint maxdepth s :=
 match s with
 | Leaf => 0
 | Node _ l _ _ r => S (max (maxdepth l) (maxdepth r))
 end.

Fixpoint mindepth s :=
 match s with
 | Leaf => 0
 | Node _ l _ _ r => S (min (mindepth l) (mindepth r))
 end.

(** ** Testing universal or existential properties. *)

(** We do not use the standard boolean operators of Coq,
    but lazy ones. *)

Fixpoint for_all (f:key->elt->bool) s := match s with
  | Leaf => true
  | Node _ l x e r => f x e &&& for_all f l &&& for_all f r
end.

Fixpoint exists_ (f:key->elt->bool) s := match s with
  | Leaf => false
  | Node _ l x e r => f x e ||| exists_ f l ||| exists_ f r
end.

(** ** Comparison of trees *)

(** The algorithm here has been suggested by Xavier Leroy,
    and transformed into c.p.s. by Benjamin Grégoire.
    The original ocaml code (with non-structural recursive calls)
    has also been formalized (thanks to Function+measure), see
    [ocaml_compare] in [MSetFullAVL]. The following code with
    continuations computes dramatically faster in Coq, and
    should be almost as efficient after extraction.
*)

(** * Comparison *)

(** Enumeration of the elements of a tree. This corresponds
    to the "samefringe" notion in the litterature. *)

Inductive enumeration :=
 | End : enumeration
 | More : key -> elt -> tree -> enumeration -> enumeration.

(** [cons t e] adds the elements of tree [t] on the head of
    enumeration [e]. *)

Fixpoint cons s e : enumeration :=
 match s with
  | Leaf => e
  | Node _ l x v r => cons l (More x v r e)
 end.

(** One step of comparison of elements *)

Variable eqb : elt->elt->bool.

Definition equal_more x1 v1 (cont:enumeration->bool) e2 :=
 match e2 with
 | End => false
 | More x2 v2 r2 e2 =>
     match K.compare x1 x2 with
      | Eq => eqb v1 v2 &&& cont (cons r2 e2)
      | _ => false
     end
 end.

(** Comparison of left tree, middle element, then right tree *)

Fixpoint equal_cont m1 (cont:enumeration->bool) e2 :=
 match m1 with
  | Leaf => cont e2
  | Node _ l1 x1 v1 r1 =>
     equal_cont l1 (equal_more x1 v1 (equal_cont r1 cont)) e2
  end.

(** Initial continuation *)

Definition equal_end e2 := match e2 with End => true | _ => false end.

(** The complete boolean comparison *)

Definition equal m1 m2 := equal_cont m1 equal_end (cons m2 End).

(** Ternary comparison *)

Variable cmp : elt -> elt -> comparison.

(** One step of comparison of bindings *)

Definition compare_more x1 d1 (cont:enumeration -> comparison) e2 :=
  match e2 with
  | End => Gt
  | More x2 d2 r2 e2 =>
    lex (K.compare x1 x2) (lex (cmp d1 d2) (cont (cons r2 e2)))
  end.

(** Comparison of left tree, middle element, then right tree *)

Fixpoint compare_cont s1 (cont:enumeration -> comparison) e2 :=
  match s1 with
  | Leaf => cont e2
  | Node _ l1 x1 d1 r1 =>
    compare_cont l1 (compare_more x1 d1 (compare_cont r1 cont)) e2
  end.

(** Initial continuation *)

Definition compare_end (e2:enumeration) :=
  match e2 with End => Eq | _ => Lt end.

(** The complete comparison *)

Definition compare m1 m2 :=
  compare_cont m1 compare_end (cons m2 End).

End Elt.

(** ** Map *)

Fixpoint map {elt elt'}(f : elt -> elt')(m : t elt) : t elt' :=
  match m with
   | Leaf _  => Leaf _
   | Node h l x d r => Node h (map f l) x (f d) (map f r)
  end.

(* ** Mapi *)

Fixpoint mapi (elt elt' : Type)(f : key -> elt -> elt')(m : t elt) : t elt' :=
  match m with
   | Leaf _ => Leaf _
   | Node h l x d r => Node h (mapi f l) x (f x d) (mapi f r)
  end.

End Ops.

(** * Props : correctness proofs of these generic operations *)

Module Type Props (K:OrderedType)(Info:InfoTyp)(Import M:Ops K Info).

Implicit Types x y k : K.t.

Local Infix "==" := K.eq (at level 70).

(** Overloaded "<" notation *)

Class LessThan (A B : Type) := lessthan : A -> B -> Prop.
Local Infix "<" := lessthan.

Global Instance lt_key_key : LessThan K.t K.t := K.lt.

(** ** Occurrence in a tree *)

Module Ind. (* Module allowing a "Definition" of MapsTo below. *)

Inductive MapsTo elt (x : key)(e : elt) : t elt -> Prop :=
| MapsRoot l r h y : x == y -> MapsTo x e (Node h l y e r)
| MapsLeft l r h y e' : MapsTo x e l -> MapsTo x e (Node h l y e' r)
| MapsRight l r h y e' : MapsTo x e r -> MapsTo x e (Node h l y e' r).

End Ind.
Definition MapsTo := Ind.MapsTo.
Import Ind. (* In the proofs below, let's work with Ind.MapsTo. *)

Local Notation "m @ x ↦ e" := (MapsTo x e m)
 (at level 9, format "m '@' x  '↦'  e").

Definition In elt k m := exists e:elt, m@k ↦ e.
Local Infix "∈" := In (at level 70).

Definition Eqdom elt (m m' : t elt) := forall k, k ∈ m <-> k ∈ m'.
Definition Equal elt (m m' : t elt) := forall k, find k m = find k m'.
Definition Equiv elt (R:elt->elt->Prop) m m' :=
 Eqdom m m' /\ (forall k e e', m@k ↦ e -> m'@k ↦ e' -> R e e').
Definition Equivb elt cmp := @Equiv elt (Cmp cmp).

Definition AllKeys elt (P:key->Prop) (m : t elt) :=
 forall x, x ∈ m -> P x.

(** ** Binary search trees *)

(** Strict order between keys and trees:
    [x < m] when [x] is strictly smaller than any key in [m].
    [m < x] when [x] is strictly greater than any key in [m].
    [m < m'] when all keys in [m] are lower than all keys in [m']. *)

Global Instance lt_key_map elt : LessThan K.t (t elt) :=
 fun x => AllKeys (lessthan x).
Global Instance lt_map_key elt : LessThan (t elt) K.t :=
 fun m x => AllKeys (fun y => y < x) m.
Global Instance lt_map_map elt : LessThan (t elt) (t elt) :=
 fun m m' => AllKeys (fun x => x < m') m.

(** [Bst t] : [t] is a binary search tree *)

Inductive Bst elt : t elt -> Prop :=
| BSLeaf : Bst (Leaf _)
| BSNode h x e l r : Bst l -> Bst r -> l < x -> x < r ->
  Bst (Node h l x e r).

(** [Bst] is the (decidable) invariant our trees will have to satisfy. *)

Definition IsOk := Bst.
Class Ok elt (m:t elt) : Prop := ok : Bst m.

Module F := OrderedTypeFacts K.
Module O := KeyOrderedType K.
Module L := Tries.MMaps.OrdList.MakeRaw K.

Scheme tree_ind := Induction for tree Sort Prop.

(** * Automation and dedicated tactics. *)

Local Hint Constructors tree MapsTo Bst : map.
Local Hint Unfold Ok In : map.
Local Hint Immediate F.eq_sym : map.
Local Hint Resolve F.eq_refl : map.

Tactic Notation "factornode" ident(s) :=
 try clear s;
 match goal with
   | |- context [Node ?h ?l ?x ?e ?r] =>
       set (s:=Node h l x e r) in *; clearbody s; clear l x e r; try clear h
   | _ : context [Node ?h ?l ?x ?e ?r] |- _ =>
       set (s:=Node h l x e r) in *; clearbody s; clear l x e r; try clear h
 end.

(** A tactic for cleaning hypothesis after use of functional induction. *)

Ltac cleanf :=
 match goal with
  | H : K.compare _ _ = Eq |- _ =>
    rewrite ?H; apply F.compare_eq in H; cleanf
  | H : K.compare _ _ = Lt |- _ =>
    rewrite ?H; apply F.compare_lt_iff in H; cleanf
  | H : K.compare _ _ = Gt |- _ =>
    rewrite ?H; apply F.compare_gt_iff in H; cleanf
  | _ => idtac
 end.


(** A tactic to repeat [inversion_clear] on all hyps of the
    form [(f (Node ...))] *)

Ltac inv f :=
  match goal with
     | H:f (Leaf _) |- _ => inversion_clear H; inv f
     | H:f _ (Leaf _) |- _ => inversion_clear H; inv f
     | H:f _ _ (Leaf _) |- _ => inversion_clear H; inv f
     | H:f _ _ _ (Leaf _) |- _ => inversion_clear H; inv f
     | H:f (Node _ _ _ _ _) |- _ => inversion_clear H; inv f
     | H:f _ (Node _ _ _ _ _) |- _ => inversion_clear H; inv f
     | H:f _ _ (Node _ _ _ _ _) |- _ => inversion_clear H; inv f
     | H:f _ _ _ (Node _ _ _ _ _) |- _ => inversion_clear H; inv f
     | _ => idtac
  end.

Ltac inv_all :=
  match goal with
     | H:_ (Leaf _) |- _ => inversion_clear H; inv_all
     | H:_ _ (Leaf _) |- _ => inversion_clear H; inv_all
     | H:_ _ _ (Leaf _) |- _ => inversion_clear H; inv_all
     | H:_ _ _ _ (Leaf _) |- _ => inversion_clear H; inv_all
     | H:_ (Node _ _ _ _ _) |- _ => inversion_clear H; inv_all
     | H:_ _ (Node _ _ _ _ _) |- _ => inversion_clear H; inv_all
     | H:_ _ _ (Node _ _ _ _ _) |- _ => inversion_clear H; inv_all
     | H:_ _ _ _ (Node _ _ _ _ _) |- _ => inversion_clear H; inv_all
     | _ => idtac
  end.

Ltac chok := change Bst with Ok in *.
Ltac autok := chok; auto with typeclass_instances map.
Ltac invok := inv_all; chok.
Ltac autom := auto with map.
Ltac eautom := eauto with map.

Ltac intuition_m := repeat (intuition; inv MapsTo).

Ltac redk :=
  match goal with
  | |- context [ O.eqke ?p ?q ] =>
    change (O.eqke p q) with (fst p == fst q /\ snd p = snd q); simpl
  | H : context [ O.eqke ?p ?q] |- _ =>
    change (O.eqke p q) with (fst p == fst q /\ snd p = snd q) in H;
    simpl in H
  end.

Arguments Ok {elt} m.
Arguments Equal {elt} m m'.
Arguments Eqdom {elt} m m'.

Global Instance Equal_equiv {elt} : Equivalence (@Equal elt).
Proof. split; congruence. Qed.
Global Instance Eqdom_equiv {elt} : Equivalence (@Eqdom elt).
Proof.
 split; try firstorder. intros x y z E E' k. now rewrite (E k), (E' k).
Qed.

(** Facts about [MapsTo] and [In]. *)

Lemma mapsto_in {elt} k (e:elt) m : m@k ↦ e -> k ∈ m.
Proof.
 eauto with map.
Qed.
Local Hint Resolve mapsto_in : map.

Lemma in_mapsto {elt} k m : k ∈ m -> exists e:elt, m@k ↦ e.
Proof.
 auto with map.
Qed.

Lemma mapsto_eq {elt} m x y (e:elt) :
  x == y -> m@x ↦ e -> m@y ↦ e.
Proof.
 induction m; simpl; intuition_m; eauto. constructor. F.order.
Qed.
Local Hint Immediate mapsto_eq : map.

Global Instance MapsTo_compat {elt} :
  Proper (K.eq==>Logic.eq==>Logic.eq==>iff) (@MapsTo elt).
Proof.
 split; subst; now apply mapsto_eq.
Qed.

Lemma leaf_mapsto {elt} y e : (Leaf elt)@y ↦ e <-> False.
Proof.
 now split.
Qed.

Lemma node_mapsto {elt} l x (e:elt) r h y v :
 (Node h l x e r)@y ↦ v <->
   l@y ↦ v \/ (y == x /\ v = e) \/ r@y ↦ v.
Proof.
 intuition_m; subst; auto with map.
Qed.

Global Instance in_compat {elt} :
  Proper (K.eq==>Logic.eq==>iff) (@In elt).
Proof.
 intros x x' E m m' <-.
 split; intros (e,M); exists e. now rewrite <-E. now rewrite E.
Qed.

Lemma in_leaf {elt} y : y ∈ (@Leaf elt) <-> False.
Proof.
 unfold In. setoid_rewrite leaf_mapsto. firstorder.
Qed.

Lemma in_node {elt} l x (e:elt) r h y :
  y ∈ (Node h l x e r) <-> y ∈ l \/ y == x \/ y ∈ r.
Proof.
 unfold In. setoid_rewrite node_mapsto. firstorder.
 exists e. intuition.
Qed.

Ltac intuition_in := rewrite ?in_node, ?in_leaf; intuition.

Lemma in_left {elt} l x (e:elt) r h y : y ∈ l -> y ∈ (Node h l x e r).
Proof.
 intuition_in.
Qed.

Lemma in_right {elt} l x (e:elt) r h y : y ∈ r -> y ∈ (Node h l x e r).
Proof.
 intuition_in.
Qed.
Local Hint Resolve in_left in_right : map.

(** Results about [AllKeys] *)

Lemma allkeys_leaf {elt} P : AllKeys P (@Leaf elt).
Proof.
 intros y (e,M). inversion M.
Qed.

Lemma allkeys_node {elt} P h l x (e:elt) r :
  Proper (K.eq ==> iff) P ->
  AllKeys P (Node h l x e r) <-> AllKeys P l /\ P x /\ AllKeys P r.
Proof.
 unfold AllKeys. setoid_rewrite in_node. firstorder. apply H0; autom.
Qed.

Global Instance allkeys_m {elt} :
 Proper ((K.eq ==> iff) ==> Eqdom ==> iff) (@AllKeys elt).
Proof.
 intros P P' HP m m' Hm. unfold AllKeys.
 split; intros H x IN.
 - rewrite <- (HP x); autom. apply H, Hm; autom.
 - rewrite (HP x); autom. apply H, Hm; autom.
Qed.

(** Results about [<] *)

Lemma above_leaf {elt} x : @Leaf elt < x.
Proof.
 apply allkeys_leaf.
Qed.

Lemma above_node {elt} x h l y (e:elt) r :
 Node h l y e r < x <-> l < x /\ y < x /\ r < x.
Proof.
 apply allkeys_node with (P := fun z => z < x). now intros ? ? ->.
Qed.

Global Instance above_m {elt} :
  Proper (@Eqdom elt ==> K.eq ==> iff) lessthan.
Proof.
 intros until 2. apply allkeys_m; auto. split; F.order.
Qed.

Lemma below_leaf {elt} x : x < @Leaf elt.
Proof.
 apply allkeys_leaf.
Qed.

Lemma below_node {elt} x h l y (e:elt) r :
 x < Node h l y e r <-> x < l /\ x < y /\ x < r.
Proof.
 apply allkeys_node. now intros ? ? ->.
Qed.

Global Instance below_m {elt} :
  Proper (K.eq ==> @Eqdom elt ==> iff) lessthan.
Proof.
 intros until 2. apply allkeys_m; auto. split; F.order.
Qed.

Global Instance apart_m {elt} :
 Proper (@Eqdom elt ==> @Eqdom elt ==> iff) lessthan.
Proof.
 intros until 2. apply allkeys_m; auto.
 intros until 1. now apply below_m.
Qed.

(** Helper tactic concerning order of keys. *)

Ltac invlt :=
  match goal with
  | H : _ < Node _ _ _ _ _ |- _ => rewrite !below_node in H; invlt
  | H : Node _ _ _ _ _ < _ |- _ => rewrite !above_node in H; invlt
  | _ => idtac
  end.

Ltac ok :=
 invok;
 match goal with
   | |- Ok (Node _ _ _ _ _) => constructor; autok; ok
   | |- _ < Node _ _ _ _ _ => rewrite !below_node; repeat split; ok
   | |- Node _ _ _ _ _ < _ => rewrite !above_node; repeat split; ok
   | _ => eauto with typeclass_instances map
 end.

Ltac order := intros; match goal with
 | IN: _ ∈ ?m, LT: ?m < _ |- _ => specialize (LT _ IN); order
 | IN: _ ∈ ?m, LT: _ < ?m |- _ => specialize (LT _ IN); order
 | M: ?m @ _ ↦ _, LT: ?m < _ |- _ => specialize (LT _ (mapsto_in M)); order
 | M: ?m @ _ ↦ _, LT: _ < ?m |- _ => specialize (LT _ (mapsto_in M)); order
 | _ => simpl in *; F.order
end.

Lemma above_notin {elt} (m:t elt) x : m < x -> ~ x ∈ m.
Proof.
 intros until 2; order.
Qed.

Lemma below_notin {elt} (m:t elt) x : x < m -> ~ x ∈ m.
Proof.
 intros until 2; order.
Qed.

Lemma above_trans {elt} (m:t elt) x y : x < y -> m < x -> m < y.
Proof.
 intros until 3; order.
Qed.

Lemma below_trans {elt} (m:t elt) x y : y < x -> x < m -> y < m.
Proof.
 intros until 3; order.
Qed.

Local Hint Resolve above_notin above_trans below_notin below_trans : map.

Lemma between {elt} (m m':t elt) x :
  m < x -> x < m' -> m < m'.
Proof.
 intros until 4; order.
Qed.

Lemma apart_node_l {elt} h l x v r (m:t elt) :
  (Node h l x v r) < m <-> l < m /\ x < m /\ r < m.
Proof.
 apply allkeys_node. now intros ? ? ->.
Qed.

Lemma apart_node_r {elt} h l x v r (m:t elt) :
  m < (Node h l x v r) <-> m < l /\ m < x /\ m < r.
Proof.
 unfold "<"; unfold lt_map_map, lt_map_key, AllKeys.
 setoid_rewrite below_node. split; [ | intuition].
 intros H; repeat split; intros y IN; now specialize (H y IN).
Qed.


(** Bst is decidable *)

Global Instance Bst_Ok {elt} (m : t elt) (B : Bst m) : Ok m := B.

Fixpoint above {elt} x (m : t elt) :=
 match m with
  | Leaf _ => true
  | Node _ l y _ r =>
     match K.compare x y with
      | Gt => above x l && above x r
      | _ => false
     end
 end.

Fixpoint below {elt} x (m : t elt) :=
 match m with
  | Leaf _ => true
  | Node _ l y _ r =>
     match K.compare x y with
      | Lt => below x l && below x r
      | _ => false
     end
 end.

Fixpoint isok {elt} (m : t elt) :=
 match m with
  | Leaf _ => true
  | Node _  l x _ r => isok l && isok r && above x l && below x r
 end.

Lemma above_iff {elt} x (m:t elt) :
  m < x <-> above x m = true.
Proof.
 induction m as [|c l IHl y v r IHr]; simpl.
 - intuition. apply above_leaf.
 - rewrite above_node.
   case K.compare_spec.
   + split; intros; try easy. intuition. order.
   + split; intros; try easy. intuition. order.
   + rewrite andb_true_iff; intuition.
Qed.

Lemma below_iff {elt} x (m:t elt) :
  x < m <-> below x m = true.
Proof.
 induction m as [|c l IHl y v r IHr]; simpl.
 - intuition. apply below_leaf.
 - rewrite below_node.
   case K.compare_spec.
   + split; intros; try easy. intuition. order.
   + rewrite !andb_true_iff. intuition.
   + split; intros; try easy. intuition. order.
Qed.

Lemma isok_iff {elt} (m:t elt) : Ok m <-> isok m = true.
Proof.
 induction m as [|c l IHl y v r IHr]; simpl.
 - intuition.
 - rewrite !andb_true_iff, <- IHl, <-IHr, <- below_iff, <- above_iff.
   intuition; invok; auto.
Qed.

Lemma isok_spec {elt} (m:t elt) : reflect (Ok m) (isok m).
Proof.
 apply iff_reflect, isok_iff.
Qed.

Lemma isok_Ok {elt} (m:t elt) : isok m = true -> Ok m.
Proof. apply isok_iff. Qed.

Section Elt.
Variable elt:Type.
Implicit Types m r : t elt.

(** * Membership *)

Lemma find_1 m x e `{!Ok m} : m@x ↦ e -> find x m = Some e.
Proof.
 induction m; simpl; invok.
 - intuition_m.
 - rewrite node_mapsto.
   case K.compare_spec; intuition_m; subst; auto; order.
Qed.

Lemma find_2 m x e : find x m = Some e -> m@x ↦ e.
Proof.
 induction m; simpl; try easy.
 case K.compare_spec; [ intros -> [= ->] | .. ]; intuition_m.
Qed.

Lemma find_spec m x e `{!Ok m} : find x m = Some e <-> m@x ↦ e.
Proof.
 split; auto using find_1, find_2.
Qed.

Lemma find_in m x : find x m <> None -> x ∈ m.
Proof.
 destruct (find x m) eqn:F; intros H.
 - exists e. now apply find_2.
 - now elim H.
Qed.

Lemma in_find m x `{!Ok m} : x ∈ m -> find x m <> None.
Proof.
 intros (e,M). now rewrite (find_1 M).
Qed.

Lemma find_in_iff m x `{!Ok m} :
 find x m <> None <-> x ∈ m.
Proof.
 split; auto using find_in, in_find.
Qed.

Lemma not_find_iff m x `{!Ok m} :
 find x m = None <-> ~ x ∈ m.
Proof.
 rewrite <- find_in_iff; trivial.
 destruct (find x m); split; try easy. now destruct 1.
Qed.

Lemma eq_option_alt (o o':option elt) :
 o=o' <-> (forall e, o=Some e <-> o'=Some e).
Proof.
split; intros.
- now subst.
- destruct o, o'; rewrite ?H; auto. symmetry; now apply H.
Qed.

Lemma find_mapsto_equiv m m' x `{!Ok m, !Ok m'} :
 find x m = find x m' <->
  (forall d, m@x ↦ d <-> m'@x ↦ d).
Proof.
 rewrite eq_option_alt.
 split; intros H d. now rewrite <- 2 find_spec. now rewrite 2 find_spec.
Qed.

Lemma find_in_equiv m m' x `{!Ok m, !Ok m'} :
 find x m = find x m' ->
  (x ∈ m <-> x ∈ m').
Proof.
 intros E. split; intros; apply find_in; [ rewrite <- E | rewrite E ];
  apply in_find; auto.
Qed.

Lemma find_compat m x x' `{!Ok m} : x == x' -> find x m = find x' m.
Proof.
 intros E.
 destruct (find x' m) eqn:H.
 - apply find_1; trivial. rewrite E. now apply find_2.
 - rewrite not_find_iff in *; trivial. now rewrite E.
Qed.

Lemma mem_spec m x `{!Ok m} : mem x m = true <-> x ∈ m.
Proof.
 induction m; simpl.
 - now rewrite in_leaf.
 - invok. rewrite in_node. case K.compare_spec; intuition; order.
Qed.

(** * Empty map *)

Global Instance empty_ok : Ok (empty elt).
Proof.
 constructor.
Qed.

Lemma empty_spec x : find x (empty elt) = None.
Proof.
 reflexivity.
Qed.

(** * Emptyness test *)

Lemma is_empty_spec m : is_empty m = true <-> forall x, find x m = None.
Proof.
 destruct m as [|h r x e l]; simpl; split; try easy.
 intros H. specialize (H x). now rewrite F.compare_refl in H.
Qed.

(** * Elements *)

Definition eq_key : (key*elt) -> (key*elt) -> Prop := @O.eqk elt.
Definition eq_key_elt : (key*elt) -> (key*elt) -> Prop := @O.eqke elt.
Definition lt_key : (key*elt) -> (key*elt) -> Prop := @O.ltk elt.

Notation eqk := (O.eqk (elt:= elt)).
Notation eqke := (O.eqke (elt:= elt)).
Notation ltk := (O.ltk (elt:= elt)).


Lemma bindings_aux_mapsto m acc x e :
 InA eqke (x,e) (bindings_aux acc m) <-> m@x ↦ e \/ InA eqke (x,e) acc.
Proof.
 revert acc.
 induction m as [ | h l Hl y e' r Hr ]; intros acc; simpl; auto.
 - intuition_m.
 - rewrite Hl, InA_cons, Hr. redk. intuition_m. subst; autom.
Qed.

Lemma bindings_spec1 m x e :
 InA eqke (x,e) (bindings m) <-> m@x ↦ e.
Proof.
 unfold bindings. rewrite bindings_aux_mapsto. rewrite InA_nil. intuition.
Qed.

Lemma bindings_in m x : L.PX.In x (bindings m) <-> x ∈ m.
Proof.
 unfold L.PX.In.
 split; intros (y,H); exists y.
 - now rewrite <- bindings_spec1.
 - unfold L.PX.MapsTo; now rewrite bindings_spec1.
Qed.

Lemma bindings_aux_sort m acc `{!Ok m} :
 sort ltk acc ->
 (forall x e y, InA eqke (x,e) acc -> y ∈ m -> y < x) ->
 sort ltk (bindings_aux acc m).
Proof.
 revert acc.
 induction m as [ | h l Hl y e r Hr ]; intros acc; simpl; intuition.
 invok.
 apply Hl; auto.
 - constructor.
   + apply Hr; eautom.
   + clear Hl Hr.
     apply InA_InfA with (eqA:=eqke); auto with *.
     intros (y',e') Hy'.
     apply bindings_aux_mapsto in Hy'. change (y < y'). intuition; eautom.
 - clear Hl Hr. intros x e' y' Hx Hy'.
   rewrite InA_cons in Hx. redk. destruct Hx as [(Hx,->)|Hx].
   + order.
   + apply bindings_aux_mapsto in Hx. intuition. order. eautom.
Qed.

Lemma bindings_spec2 m `{!Ok m} : sort ltk (bindings m).
Proof.
 unfold bindings; apply bindings_aux_sort; auto. inversion 1.
Qed.
Local Hint Resolve bindings_spec2 : map.

Lemma bindings_spec2w m `{!Ok m} : NoDupA eqk (bindings m).
Proof.
 intros; apply O.Sort_NoDupA; autom.
Qed.

Lemma bindings_aux_cardinal m acc :
 length acc + cardinal m = length (bindings_aux acc m).
Proof.
 revert acc. induction m; simpl; intuition.
 rewrite <- IHm1; simpl.
 rewrite <- IHm2. rewrite Nat.add_succ_r, <- Nat.add_assoc.
 f_equal. f_equal. apply Nat.add_comm.
Qed.

Lemma cardinal_spec m : cardinal m = length (bindings m).
Proof.
 exact (bindings_aux_cardinal m nil).
Qed.

Lemma bindings_app :
 forall (s:t elt) acc, bindings_aux acc s = bindings s ++ acc.
Proof.
 induction s; simpl; intros; auto.
 rewrite IHs1, IHs2.
 unfold bindings; simpl.
 rewrite 2 IHs1, IHs2, !app_nil_r, !app_ass; auto.
Qed.

Lemma bindings_node_acc (t1 t2:t elt) x e z acc :
 bindings (Node z t1 x e t2) ++ acc =
 bindings t1 ++ (x,e) :: bindings t2 ++ acc.
Proof.
 unfold bindings; simpl; intros.
 rewrite !bindings_app, !app_nil_r, !app_ass; auto.
Qed.

Lemma bindings_node (t1 t2:t elt) x e z :
 bindings (Node z t1 x e t2) =
 bindings t1 ++ (x,e) :: bindings t2.
Proof.
 rewrite <- (app_nil_r (bindings _)), bindings_node_acc.
 now rewrite app_nil_r.
Qed.

Lemma rev_bindings_aux_rev m acc :
 rev_bindings_aux acc m = rev (bindings m) ++ acc.
Proof.
 revert acc. induction m; simpl; intros; auto.
 rewrite IHm2, IHm1, bindings_node, !rev_app_distr. simpl.
 now rewrite <- !app_assoc.
Qed.

Lemma rev_bindings_rev m : rev_bindings m = rev (bindings m).
Proof.
 unfold rev_bindings. rewrite rev_bindings_aux_rev. apply app_nil_r.
Qed.

Lemma in_bindings k v (m:t elt) : List.In (k,v) (bindings m) -> In k m.
Proof.
 intros IN. exists v. apply bindings_spec1, In_InA; eauto with *.
Qed.

Lemma in_bindings_uniq k k' v v' (m:t elt) `{!Ok m}:
 List.In (k,v) (bindings m) ->
 List.In (k',v') (bindings m) ->
 k == k' -> k = k' /\ v = v'.
Proof.
 induction m as [|c l IHl x e r IHr].
 - now cbn.
 - rewrite !bindings_node, !in_app_iff. simpl. invok.
   intros [INl|[[= <- <-]|INl]] [INr|[[= <- <-]|INr]] E; eauto;
   try apply in_bindings in INl; try apply in_bindings in INr; order.
Qed.

(** * Fold *)

Definition fold' {A} (f : key -> elt -> A -> A) m :=
  L.fold f (bindings m).

Lemma fold_equiv_aux {A} m (f : key -> elt -> A -> A) (a : A) acc :
 L.fold f (bindings_aux acc m) a = L.fold f acc (fold f m a).
Proof.
 revert a acc.
 induction m; simpl; trivial.
 intros. rewrite IHm1. simpl. apply IHm2.
Qed.

Lemma fold_equiv {A} m (f : key -> elt -> A -> A) (a : A) :
 fold f m a = fold' f m a.
Proof.
 unfold fold', bindings. now rewrite fold_equiv_aux.
Qed.

Lemma fold_spec m {A} (i:A)(f : key -> elt -> A -> A) :
 fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.
Proof.
 rewrite fold_equiv. unfold fold'. now rewrite L.fold_spec.
Qed.

(** * For_all / exists *)

Lemma for_all_spec (f:key->elt->bool) m :
  for_all f m = List.forallb (fun '(k,e) => f k e) (bindings m).
Proof.
induction m; simpl; auto.
rewrite bindings_node, forallb_app; simpl.
rewrite <- !andb_lazy_alt, andb_assoc, (andb_comm (f _ _)).
f_equal; auto. f_equal; auto.
Qed.

Lemma exists_spec (f:key->elt->bool) m :
  exists_ f m = List.existsb (fun '(k,e) => f k e) (bindings m).
Proof.
induction m; simpl; auto.
rewrite bindings_node, existsb_app; simpl.
rewrite <- !orb_lazy_alt, orb_assoc, (orb_comm (f _ _)).
f_equal; auto. f_equal; auto.
Qed.

(** * Comparison *)

(** [flatten_e e] returns the list of bindings of the enumeration [e]
    i.e. the list of bindings actually compared *)

Fixpoint flatten_e (e : enumeration elt) : list (key*elt) := match e with
  | End _ => nil
  | More x e t r => (x,e) :: bindings t ++ flatten_e r
 end.

Lemma flatten_e_bindings :
 forall (l:t elt) r x d z e,
 bindings l ++ flatten_e (More x d r e) =
 bindings (Node z l x d r) ++ flatten_e e.
Proof.
 intros. now rewrite bindings_node, <- app_assoc.
Qed.

Lemma cons_1 : forall (s:t elt) e,
  flatten_e (cons s e) = bindings s ++ flatten_e e.
Proof.
  induction s; auto; intros.
  simpl flatten_e; rewrite IHs1; apply flatten_e_bindings; auto.
Qed.

(** Proof of correction for the comparisons *)

Variable eqb : elt->elt->bool.

Local Notation Leq := (L.equal eqb).

Lemma equal_cont_Leq : forall m1 cont e2 l,
  (forall e, cont e = Leq l (flatten_e e)) ->
  equal_cont eqb m1 cont e2 = Leq (bindings m1 ++ l) (flatten_e e2).
Proof.
 induction m1 as [|h1 l1 Hl1 x1 d1 r1 Hr1]; intros; auto.
 rewrite bindings_node_acc; simpl.
 apply Hl1; auto.
 clear e2; intros [|x2 d2 r2 e2]; simpl; auto.
 case K.compare; auto. rewrite <- andb_lazy_alt. f_equal.
 rewrite <- cons_1; auto.
Qed.

Lemma equal_Leq m1 m2 :
  equal eqb m1 m2 = Leq (bindings m1) (bindings m2).
Proof.
 unfold equal.
 rewrite <- (app_nil_r (bindings m1)).
 replace (bindings m2) with (flatten_e (cons m2 (End _)))
  by (rewrite cons_1; simpl; rewrite app_nil_r; auto).
 apply equal_cont_Leq. now destruct e.
Qed.

Lemma Equivb_bindings m m' :
 Equivb eqb m m' <-> L.Equivb eqb (bindings m) (bindings m').
Proof.
unfold Equivb, L.Equivb; split; split; try red; intros.
do 2 rewrite bindings_in; firstorder.
destruct H.
apply (H2 k); rewrite <- bindings_spec1; auto.
do 2 rewrite <- bindings_in; firstorder.
destruct H.
apply (H2 k); unfold L.PX.MapsTo; rewrite bindings_spec1; auto.
Qed.

Lemma equal_spec (m m':t elt)`{!Ok m, !Ok m'} :
  equal eqb m m' = true <-> Equivb eqb m m'.
Proof.
 rewrite Equivb_bindings, equal_Leq.
 split; [apply L.equal_2 | apply L.equal_1];
   unfold L.Ok; apply bindings_spec2.
Qed.

Variable cmp : elt -> elt -> comparison.

Local Notation Lcmp := (L.compare cmp).

Lemma compare_cont_Lcmp : forall s1 cont e2 l,
  (forall e, cont e = Lcmp l (flatten_e e)) ->
  compare_cont cmp s1 cont e2 =
   Lcmp (bindings s1 ++ l) (flatten_e e2).
Proof.
 induction s1 as [|h1 l1 Hl1 x1 d1 r1 Hr1]; intros; simpl; auto.
 rewrite bindings_node_acc; simpl.
 apply Hl1; auto. clear e2. intros [|x2 d2 r2 e2]; simpl; auto.
 case K.compare; auto. case cmp; auto. rewrite <- cons_1; auto.
Qed.

Lemma compare_Lcmp m1 m2 :
 compare cmp m1 m2 = Lcmp (bindings m1) (bindings m2).
Proof.
 unfold compare; simpl.
 rewrite <- (app_nil_r (bindings m1)).
 replace (bindings m2) with (flatten_e (cons m2 (End _))) by
 (rewrite cons_1; simpl; rewrite app_nil_r; auto).
 apply compare_cont_Lcmp. now destruct e.
Qed.

Lemma compare_spec (m m':t elt)`{!Ok m, !Ok m'} :
  compare cmp m m' =
  list_compare (pair_compare K.compare cmp) (bindings m) (bindings m').
Proof. apply compare_Lcmp. Qed.

End Elt.

Section Map.
Variable elt elt' : Type.
Variable f : elt -> elt'.

Lemma map_spec m :
 bindings (map f m) = List.map (fun '(k,e) => (k,f e)) (bindings m).
Proof.
induction m; simpl; auto.
now rewrite !bindings_node, !map_app, IHm1, IHm2.
Qed.

Lemma map_in m x : x ∈ (map f m) <-> x ∈ m.
Proof.
induction m; simpl; intuition_in.
Qed.

Global Instance map_ok m `{!Ok m} : Ok (map f m).
Proof.
induction m; simpl; ok; intro; rewrite map_in; order.
Qed.

End Map.
Section Mapi.
Variable elt elt' : Type.
Variable f : key -> elt -> elt'.

Lemma mapi_spec m :
 bindings (mapi f m) = List.map (fun '(k,e) => (k,f k e)) (bindings m).
Proof.
induction m; simpl; auto.
now rewrite !bindings_node, !map_app, IHm1, IHm2.
Qed.

Lemma mapi_in m x : x ∈ (mapi f m) <-> x ∈ m.
Proof.
induction m; simpl; intuition_in.
Qed.

Global Instance mapi_ok m `{!Ok m} : Ok (mapi f m).
Proof.
induction m; simpl; ok; intro; rewrite mapi_in; order.
Qed.

End Mapi.

Section Elt.
Variable elt : Type.
Implicit Type m : t elt.

(** mindepth / maxdepth (used later in AVLproofs and RBTproofs *)

Local Open Scope nat.

Lemma mindepth_maxdepth m : mindepth m <= maxdepth m.
Proof.
 induction m; simpl; auto.
 rewrite <- Nat.succ_le_mono.
 transitivity (mindepth m1). apply Nat.le_min_l.
 transitivity (maxdepth m1). trivial. apply Nat.le_max_l.
Qed.

Lemma maxdepth_cardinal m : cardinal m < 2^(maxdepth m).
Proof.
 unfold Peano.lt.
 induction m as [|c l IHl x e r IHr].
 - auto.
 - simpl. rewrite <- Nat.add_succ_r, <- Nat.add_succ_l, Nat.add_0_r.
   apply Nat.add_le_mono; etransitivity;
   try apply IHl; try apply IHr; apply Nat.pow_le_mono; auto.
   * apply Nat.le_max_l.
   * apply Nat.le_max_r.
Qed.

Lemma mindepth_cardinal m : 2^(mindepth m) <= S (cardinal m).
Proof.
 unfold Peano.lt.
 induction m as [|c l IHl x e r IHr].
 - auto.
 - simpl. rewrite <- Nat.add_succ_r, <- Nat.add_succ_l, Nat.add_0_r.
   apply Nat.add_le_mono; etransitivity;
   try apply IHl; try apply IHr; apply Nat.pow_le_mono; auto.
   * apply Nat.le_min_l.
   * apply Nat.le_min_r.
Qed.

Lemma maxdepth_log_cardinal m : m <> Leaf _ ->
 Nat.log2 (cardinal m) < maxdepth m.
Proof.
 intros H.
 apply Nat.log2_lt_pow2. destruct m; simpl; intuition.
 apply maxdepth_cardinal.
Qed.

Lemma mindepth_log_cardinal m : mindepth m <= Nat.log2 (S (cardinal m)).
Proof.
 apply Nat.log2_le_pow2. auto with arith.
 apply mindepth_cardinal.
Qed.

End Elt.

End Props.
