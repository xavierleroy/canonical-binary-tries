
(** * Finite Modular Maps : Red-Black Trees *)

(** Author : Pierre Letouzey (Université de Paris - INRIA),
    adapted from earlier works in Coq Standard Library, see README.md.
    Licence : LGPL 2.1, see file LICENSE. *)

(** This module implements finite maps using Red-Black trees.
    This code is based on Coq [MSetRBT.v], due initially to
    Andrew W. Appel, 2011. See initial comment at the beginning
    of [MSetRBT.v].

    Note that we only prove here that the operations below preserve
    the binary search tree invariant ([Bst], a.k.a [Ok] predicate here),
    but *not* the Red/Black balancing invariant. Indeed, the former
    is enough to implement the desired interface [S], and ensure
    observational correctness. And proceeding this way is quite lighter.
    For the proofs of RBT balancing, see [Tries.MMaps.RBTproofs].
*)

From Coq Require Rtauto.
From Coq Require Import Bool BinPos Pnat Setoid SetoidList PeanoNat.
From Coq Require Import Orders OrdersFacts OrdersLists.
From Tries.MMaps Require Import Utils Interface OrdList GenTree.

Local Set Implicit Arguments.
Local Unset Strict Implicit.
Import ListNotations.

(* For nicer extraction, we create inductive principles
   only when needed *)
Local Unset Elimination Schemes.

(** The type of color annotation. *)

Inductive color := Red | Black.

Module Color.
 Definition t := color.
End Color.

(** * The Raw functor

   Functor of pure functions + separate proofs of invariant
   preservation *)

Module MakeRaw (K: OrderedType) <: Raw.S K.

(** ** Generic trees instantiated with Red/Black colors *)

(** We reuse a generic definition of trees where the information
    parameter is a [Color.t]. Functions like mem or fold are also
    provided by this generic functor. *)

Include Tries.MMaps.GenTree.Ops K Color.
Import GenTree.PairNotations. (* #1 and #2 for fst and snd *)
Local Open Scope lazy_bool_scope.
Local Notation color := Color.t.
Local Arguments Leaf {elt}.
Local Notation Rd := (@Node _ Red).
Local Notation Bk := (@Node _ Black).

Section Elt.
Variable elt : Type.
Local Notation t := (tree elt).
Implicit Types l r m : t.
Implicit Types e : elt.

(** ** Basic tree *)

Definition singleton (k : key) (v : elt) : t :=
  Node Black Leaf k v Leaf.

(** ** Changing root color *)

Definition makeBlack m : t :=
 match m with
 | Leaf => Leaf
 | Node _ a x v b => Bk a x v b
 end.

Definition makeRed m : t :=
 match m with
 | Leaf => Leaf
 | Node _ a x v b => Rd a x v b
 end.

(** ** Balancing *)

(** We adapt when one side is not a true red-black tree.
    Both sides have the same black depth. *)

Definition lbal l k vk r :=
 match l with
 | Rd (Rd a x vx b) y vy c => Rd (Bk a x vx b) y vy (Bk c k vk r)
 | Rd a x vx (Rd b y vy c) => Rd (Bk a x vx b) y vy (Bk c k vk r)
 | _ => Bk l k vk r
 end.

Definition rbal l k vk r :=
 match r with
 | Rd (Rd b y vy c) z vz d => Rd (Bk l k vk b) y vy (Bk c z vz d)
 | Rd b y vy (Rd c z vz d) => Rd (Bk l k vk b) y vy (Bk c z vz d)
 | _ => Bk l k vk r
 end.

(** A variant of [rbal], with reverse pattern order. *)

Definition rbal' l k vk r :=
 match r with
 | Rd b y vy (Rd c z vz d) => Rd (Bk l k vk b) y vy (Bk c z vz d)
 | Rd (Rd b y vy c) z vz d => Rd (Bk l k vk b) y vy (Bk c z vz d)
 | _ => Bk l k vk r
 end.

(** Balancing with different black depth.
    One side is almost a red-black tree, while the other is
    a true red-black tree, but with black depth + 1.
    Used in deletion. *)

Definition lbalS l k vk r :=
 match l with
 | Rd a x vx b => Rd (Bk a x vx b) k vk r
 | _ =>
   match r with
   | Bk a y vy b => rbal' l k vk (Rd a y vy b)
   | Rd (Bk a y vy b) z vz c => Rd (Bk l k vk a) y vy (rbal' b z vz (makeRed c))
   | _ => Rd l k vk r (* impossible *)
   end
 end.

Definition rbalS l k vk r :=
 match r with
 | Rd b y vy c => Rd l k vk (Bk b y vy c)
 | _ =>
   match l with
   | Bk a x vx b => lbal (Rd a x vx b) k vk r
   | Rd a x vx (Bk b y vy c) => Rd (lbal (makeRed a) x vx b) y vy (Bk c k vk r)
   | _ => Rd l k vk r (* impossible *)
   end
 end.

(** ** Insertion *)

Fixpoint ins x vx s :=
 match s with
 | Leaf => Rd Leaf x vx Leaf
 | Node c l y vy r =>
   match K.compare x y with
   | Eq => Node c l y vx r
   | Lt =>
     match c with
     | Red => Rd (ins x vx l) y vy r
     | Black => lbal (ins x vx l) y vy r
     end
   | Gt =>
     match c with
     | Red => Rd l y vy (ins x vx r)
     | Black => rbal l y vy (ins x vx r)
     end
   end
 end.

Definition add x vx s := makeBlack (ins x vx s).

(** ** Deletion *)

Fixpoint append (l:t) : t -> t :=
 match l with
 | Leaf => fun r => r
 | Node lc ll lx lv lr =>
   fix append_l (r:t) : t :=
   match r with
   | Leaf => l
   | Node rc rl rx rv rr =>
     match lc, rc with
     | Red, Red =>
       let lrl := append lr rl in
       match lrl with
       | Rd lr' x v rl' => Rd (Rd ll lx lv lr') x v (Rd rl' rx rv rr)
       | _ => Rd ll lx lv (Rd lrl rx rv rr)
       end
     | Black, Black =>
       let lrl := append lr rl in
       match lrl with
       | Rd lr' x v rl' => Rd (Bk ll lx lv lr') x v (Bk rl' rx rv rr)
       | _ => lbalS ll lx lv (Bk lrl rx rv rr)
       end
     | Black, Red => Rd (append_l rl) rx rv rr
     | Red, Black => Rd ll lx lv (append lr r)
     end
   end
 end.

Fixpoint del x m : t :=
 match m with
 | Leaf => Leaf
 | Node _ a y v b =>
   match K.compare x y with
   | Eq => append a b
   | Lt =>
     match a with
     | Bk _ _ _ _ => lbalS (del x a) y v b
     | _ => Rd (del x a) y v b
     end
   | Gt =>
     match b with
     | Bk _ _ _ _ => rbalS a y v (del x b)
     | _ => Rd a y v (del x b)
     end
   end
 end.

Definition remove x m := makeBlack (del x m).

(** ** Tree-ification

    We rebuild a tree of size [if pred then n-1 else n] as soon
    as the list [l] has enough elements *)

Definition klist A := list (key * A).
Local Notation treeify_t := (klist elt -> t * klist elt).

Definition bogus : t * klist elt := (Leaf, nil).

Definition treeify_zero : treeify_t :=
 fun acc => (Leaf,acc).

Definition treeify_one : treeify_t :=
 fun acc => match acc with
 | (x,v)::acc => (Rd Leaf x v Leaf, acc)
 | _ => bogus
 end.

Definition treeify_cont (f g : treeify_t) : treeify_t :=
 fun acc =>
 match f acc with
 | (l, (x,v)::acc) =>
   match g acc with
   | (r, acc) => (Bk l x v r, acc)
   end
 | _ => bogus
 end.

Fixpoint treeify_aux (pred:bool)(n: positive) : treeify_t :=
 match n with
 | xH => if pred then treeify_zero else treeify_one
 | xO n => treeify_cont (treeify_aux pred n) (treeify_aux true n)
 | xI n => treeify_cont (treeify_aux false n) (treeify_aux pred n)
 end.

Fixpoint plength_aux (l:klist elt)(p:positive) := match l with
 | nil => p
 | _::l => plength_aux l (Pos.succ p)
end.

Definition plength (l:klist elt) := plength_aux l 1.

Definition treeify (l:klist elt) :=
 fst (treeify_aux true (plength l) l).

End Elt.

(** * Map with removal *)

Definition ocons {A B} (a:A) (o:option B) (l:list (A*B)) :=
 match o with
 | None => l
 | Some b => (a,b)::l
 end.

Section Mapo.
Variable elt elt' : Type.
Variable f : key -> elt -> option elt'.

Fixpoint mapoL (l : klist elt)(acc : klist elt') : klist elt' :=
  match l with
   | nil => acc
   | (k,v)::l => mapoL l (ocons k (f k v) acc)
  end.

Definition mapo (m : t elt) : t elt' :=
 treeify (mapoL (rev_bindings m) nil).

End Mapo.

(** * Merge *)

Section Merge.
Variable elt elt' elt'' : Type.
Variable f : key -> option elt -> option elt' -> option elt''.

Fixpoint mergeL (l1:klist elt) :
 klist elt' -> klist elt'' -> klist elt'' :=
 match l1 with
 | nil => mapoL (fun k v' => f k None (Some v'))
 | (x,vx)::l1' =>
    fix mergeL_l1 l2 acc :=
    match l2 with
    | nil => mapoL (fun k v => f k (Some v) None) l1 acc
    | (y,vy)::l2' =>
       match K.compare x y with
       | Eq => mergeL l1' l2' (ocons x (f x (Some vx) (Some vy)) acc)
       | Lt => mergeL_l1 l2' (ocons y (f y None (Some vy)) acc)
       | Gt => mergeL l1' l2 (ocons x (f x (Some vx) None) acc)
       end
    end
 end.

Definition merge (m1 : t elt) (m2 : t elt') : t elt'' :=
 treeify (mergeL (rev_bindings m1) (rev_bindings m2) nil).

End Merge.

(** * Correctness proofs *)

Include Tries.MMaps.GenTree.Props K Color.
Import Ind.

Local Infix "∈" := In (at level 70).
Local Infix "==" := K.eq (at level 70).
Local Infix "<" := lessthan.
Local Infix "===" := Equal (at level 70).
Local Notation "m @ x ↦ e" := (MapsTo x e m)
 (at level 9, format "m '@' x  '↦'  e").

Local Hint Constructors tree MapsTo Bst : map.
Local Hint Unfold Ok Bst_Ok In : map.
Local Hint Immediate F.eq_sym : map.
Local Hint Resolve F.eq_refl : map.
Local Hint Resolve above_notin above_trans below_notin below_trans : map.
Local Hint Resolve above_leaf below_leaf : map.

Ltac rtauto := Rtauto.rtauto.
Ltac autorew := autorewrite with map.
Tactic Notation "autorew" "in" ident(H) := autorewrite with map in H.
Ltac treeorder := try intro; autorew; intuition_in; order.

Ltac induct m :=
 induction m as [|c l IHl x' vx' r IHr]; simpl; intros;
 [|case K.compare_spec; intros; invok; chok].

Ltac destmatch :=
 match goal with
 | |- context [match K.compare _ _ with _ => _ end] =>
   case K.compare_spec; destmatch
 | |- context [match ?x with _ => _ end] =>
   destruct x; destmatch
 | _ => idtac
 end.

Section Elt.
Variable elt : Type.
Implicit Types m : t elt.
Implicit Types k x y : key.
Implicit Types v vx vy : elt.

(** ** Singleton set *)

Lemma singleton_spec x (e:elt) : bindings (singleton x e) = (x,e)::nil.
Proof.
 unfold singleton. now rewrite bindings_node.
Qed.

Global Instance singleton_ok x vx : Ok (singleton x vx).
Proof.
 unfold singleton. ok.
Qed.

(** ** makeBlack, MakeRed *)

Global Instance makeBlack_ok m `{!Ok m} : Ok (makeBlack m).
Proof.
 destruct m; simpl; ok.
Qed.

Global Instance makeRed_ok m `{!Ok m} : Ok (makeRed m).
Proof.
 destruct m; simpl; ok.
Qed.

Lemma makeBlack_mapsto m x v : (makeBlack m)@x ↦ v <-> m@x ↦ v.
Proof.
 destruct m; simpl; intuition_m.
Qed.

Lemma makeRed_mapsto m x v : (makeRed m)@x ↦ v <-> m@x ↦ v.
Proof.
 destruct m; simpl; intuition_m.
Qed.

Lemma makeBlack_in m x : x ∈ (makeBlack m) <-> x ∈ m.
Proof.
 destruct m; simpl; intuition_in.
Qed.

Lemma makeRed_in m x : x ∈ (makeRed m) <-> x ∈ m.
Proof.
 destruct m; simpl; intuition_in.
Qed.

Lemma makeBlack_find m : makeBlack m === m.
Proof.
 now destruct m.
Qed.

Lemma makeRed_find m : makeRed m === m.
Proof.
 now destruct m.
Qed.

(** ** Generic handling for red-matching and red-red-matching *)

Definition isblack m :=
 match m with Bk _ _ _ _ => True | _ => False end.

Definition notblack m :=
 match m with Bk _ _ _ _ => False | _ => True end.

Definition notred m :=
 match m with Rd _ _ _ _ => False | _ => True end.

Definition rcase {A} f g m : A :=
 match m with
 | Rd a x v b => f a x v b
 | _ => g m
 end.

Inductive rspec {A} f g : t elt -> A -> Prop :=
 | rred a x v b : rspec f g (Rd a x v b) (f a x v b)
 | relse t : notred t -> rspec f g t (g t).

Fact rmatch {A} f g m : rspec (A:=A) f g m (rcase f g m).
Proof.
unfold rcase. destmatch; now constructor.
Qed.

Definition rrcase {A} f g m : A :=
 match m with
 | Rd (Rd a x vx b) y vy c => f a x vx b y vy c
 | Rd a x vx (Rd b y vy c) => f a x vx  b y vy c
 | _ => g m
 end.

Notation notredred := (rrcase (fun _ _ _ _ _ _ _ => False) (fun _ => True)).

Inductive rrspec {A} f g : t elt -> A -> Prop :=
 | rrleft a x vx b y vy c :
     rrspec f g (Rd (Rd a x vx b) y vy c) (f a x vx b y vy c)
 | rrright a x vx b y vy c :
     rrspec f g (Rd a x vx (Rd b y vy c)) (f a x vx b y vy c)
 | rrelse m : notredred m -> rrspec f g m (g m).

Fact rrmatch {A} f g m : rrspec (A:=A) f g m (rrcase f g m).
Proof.
unfold rrcase. destmatch; now constructor.
Qed.

Definition rrcase' {A} f g m : A :=
 match m with
 | Rd a x vx (Rd b y vy c) => f a x vx b y vy c
 | Rd (Rd a x vx b) y vy c => f a x vx b y vy c
 | _ => g m
 end.

Fact rrmatch' {A} f g m : rrspec (A:=A) f g m (rrcase' f g m).
Proof.
unfold rrcase'. destmatch; now constructor.
Qed.

(** Balancing operations are instances of generic match *)

Fact lbal_match l k v r :
 rrspec
   (fun a x vx b y vy c => Rd (Bk a x vx b) y vy (Bk c k v r))
   (fun l => Bk l k v r)
   l
   (lbal l k v r).
Proof.
 exact (rrmatch _ _ _).
Qed.

Fact rbal_match l k v r :
 rrspec
   (fun a x vx b y vy c => Rd (Bk l k v a) x vx (Bk b y vy c))
   (fun r => Bk l k v r)
   r
   (rbal l k v r).
Proof.
 exact (rrmatch _ _ _).
Qed.

Fact rbal'_match l k v r :
 rrspec
   (fun a x vx b y vy c => Rd (Bk l k v a) x vx (Bk b y vy c))
   (fun r => Bk l k v r)
   r
   (rbal' l k v r).
Proof.
 exact (rrmatch' _ _ _).
Qed.

Fact lbalS_match l x vx r :
 rspec
  (fun a y vy b => Rd (Bk a y vy b) x vx r)
  (fun l =>
    match r with
    | Bk a y vy b => rbal' l x vx (Rd a y vy b)
    | Rd (Bk a y vy b) z vz c =>
      Rd (Bk l x vx a) y vy (rbal' b z vz (makeRed c))
    | _ => Rd l x vx r
    end)
  l
  (lbalS l x vx r).
Proof.
 exact (rmatch _ _ _).
Qed.

Fact rbalS_match l x vx r :
 rspec
  (fun a y vy b => Rd l x vx (Bk a y vy b))
  (fun r =>
    match l with
    | Bk a y vy b => lbal (Rd a y vy b) x vx r
    | Rd a y vy (Bk b z vz c) =>
      Rd (lbal (makeRed a) y vy b) z vz (Bk c x vx r)
    | _ => Rd l x vx r
    end)
  r
  (rbalS l x vx r).
Proof.
 exact (rmatch _ _ _).
Qed.

(** ** Balancing for insertion *)

Global Instance lbal_ok l x v r `(!Ok l, !Ok r, l < x, x < r) :
 Ok (lbal l x v r).
Proof.
 destruct (lbal_match l x v r); ok; invlt; intuition; eautom.
Qed.

Global Instance rbal_ok l x v r `(!Ok l, !Ok r, l < x, x < r) :
 Ok (rbal l x v r).
Proof.
 destruct (rbal_match l x v r); ok; invlt; intuition; eautom.
Qed.

Global Instance rbal'_ok l x v r `(!Ok l, !Ok r, l < x, x < r) :
 Ok (rbal' l x v r).
Proof.
 destruct (rbal'_match l x v r); ok; invlt; intuition; eautom.
Qed.

(** Note : Rd is arbitrary here and in all similar results below *)

Lemma lbal_mapsto l x vx r y vy :
 (lbal l x vx r)@y ↦ vy <-> (Rd l x vx r)@y ↦ vy.
Proof.
 case lbal_match; intuition_m.
Qed.

Lemma rbal_mapsto l x vx r y vy :
 (rbal l x vx r)@y ↦ vy <-> (Rd l x vx r)@y ↦ vy.
Proof.
 case rbal_match; intuition_m.
Qed.

Lemma rbal'_mapsto l x vx r y vy :
 (rbal' l x vx r)@y ↦ vy <-> (Rd l x vx r)@y ↦ vy.
Proof.
 case rbal'_match; intuition_m.
Qed.

Lemma lbal_in l x v r y :
 y ∈ (lbal l x v r) <-> y == x \/ y ∈ l \/ y ∈ r.
Proof.
 unfold "∈". setoid_rewrite lbal_mapsto. setoid_rewrite node_mapsto.
 firstorder. exists v. firstorder.
Qed.

Lemma rbal_in l x v r y :
 y ∈ (rbal l x v r) <-> y == x \/ y ∈ l \/ y ∈ r.
Proof.
 unfold "∈". setoid_rewrite rbal_mapsto; setoid_rewrite node_mapsto.
 firstorder. exists v. firstorder.
Qed.

Lemma rbal'_in l x r v y :
 y ∈ (rbal' l x v r) <-> y == x \/ y ∈ l \/ y ∈ r.
Proof.
 unfold "∈". setoid_rewrite rbal'_mapsto; setoid_rewrite node_mapsto.
 firstorder. exists v. firstorder.
Qed.

Lemma lbal_find l x v r `{!Ok l, !Ok r} :
 l < x -> x < r ->
 lbal l x v r === Rd l x v r.
Proof.
 intros Hl Hr y. apply find_mapsto_equiv; auto using lbal_mapsto; autok.
Qed.

Lemma rbal_find l x v r `{!Ok l, !Ok r} :
 l < x -> x < r ->
 rbal l x v r === Rd l x v r.
Proof.
 intros Hl Hr y. apply find_mapsto_equiv; auto using rbal_mapsto; autok.
Qed.

Lemma rbal'_find l x v r `{!Ok l, !Ok r} :
 l < x -> x < r ->
 rbal' l x v r === Rd l x v r.
Proof.
 intros Hl Hr y. apply find_mapsto_equiv; auto using rbal'_mapsto; autok.
Qed.

Hint Rewrite (@in_node elt) makeRed_in makeBlack_in : map.
Hint Rewrite lbal_in rbal_in rbal'_in : map.

(** ** Insertion *)

Lemma ins_in m x v y :
 y ∈ (ins x v m) <-> y == x \/ y ∈ m.
Proof.
 induct m; destmatch; autorew; rewrite ?IHl, ?IHr; intuition_in.
 setoid_replace y with x; eauto.
Qed.
Hint Rewrite ins_in : map.

Lemma ins_above m x v y : m < y -> x < y -> ins x v m < y.
Proof.
 intros. treeorder.
Qed.

Lemma ins_below m x v y : y < m -> y < x -> y < ins x v m.
Proof.
 intros. treeorder.
Qed.
Local Hint Resolve ins_above ins_below : map.

Global Instance ins_ok m x v `{!Ok m} : Ok (ins x v m).
Proof.
 induct m; auto; destmatch;
 (eapply lbal_ok || eapply rbal_ok || ok); auto; treeorder.
Qed.

Lemma ins_spec1 m x v `{!Ok m} : find x (ins x v m) = Some v.
Proof.
 induct m; simpl; destmatch;
  rewrite ?lbal_find, ?rbal_find by eauto with *;
  simpl; destmatch; auto; try order.
Qed.

Lemma ins_spec2 m x y v `{!Ok m} : ~ x == y ->
 find y (ins x v m) = find y m.
Proof.
 induct m; simpl; destmatch;
  rewrite ?lbal_find, ?rbal_find by eauto with *;
  simpl; destmatch; auto; try order.
Qed.

Lemma ins_find m x y v `{!Ok m} :
 find y (ins x v m) =
  match K.compare y x with Eq => Some v | _ => find y m end.
Proof.
 destmatch; intros E.
 - apply find_spec; autok. rewrite E. apply find_spec; autok.
   now apply ins_spec1.
 - apply ins_spec2; trivial; order.
 - apply ins_spec2; trivial; order.
Qed.

Global Instance add_ok m x v `{!Ok m} : Ok (add x v m).
Proof.
 unfold add; autok.
Qed.

Lemma add_in m x v y :
 y ∈ (add x v m) <-> y == x \/ y ∈ m.
Proof.
 unfold add. now autorew.
Qed.
Hint Rewrite add_in : map.

Lemma add_spec1 m x v `{!Ok m} : find x (add x v m) = Some v.
Proof.
unfold add. rewrite makeBlack_find. now apply ins_spec1.
Qed.

Lemma add_spec2 m x y v `{!Ok m} : ~ x == y ->
 find y (add x v m) = find y m.
Proof.
unfold add. rewrite makeBlack_find. now apply ins_spec2.
Qed.


(** ** Balancing for deletion *)

Global Instance lbalS_ok l x v r :
  forall `(!Ok l, !Ok r, l < x, x < r), Ok (lbalS l x v r).
Proof.
 case lbalS_match; intros; destmatch; try treeorder; invok; invlt.
 - ok; intuition.
 - constructor; chok; try treeorder. apply rbal'_ok; treeorder.
 - apply rbal'_ok; treeorder.
Qed.

Global Instance rbalS_ok l x v r :
 forall `(!Ok l, !Ok r, l < x, x < r), Ok (rbalS l x v r).
Proof.
 case rbalS_match; intros; destmatch; try treeorder; invok; invlt.
 - ok; intuition.
 - constructor; chok; try treeorder. apply lbal_ok; treeorder.
 - apply lbal_ok; treeorder.
Qed.

Lemma lbalS_mapsto l x v r y vy :
  (lbalS l x v r)@y ↦ vy <-> (Rd l x v r)@y ↦ vy.
Proof.
 case lbalS_match; intros.
 - intuition_m.
 - destmatch; intuition_m;
   rewrite ?rbal'_mapsto in *; intuition_m;
   rewrite ?makeRed_mapsto in *; intuition_m;
   apply MapsRight; rewrite rbal'_mapsto; intuition_m.
   apply MapsRight. now rewrite makeRed_mapsto.
Qed.

Lemma rbalS_mapsto l x v r y vy :
  (rbalS l x v r)@y ↦ vy <-> (Rd l x v r)@y ↦ vy.
Proof.
 case rbalS_match; intros.
 - intuition_m.
 - destmatch; intuition_m;
   rewrite ?lbal_mapsto in *; intuition_m;
   rewrite ?makeRed_mapsto in *; intuition_m;
   apply MapsLeft; rewrite lbal_mapsto; intuition_m.
   apply MapsLeft. now rewrite makeRed_mapsto.
Qed.

Lemma lbalS_in l x v r y :
  y ∈ (lbalS l x v r) <-> y == x \/ y ∈ l \/ y ∈ r.
Proof.
 unfold "∈"; setoid_rewrite lbalS_mapsto; setoid_rewrite node_mapsto.
 firstorder. exists v. firstorder.
Qed.

Lemma rbalS_in l x r v y :
  y ∈ (rbalS l x v r) <-> y == x \/ y ∈ l \/ y ∈ r.
Proof.
 unfold "∈"; setoid_rewrite rbalS_mapsto; setoid_rewrite node_mapsto.
 firstorder. exists v. firstorder.
Qed.

Lemma lbalS_find l x v r `{!Ok l, !Ok r} : l < x -> x < r ->
  lbalS l x v r === Rd l x v r.
Proof.
 intros Hl Hr y. apply find_mapsto_equiv; auto using lbalS_mapsto; autok.
Qed.

Lemma rbalS_find l x v r `{!Ok l, !Ok r} : l < x -> x < r ->
  rbalS l x v r === Rd l x v r.
Proof.
 intros Hl Hr y. apply find_mapsto_equiv; auto using rbalS_mapsto; autok.
Qed.

Hint Rewrite lbalS_in rbalS_in : map.

(** ** Append for deletion *)

Ltac append_tac l r :=
 induction l as [| lc ll _ lx lv lr IHlr];
 [intro r; simpl
 |induction r as [| rc rl IHrl rx rv rr _];
   [simpl
   |destruct lc, rc;
     [specialize (IHlr rl); clear IHrl
     |simpl;
      assert (Hr:notred (Bk rl rx rv rr)) by (simpl; trivial);
      set (r:=Bk rl rx rv rr) in *; clearbody r; clear IHrl rl rx rv rr;
      specialize (IHlr r)
     |change (append _ _) with (Rd (append (Bk ll lx lv lr) rl) rx rv rr);
      assert (Hl:notred (Bk ll lx lv lr)) by (simpl; trivial);
      set (l:=Bk ll lx lv lr) in *; clearbody l; clear IHlr ll lx lv lr
     |specialize (IHlr rl); clear IHrl]]].

Lemma mapsto_2levels c cl ll lx lv lr x v cr rl rx rv rr y e :
 (Node c (Node cl ll lx lv lr) x v (Node cr rl rx rv rr))@y ↦ e <->
  (Node cl ll lx lv Leaf)@y ↦ e \/
  (Node c lr x v rl)@y ↦ e \/
  (Node cr Leaf rx rv rr)@y ↦ e.
Proof.
 rewrite !node_mapsto, !leaf_mapsto. rtauto.
Qed.

Lemma append_mapsto l r y v :
  (append l r)@y ↦ v <-> l@y ↦ v \/ r@y ↦ v.
Proof.
 revert r.
 append_tac l r; try (intuition_m; fail).
 - (* Rd / Rd *)
   simpl. destmatch.
   + intuition_m.
   + rewrite mapsto_2levels. factornode m.
     rewrite !node_mapsto, !leaf_mapsto. rtauto.
   + factornode m. rewrite !node_mapsto. rtauto.
 - (* Bk / Bk *)
   simpl. destmatch; rewrite ?lbalS_mapsto.
   + intuition_m.
   + rewrite mapsto_2levels. factornode m.
     rewrite !node_mapsto, !leaf_mapsto. rtauto.
   + factornode m. rewrite !node_mapsto. rtauto.
Qed.

Lemma append_in (l r : t elt) x :
 x ∈ (append l r) <-> x ∈ l \/ x ∈ r.
Proof.
 unfold "∈". setoid_rewrite append_mapsto. firstorder.
Qed.

Hint Rewrite append_in : map.

Global Instance append_ok : forall l r `{!Ok l, !Ok r},
 l < r -> Ok (@append elt l r).
Proof.
 append_tac l r; trivial; intros OK OK' AP;
 rewrite ?apart_node_l, ?apart_node_r in AP;
 decompose [and] AP; clear AP; ok; try treeorder.
 - (* Rd / Rd *)
   assert (U : Ok (append lr rl)) by auto.
   assert (V : lx < append lr rl) by (invlt;treeorder).
   assert (W : append lr rl < rx) by (invlt;treeorder).
   simpl. destmatch; invlt; ok; intuition; eautom.
 - (* Bk / Bk *)
   assert (U : Ok (append lr rl)) by auto.
   assert (V : lx < append lr rl) by (invlt;treeorder).
   assert (W : append lr rl < rx) by (invlt;treeorder).
   simpl. destmatch; try apply lbalS_ok; invlt; ok; intuition; eautom.
Qed.

(** ** Deletion *)

Lemma del_in m x y `{!Ok m} :
 y ∈ (del x m) <-> y ∈ m /\ ~ y==x.
Proof.
induct m; destmatch; autorew; try rewrite IHl; try rewrite IHr;
 try clear IHl IHr; treeorder.
Qed.

Hint Rewrite del_in : map.

Global Instance del_ok m x `{!Ok m} : Ok (del x m).
Proof.
induct m.
- trivial.
- eapply append_ok; eauto using between.
- assert (del x l < x') by treeorder.
  destmatch; ok.
- assert (x' < del x r) by treeorder.
  destmatch; ok.
Qed.

Lemma del_spec1 m x `{!Ok m} : find x (del x m) = None.
Proof.
apply not_find_iff; ok. rewrite del_in; treeorder.
Qed.

Lemma del_spec2 m x y `{!Ok m} : ~ x == y ->
 find y (del x m) = find y m.
Proof.
intros.
apply find_mapsto_equiv; ok.
induct m.
- easy.
- rewrite append_mapsto, node_mapsto. treeorder.
- destmatch.
  + simpl. intuition_m.
  + rewrite 2 node_mapsto. factornode l. now rewrite IHl by ok.
  + rewrite lbalS_mapsto, 2 node_mapsto. factornode l.
    now rewrite IHl by ok.
- destmatch.
  + simpl. intuition_m.
  + rewrite 2 node_mapsto. factornode r. now rewrite IHr by ok.
  + rewrite rbalS_mapsto, 2 node_mapsto. factornode r.
    now rewrite IHr by ok.
Qed.

Lemma remove_in m x y `{!Ok m} :
 y ∈ (remove x m) <-> y ∈ m /\ ~ y==x.
Proof.
unfold remove. now autorew.
Qed.

Hint Rewrite remove_in : map.

Global Instance remove_ok m x `{!Ok m} : Ok (remove x m).
Proof.
unfold remove; ok.
Qed.

Lemma remove_spec1 m x `{!Ok m} : find x (remove x m) = None.
Proof.
unfold remove. rewrite makeBlack_find. now apply del_spec1.
Qed.

Lemma remove_spec2 m x y `{!Ok m} : ~ x == y ->
 find y (remove x m) = find y m.
Proof.
unfold remove. rewrite makeBlack_find. now apply del_spec2.
Qed.

(** ** Treeify *)

Local Notation ifpred p n := (if p then pred n else n%nat).
Local Notation treeify_t := (klist elt -> t elt * klist elt).

Definition treeify_invariant size (f:treeify_t) :=
 forall acc,
 size <= length acc ->
 let (m,acc') := f acc in
 cardinal m = size /\ acc = bindings m ++ acc'.

Lemma treeify_zero_spec : treeify_invariant 0 (@treeify_zero elt).
Proof.
 intro. simpl. auto.
Qed.

Lemma treeify_one_spec : treeify_invariant 1 (@treeify_one elt).
Proof.
 intros [|x acc]; simpl; auto. inversion 1.
 destruct x. simpl; auto.
Qed.

Lemma treeify_cont_spec f g size1 size2 size :
 treeify_invariant size1 f ->
 treeify_invariant size2 g ->
 size = S (size1 + size2) ->
 treeify_invariant size (treeify_cont f g).
Proof.
 intros Hf Hg EQ acc LE. unfold treeify_cont.
 specialize (Hf acc).
 destruct (f acc) as (t1,acc1).
 destruct Hf as (Hf1,Hf2).
  { transitivity size; trivial. subst. auto with arith. }
 destruct acc1 as [|x acc1].
  { exfalso. revert LE. apply Nat.lt_nge. subst.
    rewrite app_nil_r, <- cardinal_spec; auto with arith. }
 specialize (Hg acc1).
 destruct (g acc1) as (t2,acc2).
 destruct Hg as (Hg1,Hg2).
  { revert LE. subst.
    rewrite app_length, <- cardinal_spec. simpl.
    rewrite Nat.add_succ_r, <- Nat.succ_le_mono.
    apply Nat.add_le_mono_l. }
 destruct x; simpl.
 rewrite bindings_node_acc. subst; auto.
Qed.

Lemma treeify_aux_spec n (p:bool) :
 treeify_invariant (ifpred p (Pos.to_nat n)) (treeify_aux p n).
Proof.
 revert p.
 induction n as [n|n|]; intros p; simpl treeify_aux.
 - eapply treeify_cont_spec; [ apply (IHn false) | apply (IHn p) | ].
   rewrite Pos2Nat.inj_xI.
   assert (H := Pos2Nat.is_pos n). apply Nat.neq_0_lt_0 in H.
   destruct p; simpl; intros; rewrite Nat.add_0_r; trivial.
   now rewrite <- Nat.add_succ_r, Nat.succ_pred; trivial.
 - eapply treeify_cont_spec; [ apply (IHn p) | apply (IHn true) | ].
   rewrite Pos2Nat.inj_xO.
   assert (H := Pos2Nat.is_pos n). apply Nat.neq_0_lt_0 in H.
   rewrite <- Nat.add_succ_r, Nat.succ_pred by trivial.
   destruct p; simpl; intros; rewrite Nat.add_0_r; trivial.
   symmetry. now apply Nat.add_pred_l.
 - destruct p; [ apply treeify_zero_spec | apply treeify_one_spec ].
Qed.

Lemma plength_aux_spec l p :
  Pos.to_nat (@plength_aux elt l p) = length l + Pos.to_nat p.
Proof.
 revert p. induction l; trivial. simpl plength_aux.
 intros. now rewrite IHl, Pos2Nat.inj_succ, Nat.add_succ_r.
Qed.

Lemma plength_spec l : Pos.to_nat (@plength elt l) = S (length l).
Proof.
 unfold plength. rewrite plength_aux_spec. apply Nat.add_1_r.
Qed.

Lemma treeify_bindings l : bindings (@treeify elt l) = l.
Proof.
 assert (H := @treeify_aux_spec (plength l) true l).
 unfold treeify. destruct treeify_aux as (t,acc); simpl in *.
 destruct H as (H,H'). { now rewrite plength_spec. }
 subst l. rewrite plength_spec, app_length, <- cardinal_spec in *.
 destruct acc.
 * now rewrite app_nil_r.
 * exfalso. revert H. simpl.
   rewrite Nat.add_succ_r, Nat.add_comm.
   apply Nat.succ_add_discr.
Qed.

Lemma treeify_mapsto x v l : (treeify l)@x ↦ v <-> InA O.eqke (x,v) l.
Proof.
 intros. now rewrite <- bindings_spec1, treeify_bindings.
Qed.

(** Apart predicate on lists *)

Global Instance lt_klist A B : LessThan (klist A) (klist B)
  := fun lA lB =>
      forall ka kb, List.In ka lA -> List.In kb lB -> ka#1 < kb#1.

Section ApartList.
Variable A B : Type.
Implicit Types lA : klist A.
Implicit Types lB : klist B.

Lemma ApartL_rev lA lB : (rev lA) < lB <-> lA < lB.
Proof.
 unfold "<", lt_klist. now setoid_rewrite <- in_rev.
Qed.

Lemma ApartL_appl lA lA' lB :
 lA++lA' < lB <-> lA < lB /\ lA' < lB.
Proof.
 unfold "<", lt_klist. setoid_rewrite in_app_iff; firstorder.
Qed.

Lemma ApartL_appr lA lB lB' :
 lA < lB++lB' <-> lA < lB /\ lA < lB'.
Proof.
 unfold "<", lt_klist. setoid_rewrite in_app_iff; firstorder.
Qed.

Lemma ApartL_consl ka lA lB :
 (ka::lA) < lB <-> [ka] < lB /\ lA < lB.
Proof.
 apply (ApartL_appl [ka]).
Qed.

Lemma ApartL_consr kb lA lB :
 lA < (kb::lB) <-> lA < [kb] /\ lA < lB.
Proof.
 apply (ApartL_appr lA [kb]).
Qed.

End ApartList.

Lemma ApartL_eqk_l A B B' (lA : klist A) (kb:key*B) (kb':key*B') :
 [kb] < lA -> kb#1 == kb'#1 -> [kb'] < lA.
Proof.
 intros AP E (k,b') (k',a) [<-|[ ]] Hy; simpl.
 rewrite <-E. apply (AP kb (k',a)); simpl; auto.
Qed.

Lemma ApartL_ltk_l A B B' (lA : klist A) (kb:key*B) (kb':key*B') :
 [kb] < lA -> kb'#1 < kb#1 -> [kb'] < lA.
Proof.
 intros AP LT (k,b') (k',a) [<-|[ ]] Hy; simpl.
 rewrite LT. apply (AP kb (k',a)); simpl; auto.
Qed.

Lemma ApartL_eqk_r A B B' (lA : klist A) (kb:key*B) (kb':key*B') :
 lA < [kb] -> kb#1 == kb'#1 -> lA < [kb'].
Proof.
 intros AP E (k,a) (k',b') Hx [<-|[ ]]; simpl.
 rewrite <-E. apply (AP (k,a) kb); simpl; auto.
Qed.

Lemma ApartL_ltk_r A B B' (lA : klist A) (kb:key*B) (kb':key*B') :
 lA < [kb] -> kb#1 < kb'#1 -> lA < [kb'].
Proof.
 intros AP LT (k,a) (k',b') Hx [<-|[ ]]; simpl.
 rewrite <-LT. apply (AP (k,a) kb); simpl; auto.
Qed.

Lemma sort_app_key (l l' : klist elt) :
 sort O.ltk (l++l') <-> sort O.ltk l /\ sort O.ltk l' /\ l < l'.
Proof.
 apply SortA_app_iff with (eqA:=O.eqk)(ltA:=O.ltk); ok.
Qed.

Lemma sort_cons_key p (l : klist elt) :
 sort O.ltk (p::l) <-> sort O.ltk l /\ [p] < l.
Proof.
 rewrite (sort_app_key [p] l). firstorder.
Qed.

Lemma bindings_above x (e:elt) (m:t elt) :
  m < x <-> bindings m < [(x,e)].
Proof.
 split.
 - intros H p q Hp [<-|[ ]]. simpl. apply H.
   exists (p#2). rewrite <- bindings_spec1.
   apply In_InA; ok. now destruct p.
 - intros H y (v,M).
   rewrite <- bindings_spec1, InA_alt in M.
   destruct M as (p & E & IN). redk. destruct E as (->,->).
   apply (H _ (x,e)); simpl; auto.
Qed.

Lemma bindings_below x (e:elt) (m:t elt) :
  x < m <-> [(x,e)] < bindings m.
Proof.
 split.
 - intros H p q [<-|[ ]] Hq. simpl. apply H.
   exists (q#2). rewrite <- bindings_spec1.
   apply In_InA; ok. now destruct q.
 - intros H y (v,M).
   rewrite <- bindings_spec1, InA_alt in M.
   destruct M as (p & E & IN). redk. destruct E as (->,->).
   apply (H (x,e)); simpl; auto.
Qed.

Lemma bindings_sort (m:t elt) : sort O.ltk (bindings m) <-> Ok m.
Proof.
 split; auto using bindings_spec2.
 induction m as [|c l IHl x v r IHr].
 - unfold bindings. simpl. constructor.
 - rewrite bindings_node; simpl.
   rewrite sort_app_key, sort_cons_key, (@ApartL_consr _ elt). (* TODO *)
   rewrite <- bindings_above, <- bindings_below. intuition; ok.
Qed.

Instance treeify_ok l : sort O.ltk l -> Ok (@treeify elt l).
Proof.
 intros. apply bindings_sort. rewrite treeify_bindings; auto.
Qed.

End Elt.

Definition oelse {A} (o o' : option A) :=
 match o with
 | None => o'
 | _ => o
 end.

Definition obind {A B} (o:option A) (f:A->option B) :=
  match o with Some a => f a | None => None end.

(** [findL] : List assoc based on [K.compare] *)

Fixpoint findL {elt} x (l : klist elt) :=
 match l with
 | [] => None
 | (y,v) :: l =>
   match K.compare x y with
   | Eq => Some v
   | _ => findL x l
   end
 end.

Lemma findL_app {elt} x (l l' : klist elt) :
  findL x (l++l') = oelse (findL x l) (findL x l').
Proof.
 induction l as [|(y,v) l IH]; simpl; auto.
 rewrite IH. destmatch; auto.
Qed.

Lemma findL_inA {elt} x e (l : klist elt) :
 findL x l = Some e -> InA O.eqke (x,e) l.
Proof.
 induction l as [|(k,v) l IH]; simpl; try easy.
 destmatch; intro E; auto. intros [= ->]; auto.
Qed.

Lemma findL_inA_iff {elt} x e (l : klist elt) : sort O.ltk l ->
 (findL x l = Some e <-> InA O.eqke (x,e) l).
Proof.
 intros Sl. split; [apply findL_inA| ]. revert Sl.
 induction l as [|(k,v) l IH]; simpl; try easy.
 inversion_clear 1. rewrite InA_cons. redk. intros [(E,->)|IN].
 - destmatch; intros; auto || order.
 - destmatch; intros; auto.
   assert (LT : O.ltk (k,v) (x,e))
     by (eapply SortA_InfA_InA with (eqA:=O.eqke); ok).
   compute in LT. order.
Qed.

Lemma findL_find {elt} x (m : t elt) `{!Ok m} :
 findL x (bindings m) = find x m.
Proof.
 apply eq_option_alt. intro e.
 rewrite findL_inA_iff by now apply bindings_spec2.
 rewrite find_spec by auto.
 apply bindings_spec1.
Qed.

Section Mapo.
Variable elt elt' : Type.
Variable f : key -> elt -> option elt'.

Lemma mapoL_sorted l acc :
 sort O.ltk (rev l) -> sort O.ltk acc -> l < acc ->
 sort O.ltk (mapoL f l acc).
Proof.
 revert acc.
 induction l as [|(k,e) l IH]; simpl; auto.
 intros acc Sl Sacc AP.
 rewrite sort_app_key in Sl; ok. destruct Sl as (Sl & _ & AP').
 apply -> ApartL_rev in AP'.
 apply -> ApartL_consl in AP. destruct AP as (AP1,AP).
 apply IH; clear IH; simpl; auto; destruct (f k e); simpl; auto.
 - apply sort_cons_key. eauto using ApartL_eqk_l with map.
 - apply ApartL_consr. eauto using ApartL_eqk_r with map.
Qed.

Global Instance mapo_ok m `{!Ok m} : Ok (mapo f m).
Proof.
 unfold mapo. apply treeify_ok. apply mapoL_sorted; simpl; auto.
 - rewrite rev_bindings_rev, rev_involutive. now apply bindings_spec2.
 - inversion 2.
Qed.

Lemma mapoL_find l acc x :
 sort O.ltk (rev l) ->
 exists y : K.t,
    y == x /\
    findL x (mapoL f l acc) =
     oelse (obind (findL x (rev l)) (f y)) (findL x acc).
Proof.
 revert acc.
 induction l as [|(k,e) l IH]; simpl; intros acc Sl.
 - now exists x.
 - rewrite sort_app_key in Sl. destruct Sl as (Sl & _ & AP).
   apply -> ApartL_rev in AP.
   destruct (IH (ocons k (f k e) acc) Sl) as (y & Hy & E). clear IH.
   setoid_rewrite findL_app. setoid_rewrite E. clear E.
   destruct (findL x (rev l)) eqn:El; simpl in *; auto.
   + exists y; split; auto.
     unfold oelse, ocons; destmatch; auto. simpl.
     destmatch; auto; intros.
     apply findL_inA in El. rewrite InA_rev in El. apply InA_alt in El.
     destruct El as ((x',e') & (Hx',_) & IN).
     compute in Hx'.
     enough (x' < k) by order.
     apply (AP (x',e') (k,e)); simpl; auto.
   + clear l Sl AP El.
     destruct (f k e) eqn:Fk; simpl; destmatch; intros; firstorder;
      exists k; simpl; now rewrite Fk.
Qed.

Lemma mapoL_mapsto l acc x v' :
 InA O.eqke (x,v') (mapoL f l acc) <->
 (exists y v, y == x /\ List.In (y,v) l /\ f y v = Some v') \/
  InA O.eqke (x,v') acc.
Proof.
 revert acc.
 induction l as [|(k,e) l IH]; simpl; intros.
 - firstorder.
 - destruct (f k e) eqn:Hf; simpl in *; rewrite IH; clear IH; auto.
   rewrite ?InA_cons.
   + firstorder; try red in H; try red in H0; simpl in *; subst.
     * left. exists k, e; autom.
     * injection H0 as <- <-. right; left. compute; split; autom.
       congruence.
   + firstorder. injection H0 as <- <-. congruence.
Qed.

Lemma mapo_mapsto m x v' :
  (mapo f m)@x ↦ v' ->
   exists y v, y == x /\ m@x ↦ v /\ f y v = Some v'.
Proof.
 unfold mapo.
 rewrite treeify_mapsto, mapoL_mapsto, InA_nil; auto.
 intros [(y & v & E & IN & Hf)|[ ]].
 rewrite rev_bindings_rev, <-In_rev in IN.
 exists y, v. repeat split; auto. apply bindings_spec1.
 rewrite InA_alt. exists (y, v). split; autom.
Qed.

Lemma mapo_find m x `{!Ok m} :
  exists y, y == x /\
            find x (mapo f m) = obind (find x m) (f y).
Proof.
 assert (Ok (mapo f m)) by ok.
 destruct (@mapoL_find (rev_bindings m) nil x) as (y & Hy & EQ).
 - rewrite rev_bindings_rev, rev_involutive; now apply bindings_spec2.
 - exists y; split; auto.
   unfold mapo in *. rewrite <- !findL_find; auto.
   rewrite treeify_bindings, EQ. simpl. clear EQ.
   rewrite rev_bindings_rev, rev_involutive. now destruct obind.
Qed.

End Mapo.

Section Merge.
Variable elt elt' elt'' : Type.
Implicit Type f : key -> option elt -> option elt' -> option elt''.

Lemma mergeL_eqn f l l' acc k k' v v' :
 mergeL f ((k,v)::l) ((k',v')::l') acc =
 match K.compare k k' with
 | Eq => mergeL f l l' (ocons k (f k (Some v) (Some v')) acc)
 | Lt => mergeL f ((k,v)::l) l' (ocons k' (f k' None (Some v')) acc)
 | Gt => mergeL f l ((k',v')::l') (ocons k (f k (Some v) None) acc)
 end.
Proof.
 reflexivity.
Qed.

Lemma mergeL_sorted f l l' acc :
 sort O.ltk (rev l) -> sort O.ltk (rev l') -> sort O.ltk acc ->
 l < acc -> l' < acc ->
 sort O.ltk (mergeL f l l' acc).
Proof.
 revert l' acc.
 induction l as [|(x,e) l IHl].
 - simpl. intros. apply mapoL_sorted; auto.
 - induction l' as [|(x',e') l' IHl'].
   + intros. apply mapoL_sorted; auto.
   + intros acc Sl Sl' Sacc AP AP'. simpl in Sl, Sl'.
     assert (Sl0 := Sl). assert (Sl0' := Sl').
     assert (AP0 := AP). assert (AP0' := AP').
     apply sort_app_key in Sl. destruct Sl as (Sl & _ & APl).
     apply sort_app_key in Sl'. destruct Sl' as (Sl' & _ & APl').
     apply -> ApartL_rev in APl. apply -> ApartL_rev in APl'.
     apply -> ApartL_consl in AP. destruct AP as (AP1,AP).
     apply -> ApartL_consl in AP'. destruct AP' as (AP1',AP').
     rewrite mergeL_eqn; destmatch; [intro EQ|intro LT|intro LT];
      apply IHl || apply IHl'; clear IHl IHl'; auto;
      destruct f; simpl; auto; try apply sort_cons_key;
       try apply ApartL_consr; try apply ApartL_consl; split; auto;
       eauto using ApartL_eqk_l, ApartL_eqk_r with map;
       apply ApartL_consl; split; try (eapply ApartL_ltk_r; eautom; fail);
       intros (?,?) (?,?); compute; intuition congruence.
Qed.

Global Instance merge_ok f m m' `{!Ok m, !Ok m'} : Ok (merge f m m').
Proof.
apply treeify_ok, mergeL_sorted; auto;
 rewrite ?rev_bindings_rev, ?rev_involutive;
 now apply bindings_sort || firstorder.
Qed.

Lemma mergeL_in f l l' acc x :
 (exists v, InA O.eqke (x,v) (mergeL f l l' acc)) ->
    (exists v, InA O.eqke (x,v) l) \/
    (exists v, InA O.eqke (x,v) l') \/
    (exists v, InA O.eqke (x,v) acc).
Proof.
 revert l' acc.
 induction l as [|(y,e) l IHl].
 - simpl. intros l' acc (v,H). right.
   apply mapoL_mapsto in H.
   destruct H as [(y & v' & E & IN & _)|H].
   + left; exists v'. rewrite InA_alt. exists (y,v'); split; autom.
   + firstorder.
 - induction l' as [|(y',e') l' IHl']; intros acc.
   + intros (v,H). apply mapoL_mapsto in H; simpl in *.
     destruct H as [(y' & v' & E & [[= <- <-]|IN] & _)|H].
     * left. exists e; eautom.
     * left. exists v'. rewrite InA_cons. right. rewrite InA_alt.
       exists (y',v'); autom.
     * firstorder.
   + rewrite mergeL_eqn.
     destmatch; [intros EQ H| intros LT H|intros LT H];
      apply IHl in H || apply IHl' in H; clear IHl IHl'; firstorder;
       setoid_rewrite InA_cons; firstorder;
       destruct f; simpl in *; firstorder;
       rewrite InA_cons in H; destruct H as [(H,_)|H]; firstorder;
       compute in H.
     * left; exists e. now left.
     * right;left; exists e'. now left.
     * left; exists e. now left.
Qed.

Lemma merge_spec2' f m m' x :
  x ∈ (merge f m m') -> x ∈ m \/ x ∈ m'.
Proof.
 unfold merge, "∈".
 setoid_rewrite treeify_mapsto.
 intros H. apply mergeL_in in H. destruct H as [(v,H)|[(v,H)|(v,H)]].
 - left. exists v. rewrite rev_bindings_rev, InA_rev in H.
   now apply bindings_spec1.
 - right. exists v. rewrite rev_bindings_rev, InA_rev in H.
   now apply bindings_spec1.
 - now rewrite InA_nil in H.
Qed.

Lemma merge_spec2 f m m' x `{!Ok m, !Ok m'} :
  x ∈ (merge f m m') -> x ∈ m \/ x ∈ m'.
Proof. apply merge_spec2'. Qed.

Ltac breako :=
 destmatch; auto; try order;
 unfold oelse, ocons; destmatch; simpl; auto;
  destmatch; auto; order.

Lemma merge_find_eq f l l' acc x y y' z e e' :
  (forall k : key, f k None None = None) ->
  l < [(y, e)] ->
  l' < [(y', e')] ->
  y == y' -> z == x ->
  exists y0 : K.t,
    y0 == x /\
    oelse (f z (findL x l) (findL x l'))
      (findL x (ocons y (f y (Some e) (Some e')) acc)) =
    oelse
      (f y0 (findL x (l ++ [(y, e)])) (findL x (l' ++ [(y', e')])))
      (findL x acc).
Proof.
 intros Hf AP AP' Ey Ez. simpl.
 setoid_rewrite findL_app; simpl.
 destruct findL eqn:INl.
 - exists z; split; auto.
   assert (x < y).
   { apply findL_inA in INl. apply InA_alt in INl.
     destruct INl as ((x',e0') & (Hx',_) & INl).
     compute in Hx'. rewrite Hx'.
     apply (AP (x',e0') (y,e)); simpl; auto. }
   destruct (findL x l'); simpl; breako.
 - clear INl. simpl.
   destruct (findL x l') eqn:INl'; simpl.
   + exists z; split; auto.
     enough (x < y') by breako.
     { apply findL_inA in INl'. apply InA_alt in INl'.
       destruct INl' as ((x',e0') & (Hx',_) & INl').
       compute in Hx'. rewrite Hx'.
       apply (AP' (x',e0') (y',e')); simpl; auto. }
   + clear INl'. rewrite Hf. simpl.
     destruct (f y _ _) eqn:Fy; simpl;
       destmatch; try order;
        try setoid_rewrite Hf; firstorder;
         exists y; now rewrite Fy.
Qed.

Lemma merge_find_lt f l l' acc x y y' z e e' :
  (forall k : key, f k None None = None) ->
  l < [(y, e)] ->
  l' < [(y', e')] ->
  y < y' -> z == x ->
  exists y0 : K.t,
    y0 == x /\
    oelse (f z (findL x (l++[(y,e)])) (findL x l'))
      (findL x (ocons y' (f y' None (Some e')) acc)) =
    oelse
      (f y0 (findL x (l++[(y, e)])) (findL x (l'++[(y', e')])))
      (findL x acc).
Proof.
 intros Hf AP AP' Ey Ez. simpl.
 destruct findL eqn:INl.
 - exists z; split; auto.
   assert (x < y').
   { apply findL_inA in INl. apply InA_alt in INl.
     destruct INl as ((x',e0') & (Hx',_) & INl).
     compute in Hx'. rewrite Hx'.
     rewrite in_app_iff in INl. destruct INl.
     - rewrite <- Ey. apply (AP (x',e0') (y,e)); simpl; auto.
     - simpl in H. destruct H as [[= <- _]|[  ]]; auto. }
   setoid_rewrite findL_app.
   destruct (findL x l'); simpl; breako.
 - clear INl.
   setoid_rewrite findL_app.
   destruct (findL x l') eqn:INl'; simpl.
   + exists z; split; auto.
     enough (x < y') by breako.
     { apply findL_inA in INl'. apply InA_alt in INl'.
       destruct INl' as ((x',e0') & (Hx',_) & INl').
       compute in Hx'. rewrite Hx'.
       apply (AP' (x',e0') (y',e')); simpl; auto. }
   + clear INl'. rewrite Hf. simpl.
     destruct (f y' _ _) eqn:Fy'; simpl;
      destmatch; try setoid_rewrite Hf; firstorder;
        exists y'; now rewrite Fy'.
Qed.

Lemma merge_find_gt f l l' acc x y y' z e e' :
  (forall k : key, f k None None = None) ->
  l < [(y, e)] ->
  l' < [(y', e')] ->
  y' < y -> z == x ->
  exists y0 : K.t,
    y0 == x /\
    oelse (f z (findL x l) (findL x (l' ++ [(y',e')])))
      (findL x (ocons y (f y (Some e) None) acc)) =
    oelse
      (f y0 (findL x (l ++ [(y, e)])) (findL x (l' ++ [(y', e')])))
      (findL x acc).
Proof.
 intros Hf AP AP' Ey Ez.
 simpl. setoid_rewrite (findL_app x l).
 destruct findL eqn:INl.
 - exists z; split; auto.
   assert (x < y).
   { apply findL_inA in INl. apply InA_alt in INl.
     destruct INl as ((x',e0') & (Hx',_) & INl).
     compute in Hx'. rewrite Hx'.
     apply (AP (x',e0') (y,e)); simpl; auto. }
   destruct (findL x (l' ++ _)); simpl; breako.
 - clear INl.
   destruct (findL x (l' ++ _)) eqn:INl'; simpl.
   + exists z; split; auto.
     enough (x < y) by breako.
     { apply findL_inA in INl'. apply InA_alt in INl'.
       destruct INl' as ((x',e0') & (Hx',_) & INl').
       compute in Hx'. rewrite Hx'.
       rewrite in_app_iff in INl'. simpl in *. destruct INl'.
       - rewrite <- Ey. apply (AP' (x',e0') (y',e')); simpl; auto.
       - destruct H as [[= <- _]|[  ]]; auto. }
   + clear INl'. rewrite Hf. simpl.
     destruct (f y _ _) eqn:Fy; simpl;
      destmatch; try setoid_rewrite Hf; firstorder;
        exists y; now rewrite Fy.
Qed.

Lemma mergeL_find f l l' acc x :
 (forall k, f k None None = None) ->
 sort O.ltk (rev l) ->
 sort O.ltk (rev l') ->
 exists y, y == x /\
  findL x (mergeL f l l' acc) =
  oelse (f y (findL x (rev l)) (findL x (rev l'))) (findL x acc).
Proof.
 intros Hf.
 revert l' acc.
 induction l as [|(y,e) l IHl].
 - simpl. intros l' acc _ Sl'.
   destruct (@mapoL_find _ _ (fun k v' => f k None (Some v')) l' acc x Sl')
     as (y & Hy & EQ).
   exists y; split; auto; rewrite EQ; clear EQ.
   destruct findL; simpl; rewrite ?Hf; auto.
 - induction l' as [|(y',e') l' IHl'].
   + intros acc Sl _. clear IHl.
     destruct (@mapoL_find _ _ (fun k v => f k (Some v) None) _ acc x Sl)
       as (z & Hz & EQ).
     exists z; split; auto. cbn - [mapoL]. rewrite EQ; clear EQ.
     simpl. destruct findL; simpl; rewrite ?Hf; auto.
   + intros acc Sl Sl'.
     simpl in Sl, Sl'.
     assert (Sl0 := Sl). assert (Sl0' := Sl').
     rewrite sort_app_key in Sl, Sl'.
     destruct Sl as (Sl & _ & AP). destruct Sl' as (Sl' & _ & AP').
     rewrite mergeL_eqn. destmatch; [intro EQ | intro LT | intro LT];
      set (acc' := ocons _ _ _).
     * destruct (IHl l' acc') as (z & Hz & E); auto.
       rewrite E. apply merge_find_eq; auto.
     * destruct (IHl' acc') as (z & Hz & E); auto.
       setoid_rewrite E. apply merge_find_lt; auto.
     * destruct (IHl ((y',e')::l') acc') as (z & Hz & E); auto.
       setoid_rewrite E. apply merge_find_gt; auto.
Qed.

Lemma merge_spec1n f m m' x `{!Ok m, !Ok m'} :
 (forall k, f k None None = None) ->
 exists y, y == x /\
           find x (merge f m m') = f y (find x m) (find x m').
Proof.
 intros Hf.
 assert (Ok (merge f m m')) by ok.
 destruct (@mergeL_find f (rev_bindings m) (rev_bindings m') nil x)
   as (y & Hy & EQ); auto.
 - rewrite rev_bindings_rev, rev_involutive; now apply bindings_sort.
 - rewrite rev_bindings_rev, rev_involutive; now apply bindings_sort.
 - exists y; split; auto.
   unfold merge in *. rewrite <- !findL_find; auto.
   rewrite treeify_bindings, EQ. simpl. clear EQ.
   rewrite rev_bindings_rev, rev_involutive.
   rewrite rev_bindings_rev, rev_involutive.
   now destruct f.
Qed.

Lemma merge_spec1 f m m' x `{!Ok m, !Ok m'} :
 (x ∈ m \/ x ∈ m') ->
 exists y, y == x /\
           find x (merge f m m') = f y (find x m) (find x m').
Proof.
 set (g := fun x o o' => match o,o' with None, None => None
                                        | _,_ => f x o o' end).
 destruct (@merge_spec1n g m m' x) as (y & Hy & EQ); auto.
 change (merge f) with (merge g).
 exists y; split; auto. rewrite EQ.
 destruct (find x m) eqn:F; simpl; auto.
 destruct (find x m') eqn:F'; simpl; auto.
 rewrite not_find_iff in F, F'; intuition.
Qed.

End Merge.

(** ** Filtering *)

Section Filter.
Variable elt : Type.
Implicit Types f : key -> elt -> bool.

Fixpoint filter_aux f m acc :=
 match m with
 | Leaf => acc
 | Node _ l k v r =>
   let acc := filter_aux f r acc in
   if f k v then filter_aux f l ((k,v)::acc)
   else filter_aux f l acc
 end.

Definition filter f m := treeify (filter_aux f m nil).

Fixpoint partition_aux f m acc1 acc2 :=
 match m with
 | Leaf => (acc1,acc2)
 | Node _ l k v r =>
   let (acc1, acc2) := partition_aux f r acc1 acc2 in
   if f k v then partition_aux f l ((k,v)::acc1) acc2
   else partition_aux f l acc1 ((k,v)::acc2)
 end.

Definition partition f m :=
  let (l1,l2) := partition_aux f m nil nil in
  (treeify l1, treeify l2).

(** ** Filter *)

Lemma filter_aux_bindings f m acc :
 filter_aux f m acc = List.filter (fun '(k,e) => f k e) (bindings m) ++ acc.
Proof.
 revert acc.
 induction m as [|c l IHl x v r IHr]; trivial.
 intros acc.
 rewrite <- (List.app_nil_r (bindings _)).
 rewrite bindings_node, !filter_app. simpl. rewrite List.app_nil_r.
 destruct (f x v); now rewrite IHl, IHr, app_ass.
Qed.

Lemma filter_spec0 f m :
 bindings (filter f m) = List.filter (fun '(k,e) => f k e) (bindings m).
Proof.
 unfold filter.
 now rewrite treeify_bindings, filter_aux_bindings, app_nil_r.
Qed.

Lemma filter_spec f m `{!Ok m} :
 bindings (filter f m) = List.filter (fun '(k,e) => f k e) (bindings m).
Proof.
 unfold filter.
 now rewrite treeify_bindings, filter_aux_bindings, app_nil_r.
Qed.

Global Instance filter_ok f m `(!Ok m) : Ok (filter f m).
Proof.
 apply bindings_sort.
 rewrite filter_spec0.
 apply filter_sort with O.eqk; ok. now apply bindings_sort.
Qed.

Lemma filter_mapsto f m (Hf : Proper (K.eq==>eq==>eq) f) k v :
 MapsTo k v (filter f m) <-> MapsTo k v m /\ f k v = true.
Proof.
 rewrite <- bindings_spec1, filter_spec0, filter_InA, bindings_spec1.
 easy.
 intros (?,?) (?,?) (?,?); now apply Hf.
Qed.


(** ** Partition *)

Lemma partition_aux_spec f m acc1 acc2 :
 partition_aux f m acc1 acc2 =
  (filter_aux f m acc1, filter_aux (fun k e => negb (f k e)) m acc2).
Proof.
 revert acc1 acc2.
 induction m as [ | c l Hl x e r Hr ]; simpl.
 - trivial.
 - intros acc1 acc2.
   destruct (f x e); simpl; now rewrite Hr, Hl.
Qed.

Lemma partition_alt f m :
 partition f m = (filter f m, filter (fun k e => negb (f k e)) m).
Proof.
 unfold partition, filter. now rewrite partition_aux_spec.
Qed.

Lemma partition_spec1 f m :
 Proper (K.eq==>eq==>eq) f ->
 Equal (fst (partition f m)) (filter f m).
Proof. now rewrite partition_alt. Qed.

Lemma partition_spec2 f m :
 Proper (K.eq==>eq==>eq) f ->
 Equal (snd (partition f m)) (filter (fun k e => negb (f k e)) m).
Proof. now rewrite partition_alt. Qed.

Instance partition_ok1 f m `(!Ok m) : Ok (fst (partition f m)).
Proof. rewrite partition_alt; now apply filter_ok. Qed.

Instance partition_ok2 f m `(!Ok m) : Ok (snd (partition f m)).
Proof. rewrite partition_alt; now apply filter_ok. Qed.

Lemma partition_spec f m `{!Ok m} :
 prodmap (@bindings _) (partition f m) =
 List.partition (fun '(k,e) => f k e) (bindings m).
Proof.
 rewrite partition_alt, partition_filter. unfold prodmap. f_equal.
 - now apply filter_spec.
 - rewrite filter_spec; auto. f_equiv. now intros (k,e) ? <-.
Qed.

End Filter.
End MakeRaw.

(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we
   need to encapsulate everything into a type of binary search trees. *)

Module Make (K: OrderedType) <: Interface.S K.
 Module Raw := MakeRaw K.
 Include Raw.Pack K Raw.
End Make.
