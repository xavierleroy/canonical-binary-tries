
(** * Finite Modular Maps : Raw Interface *)

(** Author : Pierre Letouzey (Université de Paris - INRIA),
    adapted from earlier works in Coq Standard Library, see README.md.
    Licence : LGPL 2.1, see file LICENSE. *)

(** This "raw" interface isn't meant for general use, see rather the
    [Interface] file for that. The "raw" version has two interests :

    - Internally, as an intermediate step during the implementations
      [WeakList] [OrdList], [AVL] and [RBT] proposed in this library.
      Actually, only the [Positive] implementation does not use it.

    - For advanced users, access to a "raw" map datatype allows
      smaller memory footprint during Coq computations (no proof
      parts) and hence slightly faster operations, at the expense of
      more complex reasoning when proving properties later.

    Raw means here that no proof part is stored along the map
    datatypes, while the type of maps used here is too large to be
    directly a implementation of [Interface.S] : among all inhabitants
    of this type of maps, only the ones fulfilling some adequacy
    predicate [Ok] should be considered (think for instance of lists
    that are sorted or trees that are binary search trees). Almost all
    operations here will have [Ok] pre-conditions, and all operations
    answering new maps will maintain this adequacy.

    A implementation of the usual [Interface.S] can then be obtained
    by restricting the type of maps, and then wrapping all operations.
    In functors [WPack] and [Pack] below, this is done via a record
    combining a map and a adequacy proof. These functors are used as
    the final steps in [OrdList], [AVL] and [RBT].

    See [Interface] for the documentation of all these operations and
    extra explanations. *)

From Tries.MMaps Require Export Comparisons Interface.
Set Implicit Arguments.
Unset Strict Implicit.
(* No induction principles for the records below *)
Local Unset Elimination Schemes.

Definition Cmp {elt:Type}(cmp:elt->elt->bool) e1 e2 := cmp e1 e2 = true.

Module Type WS (K : DecidableType).

  Definition key := K.t.

  Definition eq_key {elt} (p p':key*elt) := K.eq (fst p) (fst p').

  Definition eq_key_elt {elt} (p p':key*elt) :=
      K.eq (fst p) (fst p') /\ (snd p) = (snd p').

  Parameter t : Type -> Type.
  (** the abstract type of maps *)

  (** Is a set well-formed or ill-formed ? *)

  Parameter IsOk : forall {elt}, t elt -> Prop.
  Class Ok {elt}(m:t elt) : Prop := ok : IsOk m.

  (** In order to be able to validate (at least some) particular maps as
      well-formed, we ask for a boolean function for (semi-)deciding
      predicate [Ok]. If [Ok] isn't decidable, [isok] may be the
      always-false function. *)
  Parameter isok : forall {elt}, t elt -> bool.
  Parameter isok_Ok : forall {elt} (m:t elt), isok m = true -> Ok m.

  Section Ops.
  Parameter empty : forall {elt}, t elt.
  Variable elt:Type.
  Parameter is_empty : t elt -> bool.
  Parameter find : key -> t elt -> option elt.
  Parameter singleton : key -> elt -> t elt.
  Parameter add : key -> elt -> t elt -> t elt.
  Parameter remove : key -> t elt -> t elt.
  Parameter mem : key -> t elt -> bool.
  Parameter bindings : t elt -> list (key*elt).
  Parameter cardinal : t elt -> nat.
  Parameter fold : forall A: Type, (key -> elt -> A -> A) -> t elt -> A -> A.
  Parameter equal : (elt -> elt -> bool) -> t elt -> t elt -> bool.
  Parameter filter : (key -> elt -> bool) -> t elt -> t elt.
  Parameter partition : (key -> elt -> bool) -> t elt -> t elt * t elt.
  Parameter for_all : (key -> elt -> bool) -> t elt -> bool.
  Parameter exists_ : (key -> elt -> bool) -> t elt -> bool.
  Variable elt' elt'' : Type.
  Parameter map : (elt -> elt') -> t elt -> t elt'.
  Parameter mapi : (key -> elt -> elt') -> t elt -> t elt'.
  Parameter merge : (key -> option elt -> option elt' -> option elt'') ->
                      t elt -> t elt' ->  t elt''.
  End Ops.

  Declare Instance empty_ok {elt} : Ok (@empty elt).
  Declare Instance singleton_ok {elt} x (e:elt) : Ok (singleton x e).
  Declare Instance add_ok {elt} (m:t elt) x e `(!Ok m) :
    Ok (add x e m).
  Declare Instance remove_ok {elt} (m:t elt) x `(!Ok m) :
    Ok (remove x m).
  Declare Instance filter_ok {elt} f (m:t elt) `(!Ok m) :
    Ok (filter f m).
  Declare Instance partition_ok1 {elt} f (m:t elt) `(!Ok m) :
    Ok (fst (partition f m)).
  Declare Instance partition_ok2 {elt} f (m:t elt) `(!Ok m) :
    Ok (snd (partition f m)).
  Declare Instance map_ok {elt elt'}(f:elt->elt') m `(!Ok m) :
    Ok (map f m).
  Declare Instance mapi_ok {elt elt'}(f:key->elt->elt') m `(!Ok m) :
    Ok (mapi f m).
  Declare Instance merge_ok {elt elt' elt''}
    (f:key -> option elt -> option elt' -> option elt'') m m'
    `(!Ok m, !Ok m') :
    Ok (merge f m m').

  Parameter MapsTo : forall {elt}, key -> elt -> t elt -> Prop.
  Definition In {elt}(k:key)(m: t elt) : Prop := exists e, MapsTo k e m.

  Section Specs.
  Context {elt elt' elt'' : Type}.
  Global Declare Instance MapsTo_compat :
      Proper (K.eq==>Logic.eq==>Logic.eq==>iff) (@MapsTo elt).

  Variable m m' : t elt.
  Variable x y : key.
  Variable e : elt.
  Parameter find_spec : forall `{!Ok m},
     find x m = Some e <-> MapsTo x e m.
  Parameter mem_spec : forall `{!Ok m}, mem x m = true <-> In x m.
  Parameter empty_spec : find x (@empty elt) = None.
  Parameter is_empty_spec :
     is_empty m = true <-> forall x, find x m = None.
  Parameter add_spec1 : forall `{!Ok m}, find x (add x e m) = Some e.
  Parameter add_spec2 : forall `{!Ok m},
    ~K.eq x y -> find y (add x e m) = find y m.
  Parameter remove_spec1 : forall `{!Ok m}, find x (remove x m) = None.
  Parameter remove_spec2 : forall `{!Ok m},
    ~K.eq x y -> find y (remove x m) = find y m.
  Parameter bindings_spec1 :
    InA eq_key_elt (x,e) (bindings m) <-> MapsTo x e m.
  Parameter bindings_spec2w : forall `{!Ok m},
    NoDupA eq_key (bindings m).
  Parameter singleton_spec : bindings (singleton x e) = (x,e)::nil.
  Parameter cardinal_spec : cardinal m = length (bindings m).
  Parameter fold_spec :
    forall {A} (i : A) (f : key -> elt -> A -> A),
    fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.

  Parameter filter_spec : forall (f:key->elt->bool) m `{!Ok m},
   bindings (filter f m) = List.filter (fun '(k,e) => f k e) (bindings m).
  Parameter partition_spec : forall (f:key->elt->bool) m `{!Ok m},
   prodmap (@bindings _) (partition f m) =
    List.partition (fun '(k,e) => f k e) (bindings m).
  Parameter for_all_spec : forall (f:key->elt->bool) m,
   for_all f m = List.forallb (fun '(k,e) => f k e) (bindings m).
  Parameter exists_spec : forall (f:key->elt->bool) m,
   exists_ f m = List.existsb (fun '(k,e) => f k e) (bindings m).

  Definition Equal (m m':t elt) := forall y, find y m = find y m'.
  Definition Eqdom (m m':t elt) := forall y, In y m <-> In y m'.
  Definition Equiv (R:elt->elt->Prop) m m' :=
   Eqdom m m' /\ (forall k e e', MapsTo k e m -> MapsTo k e' m' -> R e e').
  Definition Equivb (cmp: elt->elt->bool) := Equiv (Cmp cmp).

  Parameter equal_spec :
   forall (cmp : elt -> elt -> bool) m m' `{!Ok m, !Ok m'},
    equal cmp m m' = true <-> Equivb cmp m m'.

  Parameter map_spec : forall (f:elt->elt') m,
    bindings (map f m) = List.map (fun '(k,e) => (k,f e)) (bindings m).
  Parameter mapi_spec : forall (f:key->elt->elt') m,
    bindings (mapi f m) = List.map (fun '(k,e) => (k,f k e)) (bindings m).

  Implicit Types f : key->option elt->option elt'->option elt''.

  Parameter merge_spec1 :
   forall f m m' x `{!Ok m, !Ok m'},
     In x m \/ In x m' ->
     exists y:key, K.eq y x /\
                   find x (merge f m m') = f y (find x m) (find x m').

  Parameter merge_spec2 :
    forall f m m' x `{!Ok m, !Ok m'},
      In x (merge f m m') -> In x m \/ In x m'.

  End Specs.
End WS.

(** ** Raw Maps on ordered keys. *)

Module Type S (K : OrderedType).
  Include WS K.

  Definition lt_key {elt} (p p':key*elt) := K.lt (fst p) (fst p').

  Parameter bindings_spec2 :
    forall {elt}(m : t elt)`{!Ok m}, sort lt_key (bindings m).

  Parameter compare :
    forall {elt}, (elt -> elt -> comparison) -> t elt -> t elt -> comparison.

  Parameter compare_spec :
    forall {elt} (cmp : elt -> elt -> comparison)(m m':t elt)`{!Ok m, !Ok m'},
      compare cmp m m' =
      list_compare (pair_compare K.compare cmp) (bindings m) (bindings m').

End S.

(** ** From Raw.WS to Interface.WS

    A record packs the datatype and the adequacy proof.
    The rest is a wrapper around the raw functions. *)

Module WPack (K : DecidableType) (R : WS K) <: Interface.WS K.
 Import R. (** The raw datatype for maps *)
 Definition key := K.t.

 (** The map structure with adequacy proofs attached *)

 Record t_ (elt:Type) := Mkt {this :> R.t elt; ok : Ok this}.
 Definition t := t_.

 Existing Instance ok.
 Arguments Mkt {elt} this {ok}.

 (** By default, the adequacy proof attached to a map [m] will have
     a size proportional to the number of operations used
     to build this map (one extra [add_ok] for each [add] operation,
     etc). If we have a proof [b : isok m = true], then the
     following function [Mkt_bool] builds a map with proof part
     [@isok_Ok m b]. When [b] is obtained by computation, this
     leads to a constant-size proof part (assuming that all occurrences
     of [m] are properly shared in memory). This is a typical
     time/memory trade-off. *)

 Definition Mkt_bool {elt} (m : R.t elt)(b : isok m = true) : t elt :=
  @Mkt _ m (isok_Ok b).

 Section Elt.
 Context {elt elt' elt'': Type}.

 Implicit Types m : t elt.
 Implicit Types x y : key.
 Implicit Types e : elt.

 Definition empty : t elt := Mkt (@empty elt).
 Definition is_empty m : bool := is_empty m.
 Definition singleton x e : t elt := Mkt (singleton x e).
 Definition add x e m : t elt := Mkt (add x e m).
 Definition remove x m : t elt := Mkt (remove x m).
 Definition mem x m : bool := mem x m.
 Definition find x m : option elt := find x m.
 Definition map f m : t elt' := Mkt (map f m).
 Definition mapi (f:key->elt->elt') m : t elt' := Mkt (mapi f m).
 Definition merge f m (m':t elt') : t elt'' := Mkt (merge f m m').
 Definition bindings m : list (key*elt) := bindings m.
 Definition cardinal m := cardinal m.
 Definition fold {A} (f:key->elt->A->A) m i := fold f m i.
 Definition equal cmp m m' : bool := equal cmp m m'.
 Definition filter (f:key->elt->bool) m := Mkt (filter f m).
 Definition partition (f:key->elt->bool) m :=
   let p := partition f m in (Mkt (fst p), Mkt (snd p)).
 Definition for_all (f:key->elt->bool) m : bool := for_all f m.
 Definition exists_ (f:key->elt->bool) m : bool := exists_ f m.

 Definition MapsTo x e m : Prop := MapsTo x e m.
 Definition In x m : Prop := In x m.

 Definition eq_key {elt} (p p':key*elt) := K.eq (fst p) (fst p').

 Definition eq_key_elt {elt} (p p':key*elt) :=
  K.eq (fst p) (fst p') /\ (snd p) = (snd p').

 Instance MapsTo_compat :
   Proper (K.eq==>Logic.eq==>Logic.eq==>iff) MapsTo.
 Proof.
  intros k k' Hk e e' <- m m' <-. unfold MapsTo; simpl. now rewrite Hk.
 Qed.

 Lemma find_spec m x e : find x m = Some e <-> MapsTo x e m.
 Proof. apply find_spec, ok. Qed.

 Lemma mem_spec m x : mem x m = true <-> In x m.
 Proof. apply mem_spec, ok. Qed.

 Lemma empty_spec x : find x empty = None.
 Proof. apply empty_spec. Qed.

 Lemma is_empty_spec m : is_empty m = true <-> forall x, find x m = None.
 Proof. apply is_empty_spec. Qed.

 Lemma add_spec1 m x e : find x (add x e m) = Some e.
 Proof. apply add_spec1, ok. Qed.
 Lemma add_spec2 m x y e : ~ K.eq x y -> find y (add x e m) = find y m.
 Proof. apply add_spec2, ok. Qed.

 Lemma remove_spec1 m x : find x (remove x m) = None.
 Proof. apply remove_spec1, ok. Qed.
 Lemma remove_spec2 m x y : ~K.eq x y -> find y (remove x m) = find y m.
 Proof. apply remove_spec2, ok. Qed.

 Lemma bindings_spec1 m x e :
   InA eq_key_elt (x,e) (bindings m) <-> MapsTo x e m.
 Proof. apply bindings_spec1. Qed.

 Lemma bindings_spec2w m : NoDupA eq_key (bindings m).
 Proof. apply bindings_spec2w, ok. Qed.

 Lemma cardinal_spec m : cardinal m = length (bindings m).
 Proof. apply cardinal_spec. Qed.

 Lemma singleton_spec x e : bindings (singleton x e) = (x,e)::nil.
 Proof. apply singleton_spec. Qed.

 Lemma fold_spec m {A} (i : A) (f : key -> elt -> A -> A) :
   fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.
 Proof. apply fold_spec. Qed.

 Lemma filter_spec (f:key->elt->bool) m :
   bindings (filter f m) = List.filter (fun '(k,e) => f k e) (bindings m).
 Proof. apply filter_spec, ok. Qed.
 Lemma partition_spec (f:key->elt->bool) m :
   prodmap bindings (partition f m) =
    List.partition (fun '(k,e) => f k e) (bindings m).
 Proof.
 unfold bindings. rewrite <- partition_spec by apply ok.
 unfold partition; simpl. now destruct R.partition.
 Qed.
 Lemma for_all_spec (f:key->elt->bool) m :
   for_all f m = List.forallb (fun '(k,e) => f k e) (bindings m).
 Proof. apply for_all_spec. Qed.
 Lemma exists_spec (f:key->elt->bool) m :
   exists_ f m = List.existsb (fun '(k,e) => f k e) (bindings m).
 Proof. apply exists_spec. Qed.

 Definition Equal m m' := forall y, find y m = find y m'.
 Definition Eqdom (m m':t elt) := forall y, In y m <-> In y m'.
 Definition Equiv (R:elt->elt->Prop) m m' :=
  Eqdom m m' /\ (forall k e e', MapsTo k e m -> MapsTo k e' m' -> R e e').
 Definition Equivb cmp := Equiv (Cmp cmp).

 Lemma Equivb_Equivb cmp m m' :
  Equivb cmp m m' <-> R.Equivb cmp m m'.
 Proof.
 unfold Equivb, Equiv, R.Equivb, R.Equiv. intuition.
 Qed.

 Lemma equal_spec cmp m m' :
   equal cmp m m' = true <-> Equivb cmp m m'.
 Proof. rewrite Equivb_Equivb. apply equal_spec; apply ok. Qed.

 End Elt.

 Lemma map_spec {elt elt'} (f:elt->elt') m :
   bindings (map f m) = List.map (fun '(k,e) => (k,f e)) (bindings m).
 Proof. apply map_spec. Qed.

 Lemma mapi_spec {elt elt'} (f:key->elt->elt') m :
   bindings (mapi f m) = List.map (fun '(k,e) => (k,f k e)) (bindings m).
 Proof. apply mapi_spec. Qed.

 Lemma merge_spec1 {elt elt' elt''}
       (f:key->option elt->option elt'->option elt'') m m' x :
   In x m \/ In x m' ->
   exists y:key, K.eq y x /\
                 find x (merge f m m') = f y (find x m) (find x m').
 Proof. apply merge_spec1; apply ok. Qed.

 Lemma merge_spec2 {elt elt' elt''}
       (f:key -> option elt->option elt'->option elt'') m m' x :
   In x (merge f m m') -> In x m \/ In x m'.
 Proof. apply merge_spec2; apply ok. Qed.

End WPack.

Module Pack (K : OrderedType) (R : S K) <: Interface.S K.
 Include WPack K R.

 Definition lt_key {elt} (p p':key*elt) := K.lt (fst p) (fst p').

 Lemma bindings_spec2 {elt}(m : t elt) : sort lt_key (bindings m).
 Proof. apply R.bindings_spec2. Qed.

 Definition compare {elt} cmp (m m' : t elt) := R.compare cmp m m'.

 Lemma compare_spec {elt} cmp (m m' : t elt) :
   compare cmp m m' =
   list_compare (pair_compare K.compare cmp) (bindings m) (bindings m').
 Proof. apply R.compare_spec; apply ok. Qed.

End Pack.
