
(** * Finite Modular Maps : Functors of Properties *)

(** Author : Pierre Letouzey (Université de Paris - INRIA),
    adapted from earlier works in Coq Standard Library, see README.md.
    Licence : LGPL 2.1, see file LICENSE. *)

(** This functor derives additional facts from [Tries.MMaps.Interface.S]. These
  facts are mainly the specifications of [Tries.MMaps.Interface.S] written using
  different styles: equivalence and boolean equalities.
*)

From Coq Require Import Bool Equalities Orders OrdersFacts OrdersLists.
From Coq Require OrdersAlt.
From Coq Require Import Morphisms Permutation SetoidPermutation.
From Tries.MMaps Require Import Utils Comparisons Interface.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Properties that are common to weak maps and ordered maps.

    Thanks to subtyping, this functor can also be applied to
    [(K:OrderedType)(M:S K)].
*)

Module Properties (K:DecidableType)(Import M:WS K).

Definition Empty {elt}(m : t elt) := forall x e, ~MapsTo x e m.

Definition eq_key_elt {elt} := Duo K.eq (@Logic.eq elt).
Definition eq_key {elt} := @Fst _ elt K.eq.

(** A few things about K.eq *)

Lemma eq_refl x : K.eq x x. Proof. apply K.eq_equiv. Qed.
Lemma eq_sym x y : K.eq x y -> K.eq y x. Proof. apply K.eq_equiv. Qed.
Lemma eq_trans x y z : K.eq x y -> K.eq y z -> K.eq x z.
Proof. apply K.eq_equiv. Qed.
Global Hint Immediate eq_refl eq_sym : map.
Global Hint Resolve eq_trans eq_equivalence K.eq_equiv : map.

Definition eqb x y := if K.eq_dec x y then true else false.

Lemma eqb_eq x y : eqb x y = true <-> K.eq x y.
Proof.
 unfold eqb; case K.eq_dec; now intuition.
Qed.

Lemma eqb_sym x y : eqb x y = eqb y x.
Proof.
 apply eq_bool_alt. rewrite !eqb_eq. split; apply K.eq_equiv.
Qed.

(** Initial results about MapsTo and In *)

Lemma mapsto_fun {elt} m x (e e':elt) :
  MapsTo x e m -> MapsTo x e' m -> e=e'.
Proof.
rewrite <- !find_spec. congruence.
Qed.

Lemma in_find {elt} (m : t elt) x : In x m <-> find x m <> None.
Proof.
 unfold In. split.
 - intros (e,H). rewrite <-find_spec in H. congruence.
 - destruct (find x m) as [e|] eqn:H.
   + exists e. now apply find_spec.
   + now destruct 1.
Qed.

Lemma not_in_find {elt} (m : t elt) x : ~In x m <-> find x m = None.
Proof.
 rewrite in_find. split; auto.
 intros; destruct (find x m); trivial. now destruct H.
Qed.

Notation in_find_iff := in_find (only parsing).
Notation not_find_in_iff := not_in_find (only parsing).

(** * [Equal] and [Eqdom] are setoid equalities. *)

Infix "==" := Equal (at level 30).

Global Instance Equal_equiv {elt} : Equivalence (@Equal elt).
Proof.
unfold Equal. split; congruence.
Qed.

Global Instance Eqdom_equiv {elt} : Equivalence (@Eqdom elt).
Proof.
split.
- now intro m.
- now intros m m'.
- intros m1 m2 m3 E E' y. now rewrite (E y), <-(E' y).
Qed.

Global Instance Equal_Eqdom {elt} : subrelation (@Equal elt) (@Eqdom elt).
Proof.
 intros x y E k. specialize (E k). now rewrite !in_find, E.
Qed.

Arguments Equal {elt} m m'.
Arguments Eqdom {elt} m m'.

Global Instance MapsTo_m {elt} :
  Proper (K.eq==>Logic.eq==>Equal==>iff) (@MapsTo elt).
Proof.
intros k k' Hk e e' <- m m' Hm. rewrite <- Hk.
now rewrite <- !find_spec, Hm.
Qed.

Global Instance find_m {elt} : Proper (K.eq==>Equal==>Logic.eq) (@find elt).
Proof.
intros k k' Hk m m' <-.
rewrite eq_option_alt. intros. now rewrite !find_spec, Hk.
Qed.

(** Note : some morphisms below can be stated with [Eqdom] instead
    of [Equal] when only the keys are considered, not the datas.
    Since [Equal] implies [Eqdom], this allows nonetheless to
    rewrite later with [Equal]. *)

Global Instance In_m {elt} : Proper (K.eq==>Eqdom==>iff) (@In elt).
Proof.
intros k k' Hk m m' Hm. rewrite (Hm k). rewrite !in_find. now rewrite Hk.
Qed.

Global Instance mem_m {elt} : Proper (K.eq==>Eqdom==>Logic.eq) (@mem elt).
Proof.
intros k k' Hk m m' Hm. now rewrite eq_bool_alt, !mem_spec, Hk, Hm.
Qed.

Global Instance Empty_m {elt} : Proper (Eqdom==>iff) (@Empty elt).
Proof.
assert (forall m m' : t elt, Eqdom m m' -> Empty m -> Empty m').
{ intros m m' EQ EM x e MT.
  assert (IN : In x m') by firstorder.
  rewrite <- EQ in IN. destruct IN as (e' & MT').
  revert MT'. apply EM. }
intros m m' EQ. split; apply H; auto. symmetry; auto.
Qed.

Global Instance is_empty_m {elt} : Proper (Eqdom ==> Logic.eq) (@is_empty elt).
Proof.
intros m m' Hm. rewrite eq_bool_alt, !is_empty_spec.
setoid_rewrite <- not_in_find. now setoid_rewrite Hm.
Qed.

Global Instance add_m {elt} : Proper (K.eq==>Logic.eq==>Equal==>Equal) (@add elt).
Proof.
intros k k' Hk e e' <- m m' Hm y.
destruct (K.eq_dec k y) as [H|H].
- rewrite <-H, add_spec1. now rewrite Hk, add_spec1.
- rewrite !add_spec2; trivial. now rewrite <- Hk.
Qed.

Global Instance remove_m {elt} : Proper (K.eq==>Equal==>Equal) (@remove elt).
Proof.
intros k k' Hk m m' Hm y.
destruct (K.eq_dec k y) as [H|H].
- rewrite <-H, remove_spec1. now rewrite Hk, remove_spec1.
- rewrite !remove_spec2; trivial. now rewrite <- Hk.
Qed.

Global Instance merge_m {elt elt' elt''} :
 Proper ((K.eq==>Logic.eq==>Logic.eq==>Logic.eq)==>Equal==>Equal==>Equal)
  (@merge elt elt' elt'').
Proof.
intros f f' Hf m1 m1' Hm1 m2 m2' Hm2 y.
destruct (find y m1) as [e1|] eqn:H1.
- apply find_spec in H1.
  assert (H : In y m1 \/ In y m2) by (left; now exists e1).
  destruct (merge_spec1 f H) as (y1,(Hy1,->)).
  rewrite Hm1,Hm2 in H.
  destruct (merge_spec1 f' H) as (y2,(Hy2,->)).
  rewrite <- Hm1, <- Hm2. apply Hf; trivial. now transitivity y.
- destruct (find y m2) as [e2|] eqn:H2.
  + apply find_spec in H2.
    assert (H : In y m1 \/ In y m2) by (right; now exists e2).
    destruct (merge_spec1 f H) as (y1,(Hy1,->)).
    rewrite Hm1,Hm2 in H.
    destruct (merge_spec1 f' H) as (y2,(Hy2,->)).
    rewrite <- Hm1, <- Hm2. apply Hf; trivial. now transitivity y.
  + apply not_in_find in H1. apply not_in_find in H2.
    assert (H : ~In y (merge f m1 m2)).
    { intro H. apply merge_spec2 in H. intuition. }
    apply not_in_find in H. rewrite H.
    symmetry. apply not_in_find. intro H'.
    apply merge_spec2 in H'. rewrite <- Hm1, <- Hm2 in H'.
    intuition.
Qed.

(* Later: compatibility for cardinal, fold, map, mapi... *)

(** ** Earlier specifications (cf. FMaps) *)

Section OldSpecs.
Variable elt: Type.
Implicit Type m: t elt.
Implicit Type x y z: key.
Implicit Type e: elt.

Lemma MapsTo_1 m x y e : K.eq x y -> MapsTo x e m -> MapsTo y e m.
Proof.
 now intros ->.
Qed.

Lemma find_1 m x e : MapsTo x e m -> find x m = Some e.
Proof. apply find_spec. Qed.

Lemma find_2 m x e : find x m = Some e -> MapsTo x e m.
Proof. apply find_spec. Qed.

Lemma mem_1 m x : In x m -> mem x m = true.
Proof. apply mem_spec. Qed.

Lemma mem_2 m x : mem x m = true -> In x m.
Proof. apply mem_spec. Qed.

Lemma empty_1 : Empty (@empty elt).
Proof.
 intros x e. now rewrite <- find_spec, empty_spec.
Qed.

Lemma is_empty_1 m : Empty m -> is_empty m = true.
Proof.
 unfold Empty; rewrite is_empty_spec. setoid_rewrite <- find_spec.
 intros H x. specialize (H x).
 destruct (find x m) as [e|]; trivial.
 now destruct (H e).
Qed.

Lemma is_empty_2 m : is_empty m = true -> Empty m.
Proof.
 rewrite is_empty_spec. intros H x e. now rewrite <- find_spec, H.
Qed.

Lemma add_1 m x y e : K.eq x y -> MapsTo y e (add x e m).
Proof.
 intros <-. rewrite <-find_spec. apply add_spec1.
Qed.

Lemma add_2 m x y e e' :
  ~ K.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
Proof.
 intro. now rewrite <- !find_spec, add_spec2.
Qed.

Lemma add_3 m x y e e' :
  ~ K.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
Proof.
 intro. rewrite <- !find_spec, add_spec2; trivial.
Qed.

Lemma remove_1 m x y : K.eq x y -> ~ In y (remove x m).
Proof.
 intros <-. apply not_in_find. apply remove_spec1.
Qed.

Lemma remove_2 m x y e :
  ~ K.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
Proof.
 intro. now rewrite <- !find_spec, remove_spec2.
Qed.

Lemma remove_3bis m x y e :
  find y (remove x m) = Some e -> find y m = Some e.
Proof.
 destruct (K.eq_dec x y) as [<-|H].
 - now rewrite remove_spec1.
 - now rewrite remove_spec2.
Qed.

Lemma remove_3 m x y e : MapsTo y e (remove x m) -> MapsTo y e m.
Proof.
 rewrite <-!find_spec. apply remove_3bis.
Qed.

Lemma bindings_1 m x e :
  MapsTo x e m -> InA eq_key_elt (x,e) (bindings m).
Proof. apply bindings_spec1. Qed.

Lemma bindings_2 m x e :
  InA eq_key_elt (x,e) (bindings m) -> MapsTo x e m.
Proof. apply bindings_spec1. Qed.

Lemma bindings_3w m : NoDupA eq_key (bindings m).
Proof. apply bindings_spec2w. Qed.

Lemma cardinal_1 m : cardinal m = length (bindings m).
Proof. apply cardinal_spec. Qed.

Lemma fold_1 m (A : Type) (i : A) (f : key -> elt -> A -> A) :
  fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.
Proof. apply fold_spec. Qed.

Lemma equal_1 m m' cmp : Equivb cmp m m' -> equal cmp m m' = true.
Proof. apply equal_spec. Qed.

Lemma equal_2 m m' cmp : equal cmp m m' = true -> Equivb cmp m m'.
Proof. apply equal_spec. Qed.

End OldSpecs.

(** Earlier spec about [map], now subsumed by a more precise one
    via [bindings] *)

Lemma map_find {elt elt'}(f:elt->elt') m x :
 find x (map f m) = option_map f (find x m).
Proof.
 destruct (find x m) eqn:E; simpl.
 - rewrite find_spec, <- bindings_spec1 in *.
   rewrite InA_alt in *.
   destruct E as ((y,e') & (E1,E2) & IN). simpl in *. subst e'.
   exists (y,f e). split; [easy| ].
   rewrite map_spec, in_map_iff. now exists (y,e).
 - rewrite <- not_in_find in *. rewrite <- not_in_find in E.
   contradict E. destruct E as (e,M).
   rewrite <- bindings_spec1, map_spec, InA_alt in M.
   destruct M as ((y,e') & (E1,E2) & IN). simpl in *; subst e'.
   rewrite in_map_iff in IN. destruct IN as ((z,e0) & [= <- _] & IN).
   exists e0. rewrite <- bindings_spec1, InA_alt. firstorder.
Qed.

(** Same for [mapi] *)

Lemma mapi_find {elt elt'}(f:key->elt->elt') m x :
 exists y, K.eq y x /\ find x (mapi f m) = option_map (f y) (find x m).
Proof.
 destruct (find x m) eqn:E; simpl.
 - rewrite find_spec, <- bindings_spec1 in *.
   rewrite InA_alt in *.
   destruct E as ((y,e') & (E1,E2) & IN). simpl in *. subst e'.
   exists y. split; [easy| ].
   rewrite find_spec, <- bindings_spec1, InA_alt.
   exists (y,f y e). split; [easy| ].
   rewrite mapi_spec, in_map_iff. now exists (y,e).
 - exists x. split; [easy| ].
   rewrite <- not_in_find in *. rewrite <- not_in_find in E.
   contradict E. destruct E as (e,M).
   rewrite <- bindings_spec1, mapi_spec, InA_alt in M.
   destruct M as ((y,e') & (E1,E2) & IN). simpl in *; subst e'.
   rewrite in_map_iff in IN. destruct IN as ((z,e0) & [= <- _] & IN).
   exists e0. rewrite <- bindings_spec1, InA_alt. firstorder.
Qed.

Global Instance map_m {elt elt'} :
  Proper ((Logic.eq==>Logic.eq)==>Equal==>Equal) (@map elt elt').
Proof.
intros f f' Hf m m' Hm y. rewrite !map_find, Hm.
destruct (find y m'); simpl; trivial. f_equal. now apply Hf.
Qed.

Global Instance mapi_m {elt elt'} :
  Proper ((K.eq==>Logic.eq==>Logic.eq)==>Equal==>Equal) (@mapi elt elt').
Proof.
intros f f' Hf m m' Hm y.
destruct (mapi_find f m y) as (x,(Hx,->)).
destruct (mapi_find f' m' y) as (x',(Hx',->)).
rewrite <- Hm. destruct (find y m); trivial. simpl.
f_equal. apply Hf; trivial. now rewrite Hx, Hx'.
Qed.

Lemma map_1 {elt elt'}(m: t elt)(x:key)(e:elt)(f:elt->elt') :
  MapsTo x e m -> MapsTo x (f e) (map f m).
Proof.
 rewrite <- !find_spec, map_find. now intros ->.
Qed.

Lemma map_2 {elt elt'}(m: t elt)(x:key)(f:elt->elt') :
  In x (map f m) -> In x m.
Proof.
 rewrite !in_find, map_find. apply option_map_some.
Qed.

Lemma mapi_1 {elt elt'}(m: t elt)(x:key)(e:elt)(f:key->elt->elt') :
  MapsTo x e m ->
  exists y, K.eq y x /\ MapsTo x (f y e) (mapi f m).
Proof.
 destruct (mapi_find f m x) as (y,(Hy,Eq)).
 intro H. exists y; split; trivial.
 rewrite <-find_spec in *. now rewrite Eq, H.
Qed.

Lemma mapi_2 {elt elt'}(m: t elt)(x:key)(f:key->elt->elt') :
  In x (mapi f m) -> In x m.
Proof.
 destruct (mapi_find f m x) as (y,(Hy,Eq)).
 rewrite !in_find. intro H; contradict H. now rewrite Eq, H.
Qed.

(** The ancestor [map2] of the current [merge] was dealing with functions
    on datas only, not on keys. *)

Definition map2 {elt elt' elt''} (f:option elt->option elt'->option elt'')
 := merge (fun _ => f).

Lemma map2_1 {elt elt' elt''}(m: t elt)(m': t elt')
      (x:key)(f:option elt->option elt'->option elt'') :
  In x m \/ In x m' ->
  find x (map2 f m m') = f (find x m) (find x m').
Proof.
 intros. unfold map2.
 now destruct (merge_spec1 (fun _ => f) H) as (y,(_,->)).
Qed.

Lemma map2_2 {elt elt' elt''}(m: t elt)(m': t elt')
      (x:key)(f:option elt->option elt'->option elt'') :
  In x (map2 f m m') -> In x m \/ In x m'.
Proof. apply merge_spec2. Qed.

Global Hint Immediate MapsTo_1 mem_2 is_empty_2 : map.
Global Hint Immediate map_2 mapi_2 add_3 remove_3 find_2 : map.
Global Hint Resolve mem_1 is_empty_1 is_empty_2 add_1 add_2 remove_1 : map.
Global Hint Resolve remove_2 find_1 fold_1 map_1 mapi_1 mapi_2 : map.

(** ** Specifications written using equivalences *)

Section IffSpec.
Variable elt: Type.
Implicit Type m: t elt.
Implicit Type x y z: key.
Implicit Type e: elt.

Lemma in_iff m x y : K.eq x y -> (In x m <-> In y m).
Proof. now intros ->. Qed.

Lemma mapsto_iff m x y e : K.eq x y -> (MapsTo x e m <-> MapsTo y e m).
Proof. now intros ->. Qed.

Lemma mem_in_iff m x : In x m <-> mem x m = true.
Proof. symmetry. apply mem_spec. Qed.

Lemma not_mem_in_iff m x : ~In x m <-> mem x m = false.
Proof.
rewrite mem_in_iff; destruct (mem x m); intuition.
Qed.

Lemma mem_find m x : mem x m = true <-> find x m <> None.
Proof.
 rewrite <- mem_in_iff. apply in_find.
Qed.

Lemma not_mem_find m x : mem x m = false <-> find x m = None.
Proof.
 rewrite <- not_mem_in_iff. apply not_in_find.
Qed.

Lemma In_dec m x : { In x m } + { ~ In x m }.
Proof.
 generalize (mem_in_iff m x).
 destruct (mem x m); [left|right]; intuition.
Qed.

Lemma find_mapsto_iff m x e : MapsTo x e m <-> find x m = Some e.
Proof. symmetry. apply find_spec. Qed.

Lemma equal_iff m m' cmp : Equivb cmp m m' <-> equal cmp m m' = true.
Proof. symmetry. apply equal_spec. Qed.

Lemma empty_mapsto_iff x e : MapsTo x e empty <-> False.
Proof.
rewrite <- find_spec, empty_spec. now split.
Qed.

Lemma not_in_empty x : ~In x (@empty elt).
Proof.
intros (e,H). revert H. apply empty_mapsto_iff.
Qed.

Lemma empty_in_iff x : In x (@empty elt) <-> False.
Proof.
split; [ apply not_in_empty | destruct 1 ].
Qed.

Lemma is_empty_iff m : Empty m <-> is_empty m = true.
Proof. split; [apply is_empty_1 | apply is_empty_2 ]. Qed.

Lemma add_mapsto_iff m x y e e' :
  MapsTo y e' (add x e m) <->
     (K.eq x y /\ e=e') \/
     (~K.eq x y /\ MapsTo y e' m).
Proof.
split.
- intros H. destruct (K.eq_dec x y); [left|right]; split; trivial.
  + symmetry. apply (mapsto_fun H); auto with map.
  + now apply add_3 with x e.
- destruct 1 as [(H,H')|(H,H')]; subst; auto with map.
Qed.

Lemma add_mapsto_new m x y e e' : ~In x m ->
  MapsTo y e' (add x e m) <-> (K.eq x y /\ e=e') \/ MapsTo y e' m.
Proof.
 intros.
 rewrite add_mapsto_iff. intuition.
 right; split; trivial. contradict H. exists e'. now rewrite H.
Qed.

Lemma in_add m x y e : In y m -> In y (add x e m).
Proof.
 destruct (K.eq_dec x y) as [<-|H'].
 - now rewrite !in_find, add_spec1.
 - now rewrite !in_find, add_spec2.
Qed.

Lemma add_in_iff m x y e : In y (add x e m) <-> K.eq x y \/ In y m.
Proof.
split.
- intros H. destruct (K.eq_dec x y); [now left|right].
  rewrite in_find, add_spec2 in H; trivial. now apply in_find.
- intros [<-|H].
  + exists e. now apply add_1.
  + now apply in_add.
Qed.

Lemma add_neq_mapsto_iff m x y e e' :
 ~ K.eq x y -> (MapsTo y e' (add x e m) <-> MapsTo y e' m).
Proof.
split; [apply add_3|apply add_2]; auto.
Qed.

Lemma add_neq_in_iff m x y e :
 ~ K.eq x y -> (In y (add x e m)  <-> In y m).
Proof.
split; intros (e',H0); exists e'.
- now apply add_3 with x e.
- now apply add_2.
Qed.

Lemma remove_mapsto_iff m x y e :
  MapsTo y e (remove x m) <-> ~K.eq x y /\ MapsTo y e m.
Proof.
split; [split|destruct 1].
- intro E. revert H. now rewrite <-E, <- find_spec, remove_spec1.
- now apply remove_3 with x.
- now apply remove_2.
Qed.

Lemma remove_in_iff m x y : In y (remove x m) <-> ~K.eq x y /\ In y m.
Proof.
unfold In; split; [ intros (e,H) | intros (E,(e,H)) ].
- apply remove_mapsto_iff in H. destruct H; split; trivial.
  now exists e.
- exists e. now apply remove_2.
Qed.

Lemma remove_neq_mapsto_iff : forall m x y e,
 ~ K.eq x y -> (MapsTo y e (remove x m)  <-> MapsTo y e m).
Proof.
split; [apply remove_3|apply remove_2]; auto.
Qed.

Lemma remove_neq_in_iff : forall m x y,
 ~ K.eq x y -> (In y (remove x m) <-> In y m).
Proof.
split; intros (e',H0); exists e'.
- now apply remove_3 with x.
- now apply remove_2.
Qed.

Lemma bindings_mapsto_iff m x e :
 MapsTo x e m <-> InA eq_key_elt (x,e) (bindings m).
Proof. symmetry. apply bindings_spec1. Qed.

Lemma bindings_in_iff m x :
 In x m <-> exists e, InA eq_key_elt (x,e) (bindings m).
Proof.
unfold In; split; intros (e,H); exists e; now apply bindings_spec1.
Qed.

Lemma singleton_mapsto_iff x y e e' :
 MapsTo y e' (singleton x e) <-> K.eq x y /\ e = e'.
Proof.
rewrite <- bindings_spec1, singleton_spec, InA_cons, InA_nil.
unfold Duo; simpl. intuition.
Qed.

End IffSpec.

Lemma map_mapsto_iff {elt elt'} m x b (f : elt -> elt') :
 MapsTo x b (map f m) <-> exists a, b = f a /\ MapsTo x a m.
Proof.
rewrite <-find_spec, map_find. setoid_rewrite <- find_spec.
destruct (find x m); simpl; split.
- injection 1. now exists e.
- intros (a,(->,H)). now injection H as ->.
- discriminate.
- intros (a,(_,H)); discriminate.
Qed.

Lemma map_in_iff {elt elt'} m x (f : elt -> elt') :
 In x (map f m) <-> In x m.
Proof.
rewrite !in_find, map_find. apply option_map_some.
Qed.

Lemma mapi_in_iff {elt elt'} m x (f:key->elt->elt') :
 In x (mapi f m) <-> In x m.
Proof.
rewrite !in_find. destruct (mapi_find f m x) as (y,(_,->)).
apply option_map_some.
Qed.

(** Unfortunately, we don't have simple equivalences for [mapi]
  and [MapsTo]. The only correct one needs compatibility of [f]. *)

Lemma mapi_inv {elt elt'} m x b (f : key -> elt -> elt') :
 MapsTo x b (mapi f m) ->
 exists a y, K.eq y x /\ b = f y a /\ MapsTo x a m.
Proof.
rewrite <- find_spec. setoid_rewrite <- find_spec.
destruct (mapi_find f m x) as (y,(E,->)).
destruct (find x m); simpl.
- injection 1 as <-. now exists e, y.
- discriminate.
Qed.

Lemma mapi_find' {elt elt'} (f:key->elt->elt') :
 Proper (K.eq==>Logic.eq==>Logic.eq) f ->
 forall m x,
   find x (mapi f m) = option_map (f x) (find x m).
Proof.
 intros. destruct (mapi_find f m x) as (y,(Hy,->)).
 destruct (find x m); simpl; trivial.
 now rewrite Hy.
Qed.

Lemma mapi_1bis {elt elt'} m x e (f:key->elt->elt') :
 Proper (K.eq==>Logic.eq==>Logic.eq) f ->
 MapsTo x e m -> MapsTo x (f x e) (mapi f m).
Proof.
intros. destruct (mapi_1 f H0) as (y,(->,H2)). trivial.
Qed.

Lemma mapi_mapsto_iff {elt elt'} m x b (f:key->elt->elt') :
 Proper (K.eq==>Logic.eq==>Logic.eq) f ->
 (MapsTo x b (mapi f m) <-> exists a, b = f x a /\ MapsTo x a m).
Proof.
rewrite <-find_spec. setoid_rewrite <-find_spec.
intros Pr. rewrite mapi_find' by trivial.
destruct (find x m); simpl; split.
- injection 1 as <-. now exists e.
- intros (a,(->,H)). now injection H as <-.
- discriminate.
- intros (a,(_,H)). discriminate.
Qed.

(** Things are even worse for [merge] : we don't try to state any
 equivalence, see instead boolean results below. *)

(** The usual operations are compatible with [Eqdom] :
    same domain before, same domain after, regardless of what happens
    to the datas. *)

Global Instance add_m' {elt} : Proper (K.eq==>Logic.eq==>Eqdom==>Eqdom) (@add elt).
Proof.
intros k k' Hk e e' <- m m' Hm y.
rewrite !add_in_iff. now rewrite Hk, Hm.
Qed.

Global Instance remove_m' {elt} : Proper (K.eq==>Eqdom==>Eqdom) (@remove elt).
Proof.
intros k k' Hk m m' Hm y.
rewrite !remove_in_iff. now rewrite Hk, Hm.
Qed.

(** Note : We could even use completely differents functions below,
    not equal ones *)

Global Instance map_m' {elt elt'} :
  Proper (Logic.eq==>Eqdom==>Eqdom) (@map elt elt').
Proof.
intros f f' <- m m' Hm y. rewrite !map_in_iff. apply Hm.
Qed.

Global Instance mapi_m' {elt elt'} :
  Proper (Logic.eq==>Eqdom==>Eqdom) (@mapi elt elt').
Proof.
intros f f' <- m m' Hm y. rewrite !mapi_in_iff. apply Hm.
Qed.

(** Useful tactic for simplifying expressions like
   [In y (add x e (remove z m))] *)

Ltac map_iff :=
 repeat (progress (
  rewrite add_mapsto_iff || rewrite add_in_iff ||
  rewrite remove_mapsto_iff || rewrite remove_in_iff ||
  rewrite empty_mapsto_iff || rewrite empty_in_iff ||
  rewrite map_mapsto_iff || rewrite map_in_iff ||
  rewrite mapi_in_iff)).

(** ** Specifications via the reflect predicate *)

Lemma is_empty_spec' {elt}(m:t elt) : reflect (Empty m) (is_empty m).
Proof.
 apply iff_reflect. apply is_empty_iff.
Qed.

Lemma mem_spec' {elt} x (m:t elt) : reflect (In x m) (mem x m).
Proof.
 apply iff_reflect. apply mem_in_iff.
Qed.

(** ** Specifications written using boolean predicates *)

Section BoolSpec.

Lemma mem_find_b {elt}(m:t elt)(x:key) :
  mem x m = if find x m then true else false.
Proof.
apply eq_bool_alt. rewrite mem_find. destruct (find x m).
- now split.
- split; (discriminate || now destruct 1).
Qed.

Variable elt elt' elt'' : Type.
Implicit Types m : t elt.
Implicit Types x y z : key.
Implicit Types e : elt.

Lemma mem_b m x y : K.eq x y -> mem x m = mem y m.
Proof. now intros ->. Qed.

Lemma find_o m x y : K.eq x y -> find x m = find y m.
Proof. now intros ->. Qed.

Lemma empty_o x : find x (@empty elt) = None.
Proof. apply empty_spec. Qed.

Lemma empty_a x : mem x (@empty elt) = false.
Proof. apply not_mem_find. apply empty_spec. Qed.

Lemma add_eq_o m x y e :
 K.eq x y -> find y (add x e m) = Some e.
Proof.
 intros <-. apply add_spec1.
Qed.

Lemma add_neq_o m x y e :
 ~ K.eq x y -> find y (add x e m) = find y m.
Proof. apply add_spec2. Qed.
Hint Resolve add_neq_o : map.

Lemma add_o m x y e :
 find y (add x e m) = if K.eq_dec x y then Some e else find y m.
Proof.
destruct (K.eq_dec x y); auto with map.
Qed.

Lemma add_eq_b m x y e :
 K.eq x y -> mem y (add x e m) = true.
Proof.
intros <-. apply mem_spec, add_in_iff. now left.
Qed.

Lemma add_neq_b m x y e :
 ~K.eq x y -> mem y (add x e m) = mem y m.
Proof.
intros. now rewrite !mem_find_b, add_neq_o.
Qed.

Lemma add_b m x y e :
 mem y (add x e m) = eqb x y || mem y m.
Proof.
rewrite !mem_find_b, add_o. unfold eqb.
now destruct (K.eq_dec x y).
Qed.

Lemma remove_eq_o m x y :
 K.eq x y -> find y (remove x m) = None.
Proof. intros ->. apply remove_spec1. Qed.

Lemma remove_neq_o m x y :
 ~ K.eq x y -> find y (remove x m) = find y m.
Proof. apply remove_spec2. Qed.

Hint Resolve remove_eq_o remove_neq_o : map.

Lemma remove_o m x y :
 find y (remove x m) = if K.eq_dec x y then None else find y m.
Proof.
destruct (K.eq_dec x y); auto with map.
Qed.

Lemma remove_eq_b m x y :
 K.eq x y -> mem y (remove x m) = false.
Proof.
intros <-. now rewrite mem_find_b, remove_eq_o.
Qed.

Lemma remove_neq_b m x y :
 ~ K.eq x y -> mem y (remove x m) = mem y m.
Proof.
intros. now rewrite !mem_find_b, remove_neq_o.
Qed.

Lemma remove_b m x y :
 mem y (remove x m) = negb (eqb x y) && mem y m.
Proof.
rewrite !mem_find_b, remove_o; unfold eqb.
now destruct (K.eq_dec x y).
Qed.

Lemma singleton_o1 x e :
 find x (singleton x e) = Some e.
Proof.
 now rewrite find_spec, singleton_mapsto_iff.
Qed.

Lemma singleton_o2 x y e :
 ~K.eq x y -> find y (singleton x e) = None.
Proof.
 intros H. rewrite <- not_in_find. contradict H.
 destruct H as (e' & H). now rewrite singleton_mapsto_iff in H.
Qed.

Lemma singleton_o x y e :
 find y (singleton x e) = if K.eq_dec x y then Some e else None.
Proof.
destruct (K.eq_dec x y) as [<-|NE];
 auto using singleton_o1, singleton_o2.
Qed.

Lemma map_o m x (f:elt->elt') :
 find x (map f m) = option_map f (find x m).
Proof. apply map_find. Qed.

Lemma map_b m x (f:elt->elt') :
 mem x (map f m) = mem x m.
Proof.
rewrite !mem_find_b, map_o. now destruct (find x m).
Qed.

Lemma mapi_b m x (f:key->elt->elt') :
 mem x (mapi f m) = mem x m.
Proof.
apply eq_bool_alt; rewrite !mem_spec. apply mapi_in_iff.
Qed.

Lemma mapi_o m x (f:key->elt->elt') :
 Proper (K.eq==>Logic.eq==>Logic.eq) f ->
 find x (mapi f m) = option_map (f x) (find x m).
Proof. intros; now apply mapi_find'. Qed.

(** Specification of [merge] when more is known on [f]. *)

(** If [f] is a morphism w.r.t [K.eq], then we can get rid of the
    [exists y] in [merge_spec1]. *)

Lemma merge_spec1m (f:key->option elt->option elt'->option elt'') :
 Proper (K.eq==>Logic.eq==>Logic.eq==>Logic.eq) f ->
 forall (m:t elt)(m':t elt') x,
   In x m \/ In x m' ->
   find x (merge f m m') = f x (find x m) (find x m').
Proof.
 intros Hf m m' x H.
 now destruct (merge_spec1 f H) as (y,(->,->)).
Qed.

(** If [f _ None None = None], then we can get rid of the
    [In ... \/ In ...] condition in [merge_spec1]. *)

Lemma merge_spec1n (f:key->option elt->option elt'->option elt'') :
 (forall x, f x None None = None) ->
 forall (m: t elt)(m': t elt') x,
 exists y, K.eq y x /\ find x (merge f m m') = f y (find x m) (find x m').
Proof.
intros Hf m m' x.
destruct (find x m) as [e|] eqn:Hm.
- assert (H : In x m \/ In x m') by (left; exists e; now apply find_spec).
  destruct (merge_spec1 f H) as (y,(Hy,->)).
  exists y; split; trivial. now rewrite Hm.
- destruct (find x m') as [e|] eqn:Hm'.
  + assert (H : In x m \/ In x m') by (right; exists e; now apply find_spec).
    destruct (merge_spec1 f H) as (y,(Hy,->)).
    exists y; split; trivial. now rewrite Hm, Hm'.
  + exists x. split. reflexivity. rewrite Hf.
    apply not_in_find. intro H.
    apply merge_spec2 in H. apply not_in_find in Hm. apply not_in_find in Hm'.
    intuition.
Qed.

(** And if [f] is both a morphism and satisfies [f _ None None = None] : *)

Lemma merge_spec1mn (f:key->option elt->option elt'->option elt'') :
 Proper (K.eq==>Logic.eq==>Logic.eq==>Logic.eq) f ->
 (forall x, f x None None = None) ->
 forall (m: t elt)(m': t elt') x,
  find x (merge f m m') = f x (find x m) (find x m').
Proof.
 intros Hf Hf' m m' x.
 now destruct (merge_spec1n Hf' m m' x) as (y,(->,->)).
Qed.

Lemma bindings_o : forall m x,
 find x m = findA (eqb x) (bindings m).
Proof.
intros. rewrite eq_option_alt. intro e.
rewrite <- find_mapsto_iff, bindings_mapsto_iff.
unfold eqb.
rewrite <- findA_NoDupA; dintuition; try apply bindings_3w; eauto.
Qed.

Lemma bindings_b : forall m x,
 mem x m = existsb (fun p => eqb x (fst p)) (bindings m).
Proof.
intros.
apply eq_bool_alt.
rewrite mem_spec, bindings_in_iff, existsb_exists.
split.
- intros (e,H).
  rewrite InA_alt in H.
  destruct H as ((k,e'),((H1,H2),H')); simpl in *; subst e'.
  exists (k, e); split; trivial. simpl. now apply eqb_eq.
- intros ((k,e),(H,H')); simpl in *. apply eqb_eq in H'.
  exists e. rewrite InA_alt. exists (k,e). now repeat split.
Qed.

End BoolSpec.

Section Equalities.
Variable elt:Type.

(** A few basic equalities *)

Lemma singleton_add x (e:elt) : singleton x e == add x e empty.
Proof.
 intros y. now rewrite singleton_o, add_o, empty_o.
Qed.

Global Instance singleton_m :
 Proper (K.eq ==> eq ==> Equal) (@singleton elt).
Proof.
 intros x x' Hx e e' <-. rewrite !singleton_add. now f_equiv.
Qed.

Lemma eq_empty (m: t elt) : m == empty <-> is_empty m = true.
Proof.
 unfold Equal. rewrite is_empty_spec. now setoid_rewrite empty_spec.
Qed.

Lemma add_id (m: t elt) x e : add x e m == m <-> find x m = Some e.
Proof.
 split.
 - intros H. rewrite <- (H x). apply add_spec1.
 - intros H y. rewrite !add_o. now destruct K.eq_dec as [<-|E].
Qed.

Lemma add_add_1 (m: t elt) x e :
 add x e (add x e m) == add x e m.
Proof.
 intros y. rewrite !add_o. destruct K.eq_dec; auto.
Qed.

Lemma add_add_2 (m: t elt) x x' e e' :
 ~K.eq x x' -> add x e (add x' e' m) == add x' e' (add x e m).
Proof.
 intros H y. rewrite !add_o.
 do 2 destruct K.eq_dec; auto.
 elim H. now transitivity y.
Qed.

Lemma remove_id (m: t elt) x : remove x m == m <-> ~In x m.
Proof.
 rewrite not_in_find. split.
 - intros H. rewrite <- (H x). apply remove_spec1.
 - intros H y. rewrite !remove_o. now destruct K.eq_dec as [<-|E].
Qed.

Lemma remove_remove_1 (m: t elt) x :
 remove x (remove x m) == remove x m.
Proof.
 intros y. rewrite !remove_o. destruct K.eq_dec; auto.
Qed.

Lemma remove_remove_2 (m: t elt) x x' :
 remove x (remove x' m) == remove x' (remove x m).
Proof.
 intros y. rewrite !remove_o. do 2 destruct K.eq_dec; auto.
Qed.

Lemma remove_add_1 (m: t elt) x e :
  remove x (add x e m) == remove x m.
Proof.
 intro y. rewrite !remove_o, !add_o. now destruct K.eq_dec.
Qed.

Lemma remove_add_2 (m: t elt) x x' e :
  ~K.eq x x' -> remove x' (add x e m) == add x e (remove x' m).
Proof.
 intros H y. rewrite !remove_o, !add_o.
 do 2 destruct K.eq_dec; auto.
 - elim H; now transitivity y.
 - symmetry. now apply remove_eq_o.
 - symmetry. now apply remove_neq_o.
Qed.

Lemma add_remove_1 (m: t elt) x e :
  add x e (remove x m) == add x e m.
Proof.
 intro y. rewrite !add_o, !remove_o. now destruct K.eq_dec.
Qed.

(** Another characterisation of [Equal] *)

Lemma Equal_mapsto_iff : forall m1 m2 : t elt,
 m1 == m2 <-> (forall k e, MapsTo k e m1 <-> MapsTo k e m2).
Proof.
intros m1 m2. split; [intros Heq k e|intros Hiff].
rewrite 2 find_mapsto_iff, Heq. split; auto.
intro k. rewrite eq_option_alt. intro e.
rewrite <- 2 find_mapsto_iff; auto.
Qed.

(** * Relations between [Equal], [Eqdom], [Equiv] and [Equivb]. *)

(** First, [Equal] is [Equiv] with Leibniz on elements. *)

Lemma Equal_Equiv (m m' : t elt) : m == m' <-> Equiv Logic.eq m m'.
Proof.
rewrite Equal_mapsto_iff. split; intros.
- split.
  + split; intros (e,Hin); exists e; [rewrite <- H|rewrite H]; auto.
  + intros; apply mapsto_fun with m k; auto; rewrite H; auto.
- split; intros H'.
  + destruct H.
    assert (Hin : In k m') by (rewrite <- H; exists e; auto).
    destruct Hin as (e',He').
    rewrite (H0 k e e'); auto.
  + destruct H.
    assert (Hin : In k m) by (rewrite H; exists e; auto).
    destruct Hin as (e',He').
    rewrite <- (H0 k e' e); auto.
Qed.

(** [Eqdom] is [Equiv] with a trivial relation on elements. *)

Lemma Eqdom_Equiv (m m' : t elt) :
  Eqdom m m' <-> Equiv (fun _ _ => True) m m'.
Proof.
 unfold Equiv. firstorder.
Qed.

(** [Equivb] and [Equiv] and equivalent when [eq_elt] and [cmp]
    are related. *)

Section Cmp.
Variable eq_elt : elt->elt->Prop.
Variable cmp : elt->elt->bool.

Definition compat_cmp :=
 forall e e', cmp e e' = true <-> eq_elt e e'.

Lemma Equiv_Equivb : compat_cmp ->
 forall m m', Equiv eq_elt m m' <-> Equivb cmp m m'.
Proof.
 unfold Equivb, Equiv, Cmp; intuition.
 red in H; rewrite H; eauto.
 red in H; rewrite <-H; eauto.
Qed.
End Cmp.

(** If [elt] admits a boolean equality [eqb], then
    [Equal] is decidable by [equal eqb]. *)

Lemma Equal_Equivb : forall eqb,
 (forall e e', eqb e e' = true <-> e = e') ->
 forall (m m':t elt), m == m' <-> Equivb eqb m m'.
Proof.
 intros; rewrite Equal_Equiv.
 apply Equiv_Equivb; auto.
Qed.

Lemma Equal_equal : forall eqb,
 (forall e e', eqb e e' = true <-> e = e') ->
 forall (m m':t elt), m == m' <-> equal eqb m m' = true.
Proof.
 intros. rewrite equal_spec. now apply Equal_Equivb.
Qed.

(** [Eqdom] is decidable by [equal (fun _ _ => true)]. *)

Lemma Eqdom_equal (m m' : t elt) :
  Eqdom m m' <-> equal (fun _ _ => true) m m' = true.
Proof.
 rewrite equal_spec. unfold Equivb, Cmp, Equiv. firstorder.
Qed.

End Equalities.

(** * Results about [fold], [bindings], induction principles... *)

Section Elt.
  Variable elt:Type.
  Implicit Types m : t elt.
  Implicit Types e : elt.

  Definition Add x e m m' := m' == (add x e m).

  Lemma Add_add x e m : Add x e m (add x e m).
  Proof.
   red; reflexivity.
  Qed.

  Notation eqke := (@eq_key_elt elt).
  Notation eqk := (@eq_key elt).

  Instance eqk_equiv : Equivalence eqk.
  Proof. unfold eq_key, Fst. destruct K.eq_equiv. constructor; eauto. Qed.

  Instance eqke_equiv : Equivalence eqke.
  Proof.
   unfold eq_key_elt, Duo; split; repeat red; intuition; simpl in *;
    etransitivity; eauto.
  Qed.

  (** Complements about InA, NoDupA and findA *)

  Lemma InA_eqke_eqk k k' e e' l :
    K.eq k k' -> InA eqke (k,e) l -> InA eqk (k',e') l.
  Proof.
  intros Hk. rewrite 2 InA_alt.
  intros ((k'',e'') & (Hk'',He'') & H); simpl in *; subst e''.
  exists (k'',e); split; auto. compute. now transitivity k.
  Qed.

  Lemma InA_eqk_eqke k e l :
    InA eqk (k,e) l -> exists e', InA eqke (k,e') l.
  Proof.
  rewrite InA_alt. intros ((k',e') & E & IN). compute in E.
  exists e'. rewrite InA_alt. firstorder.
  Qed.

  Lemma NoDupA_incl {A} (R R':relation A) :
   (forall x y, R x y -> R' x y) ->
   forall l, NoDupA R' l -> NoDupA R l.
  Proof.
  intros Incl.
  induction 1 as [ | a l E _ IH ]; constructor; auto.
  contradict E. revert E. rewrite 2 InA_alt. firstorder.
  Qed.

  Lemma NoDupA_eqk_eqke l : NoDupA eqk l -> NoDupA eqke l.
  Proof.
  apply NoDupA_incl. now destruct 1.
  Qed.

  Lemma findA_rev l k : NoDupA eqk l ->
    findA (eqb k) l = findA (eqb k) (rev l).
  Proof.
  intros H. apply eq_option_alt. intros e. unfold eqb.
  rewrite <- !findA_NoDupA, InA_rev; eauto with map. reflexivity.
  change (NoDupA eqk (rev l)). apply NoDupA_rev; auto using eqk_equiv.
  Qed.

  (** * Bindings *)

  Lemma in_bindings_iff m x :
    In x m <-> exists e, InA eqk (x,e) (bindings m).
  Proof.
  rewrite bindings_in_iff. split.
  - intros (e,H). apply InA_eqke_eqk with (k':=x) (e':=e) in H.
    firstorder. reflexivity.
  - intros (e,H). eapply InA_eqk_eqke; eauto.
  Qed.

  Lemma in_bindings_iff' m x e :
    In x m <-> InA eqk (x,e) (bindings m).
  Proof.
  rewrite in_bindings_iff. split.
  - intros (e',H). eapply InA_eqA; eauto with *. now compute.
  - intros H. now exists e.
  Qed.

  Lemma in_fst_bindings_iff m x :
    In x m <-> InA K.eq x (List.map fst (bindings m)).
  Proof.
  rewrite InA_alt. setoid_rewrite in_map_iff.
  rewrite in_bindings_iff. setoid_rewrite InA_alt. firstorder. subst.
  exists (snd x1). firstorder.
  Qed.

  Lemma bindings_Empty m : Empty m <-> bindings m = nil.
  Proof.
  unfold Empty. split; intros H.
  - assert (H' : forall a, ~ List.In a (bindings m)).
    { intros (k,e) H'. apply (H k e).
      rewrite bindings_mapsto_iff, InA_alt.
      exists (k,e); repeat split; auto with map. }
    destruct (bindings m) as [|p l]; trivial.
    destruct (H' p); simpl; auto.
  - intros x e. rewrite bindings_mapsto_iff, InA_alt.
    rewrite H. now intros (y,(E,H')).
  Qed.

  Lemma bindings_empty : bindings (@empty elt) = nil.
  Proof.
  rewrite <-bindings_Empty; apply empty_1.
  Qed.

  (** * Conversions between maps and association lists. *)

  Definition uncurry {U V W : Type} (f : U -> V -> W) : U*V -> W :=
   fun p => f (fst p) (snd p).

  Definition of_list :=
    List.fold_right (uncurry (@add _)) (@empty elt).

  Definition to_list := bindings.

  Lemma of_list_1 l k e : NoDupA eqk l ->
    (MapsTo k e (of_list l) <-> InA eqke (k,e) l).
  Proof.
  revert k e.
  induction l as [|(k',e') l IH]; simpl; intros k e Hnodup.
  - rewrite empty_mapsto_iff, InA_nil; intuition.
  - unfold uncurry; simpl.
    inversion_clear Hnodup as [| ? ? Hnotin Hnodup'].
    specialize (IH k e Hnodup'); clear Hnodup'.
    rewrite add_mapsto_iff, InA_cons, <- IH.
    unfold eq_key_elt, Duo at 1; simpl.
    split; destruct 1 as [H|H]; try (intuition;fail).
    destruct (K.eq_dec k k'); [left|right]; split; auto with map.
    contradict Hnotin.
    apply InA_eqke_eqk with k e; intuition.
  Qed.

  Lemma of_list_1b l k : NoDupA eqk l ->
    find k (of_list l) = findA (eqb k) l.
  Proof.
  induction l as [|(k',e') l IH]; simpl; intros Hnodup.
  apply empty_o.
  unfold uncurry; simpl.
  inversion_clear Hnodup as [| ? ? Hnotin Hnodup'].
  specialize (IH Hnodup'); clear Hnodup'.
  rewrite add_o, IH, eqb_sym. unfold eqb; now destruct K.eq_dec.
  Qed.

  Lemma of_list_2 l : NoDupA eqk l ->
    equivlistA eqke l (to_list (of_list l)).
  Proof.
  intros Hnodup (k,e).
  rewrite <- bindings_mapsto_iff, of_list_1; intuition.
  Qed.

  Lemma of_list_3 s : of_list (to_list s) == s.
  Proof.
  intros k.
  rewrite of_list_1b, bindings_o; auto.
  apply bindings_3w.
  Qed.

  (** * Fold *)

  (** Alternative specification via [fold_right] *)

  Lemma fold_spec_right m {A}(i:A)(f : key -> elt -> A -> A) :
    fold f m i = List.fold_right (uncurry f) i (rev (bindings m)).
  Proof.
   rewrite fold_1. symmetry. apply fold_left_rev_right.
  Qed.

  (** ** Induction principles about fold contributed by S. Lescuyer *)

  (** In the following lemma, the step hypothesis is deliberately restricted
      to the precise map m we are considering. *)

  Lemma fold_rec :
    forall {A}(P : t elt -> A -> Type)(f : key -> elt -> A -> A),
     forall i m,
      (forall m, Empty m -> P m i) ->
      (forall k e a m' m'', MapsTo k e m -> ~In k m' ->
         Add k e m' m'' -> P m' a -> P m'' (f k e a)) ->
      P m (fold f m i).
  Proof.
  intros A P f i m Hempty Hstep.
  rewrite fold_spec_right.
  set (F:=uncurry f).
  set (l:=rev (bindings m)).
  assert (Hstep' : forall k e a m' m'', InA eqke (k,e) l -> ~In k m' ->
             Add k e m' m'' -> P m' a -> P m'' (F (k,e) a)).
  {
   intros k e a m' m'' H ? ? ?; eapply Hstep; eauto.
   revert H; unfold l; rewrite InA_rev, bindings_mapsto_iff; auto with *. }
  assert (Hdup : NoDupA eqk l).
  { unfold l. apply NoDupA_rev; try red; unfold eq_key ; eauto with *.
    apply bindings_3w. }
  assert (Hsame : forall k, find k m = findA (eqb k) l).
  { intros k. unfold l. rewrite bindings_o, findA_rev; auto.
    apply bindings_3w. }
  clearbody l. clearbody F. clear Hstep f. revert m Hsame. induction l.
  - (* empty *)
    intros m Hsame; simpl.
    apply Hempty. intros k e.
    rewrite find_mapsto_iff, Hsame; simpl; discriminate.
  - (* step *)
    intros m Hsame; destruct a as (k,e); simpl.
    apply Hstep' with (of_list l); auto.
    + rewrite InA_cons; left; compute; auto with map.
    + inversion_clear Hdup. contradict H. destruct H as (e',He').
      apply InA_eqke_eqk with k e'; auto with map.
      rewrite <- of_list_1; auto.
    + intro k'. rewrite Hsame, add_o, of_list_1b. simpl.
      rewrite eqb_sym. unfold eqb. now destruct K.eq_dec.
      inversion_clear Hdup; auto with map.
    + apply IHl.
      * intros; eapply Hstep'; eauto.
      * inversion_clear Hdup; auto.
      * intros; apply of_list_1b. inversion_clear Hdup; auto.
  Qed.

  (** Same, with [empty] and [add] instead of [Empty] and [Add]. In this
      case, [P] must be compatible with equality of sets *)

  Theorem fold_rec_bis :
    forall {A}(P : t elt -> A -> Type)(f : key -> elt -> A -> A),
     forall i m,
     (forall m m' a, m == m' -> P m a -> P m' a) ->
     (P empty i) ->
     (forall k e a m', MapsTo k e m -> ~In k m' ->
       P m' a -> P (add k e m') (f k e a)) ->
     P m (fold f m i).
  Proof.
  intros A P f i m Pmorphism Pempty Pstep.
  apply fold_rec; intros.
  apply Pmorphism with empty; auto. intro k. rewrite empty_o.
  case_eq (find k m0); auto; intros e'; rewrite <- find_mapsto_iff.
  intro H'; elim (H k e'); auto.
  apply Pmorphism with (add k e m'); try intro; auto.
  Qed.

  Lemma fold_rec_nodep :
    forall {A}(P : A -> Type)(f : key -> elt -> A -> A)(i:A) m,
     P i -> (forall k e a, MapsTo k e m -> P a -> P (f k e a)) ->
     P (fold f m i).
  Proof.
  intros. eapply fold_rec_bis; auto.
  Qed.

  (** [fold_rec_weak] is a weaker principle than [fold_rec_bis] :
      the step hypothesis must here be applicable anywhere.
      At the same time, it looks more like an induction principle,
      and hence can be easier to use. *)

  Lemma fold_rec_weak :
    forall {A}(P : t elt -> A -> Type)(f : key -> elt -> A -> A) i,
    (forall m m' a, m == m' -> P m a -> P m' a) ->
    P empty i ->
    (forall k e a m, ~In k m -> P m a -> P (add k e m) (f k e a)) ->
    forall m, P m (fold f m i).
  Proof.
  intros; apply fold_rec_bis; auto.
  Qed.

  Lemma fold_rel :
    forall {A B}(R : A -> B -> Type)
     (f : key -> elt -> A -> A)(g : key -> elt -> B -> B) i j m,
     R i j ->
     (forall k e a b, MapsTo k e m -> R a b -> R (f k e a) (g k e b)) ->
     R (fold f m i) (fold g m j).
  Proof.
  intros A B R f g i j m Rempty Rstep.
  rewrite 2 fold_spec_right. set (l:=rev (bindings m)).
  assert (Rstep' : forall k e a b, InA eqke (k,e) l ->
    R a b -> R (f k e a) (g k e b)).
  { intros; apply Rstep; auto.
    rewrite bindings_mapsto_iff, <- InA_rev; auto with map. }
  clearbody l; clear Rstep m.
  induction l; simpl; auto.
  apply Rstep'; auto.
  destruct a; simpl; rewrite InA_cons; left; compute; auto with map.
  Qed.

  (** From the induction principle on [fold], we can deduce some general
      induction principles on maps. *)

  Lemma map_induction :
   forall P : t elt -> Type,
   (forall m, Empty m -> P m) ->
   (forall m m', P m -> forall x e, ~In x m -> Add x e m m' -> P m') ->
   forall m, P m.
  Proof.
  intros. apply (@fold_rec _ (fun s _ => P s) (fun _ _ _ => tt) tt m); eauto.
  Qed.

  Lemma map_induction_bis :
   forall P : t elt -> Type,
   (forall m m', m == m' -> P m -> P m') ->
   P empty ->
   (forall x e m, ~In x m -> P m -> P (add x e m)) ->
   forall m, P m.
  Proof.
  intros.
  apply (@fold_rec_bis _ (fun s _ => P s) (fun _ _ _ => tt) tt m); eauto.
  Qed.

  (** [fold] can be used to reconstruct the same initial set. *)

  Lemma fold_identity m : fold (@add _) m empty == m.
  Proof.
  intros.
  apply fold_rec with (P:=fun m acc => acc == m); auto with map.
  intros m' Heq k'.
  rewrite empty_o.
  case_eq (find k' m'); auto; intros e'; rewrite <- find_mapsto_iff.
  intro; elim (Heq k' e'); auto.
  intros k e a m' m'' _ _ Hadd Heq k'.
  red in Heq. rewrite Hadd, 2 add_o, Heq; auto.
  Qed.

  Section Fold_More.

  (** ** Additional properties of fold *)

  (** When a function [f] is compatible and allows transpositions, we can
      compute [fold f] in any order. *)

  Variables (A:Type)(eqA:A->A->Prop)(st:Equivalence eqA).
  Variable (f:key->elt->A->A).

  Lemma fold_Empty m i : Empty m -> eqA (fold f m i) i.
  Proof.
  intros. apply fold_rec_nodep with (P:=fun a => eqA a i).
  reflexivity.
  intros. elim (H k e); auto.
  Qed.

  Variable (Hf:Proper (K.eq==>eq==>eqA==>eqA) f).

  Lemma fold_init m i i' : eqA i i' -> eqA (fold f m i) (fold f m i').
  Proof using Hf.
  intros Hi. apply fold_rel with (R:=eqA); auto.
  intros. now apply Hf.
  Qed.

  (** Transpositions of f (a.k.a diamond property).
      Could we swap two sequential calls to f, i.e. do we have:

        f k e (f k' e' a) == f k' e' (f k e a)

      First, we do not need this equation for all keys, but only
      when k and k' are distinct, as suggested by Pierre Castéran.
      Think for instance of [f] being [M.add] : in general, we don't have
      [M.add k e (M.add k e' m) == M.add k e' (M.add k e m)].
      Fortunately, we will never encounter this situation during a real
      [fold], since the keys received by this [fold] are unique.
      NB: without this condition, this condition would be
      [SetoidList.transpose2].

      Secondly, instead of the equation above, we now use a statement
      with more basic equalities, allowing to prove [fold_commutes] even
      when [f] isn't a morphism.
      NB: When [f] is a morphism, [Diamond f] gives back the equation above.
*)

  Definition Diamond :=
    forall k k' e e' a b b', ~K.eq k k' ->
      eqA (f k e a) b -> eqA (f k' e' a) b' -> eqA (f k e b') (f k' e' b).
  Variable (Hf' : Diamond).

  Lemma fold_commutes i m k e :
   ~In k m -> eqA (fold f m (f k e i)) (f k e (fold f m i)).
  Proof using st Hf'.
  intros NI.
  apply fold_rel with (R:= fun a b => eqA a (f k e b)); auto.
  - reflexivity.
  - intros k' e' b a Hm K.
    apply Hf' with a; try easy.
    contradict NI; rewrite <- NI. now exists e'.
  Qed.

  Hint Resolve NoDupA_eqk_eqke NoDupA_rev bindings_3w : map.

  Instance fold_Proper : Proper (Equal==>eqA==>eqA) (fold f).
  Proof using st Hf Hf'.
  intros m1 m2 Hm i j Hi.
  rewrite 2 fold_spec_right.
  assert (NoDupA eqk (rev (bindings m1))) by auto with *.
  assert (NoDupA eqk (rev (bindings m2))) by auto with *.
  apply fold_right_equivlistA_restr2 with (R:=complement eqk)(eqA:=eqke)
  ; auto with *.
  - intros (k1,e1) (k2,e2) (Hk,He) a1 a2 Ha; simpl in *. now apply Hf.
  - unfold complement, eq_key, eq_key_elt, Duo,Fst.
    repeat red. intuition eauto with map.
  - intros (k,e) (k',e') z z' h h'; unfold eq_key, uncurry;simpl; auto.
    rewrite h'. eapply Hf'; now eauto.
  - rewrite <- NoDupA_altdef; auto.
  - intros (k,e).
    rewrite 2 InA_rev, <- 2 bindings_mapsto_iff, 2 find_mapsto_iff, Hm;
      auto with *.
  Qed.

  Lemma fold_Add m1 m2 k e i :
   ~In k m1 -> Add k e m1 m2 ->
   eqA (fold f m2 i) (f k e (fold f m1 i)).
  Proof using st Hf Hf'.
  intros Hm1 Hm2.
  rewrite 2 fold_spec_right.
  set (f':=uncurry f).
  change (f k e (fold_right f' i (rev (bindings m1))))
   with (f' (k,e) (fold_right f' i (rev (bindings m1)))).
  assert (NoDupA eqk (rev (bindings m1))) by (auto with * ).
  assert (NoDupA eqk (rev (bindings m2))) by (auto with * ).
  apply fold_right_add_restr with
   (R:=complement eqk)(eqA:=eqke); auto with *.
  - intros (k1,e1) (k2,e2) (Hk,He) a a' Ha; unfold f'; simpl in *. now apply Hf.
  - unfold complement, eq_key_elt, eq_key, Duo, Fst.
    repeat red; intuition eauto with map.
  - intros (k1,e1) (k2,e2) z1 z2; unfold eq_key, f', uncurry, Fst; simpl.
    eapply Hf'; now eauto.
  - rewrite <- NoDupA_altdef; auto.
  - rewrite InA_rev, <- bindings_mapsto_iff by (auto with * ). firstorder.
  - intros (a,b).
    rewrite InA_cons, 2 InA_rev, <- 2 bindings_mapsto_iff,
    2 find_mapsto_iff by (auto with * ).
    unfold eq_key_elt,Duo; simpl.
    rewrite Hm2, !find_spec, add_mapsto_new; intuition.
  Qed.

  Lemma fold_add m k e i :
   ~In k m -> eqA (fold f (add k e m) i) (f k e (fold f m i)).
  Proof using st Hf Hf'.
  intros. now apply fold_Add.
  Qed.

  End Fold_More.

  (** ** Special case of a fold only on keys *)

  Section Fold_Keys.
  Variables (A:Type)(eqA:A->A->Prop)(st:Equivalence eqA).
  Variable (f:key->A->A).
  Variable (Hf:Proper (K.eq==>eqA==>eqA) f).
  Variable (Hf':Diamond eqA (fun k _ => f k)).

  Definition foldkeys := @fold elt A (fun k _ => f k).

  Lemma foldkeys_Empty m i : Empty m -> eqA (foldkeys m i) i.
  Proof.
  now apply fold_Empty.
  Qed.

  Lemma foldkeys_init m i i' :
    eqA i i' -> eqA (foldkeys m i) (foldkeys m i').
  Proof using Hf.
  intros Hi. apply fold_rel with (R:=eqA); auto.
  intros. now apply Hf.
  Qed.

  Lemma foldkeys_commutes i m k :
   ~In k m -> eqA (foldkeys m (f k i)) (f k (foldkeys m i)).
  Proof using st Hf'.
  intros NI.
  apply fold_rel with (R:= fun a b => eqA a (f k b)); auto.
  - reflexivity.
  - intros k' e' b a Hm K.
    set (g := fun _ _ => _) in Hf'.
    change (f k') with (g k' e'). change (f k) with (g k e').
    apply Hf' with a; try easy.
    contradict NI. rewrite <- NI. now exists e'.
  Qed.

  Lemma foldkeys_Proper : Proper (Eqdom==>eqA==>eqA) foldkeys.
  Proof using st Hf Hf'.
  intros m1 m2 Hm i j Hi.
  unfold foldkeys.
  rewrite 2 fold_spec_right.
  assert (NoDupA eqk (rev (bindings m1))).
  { apply NoDupA_rev; auto with *. apply bindings_spec2w. }
  assert (NoDupA eqk (rev (bindings m2))).
  { apply NoDupA_rev; auto with *. apply bindings_spec2w. }
  apply fold_right_equivlistA_restr2 with (R:=complement eqk)(eqA:=eqk)
  ; auto with *.
  - intros (k1,e1) (k2,e2) Hk a1 a2 Ha; simpl in *. now apply Hf.
  - unfold complement, eq_key, eq_key_elt; repeat red. intuition eauto with map.
    compute. simpl in *.
    red in Hf'. eapply (@Hf' a a0); eauto.
    eapply Hf; eauto; easy.
    eapply Hf; eauto; easy.
  - rewrite <- NoDupA_altdef; auto.
  - intros (k,e).
    rewrite 2 InA_rev. specialize (Hm k).
    now rewrite <- !in_bindings_iff'.
  Qed.

  Lemma foldkeys_Add m1 m2 k e i :
   ~In k m1 -> Add k e m1 m2 ->
    eqA (foldkeys m2 i) (f k (foldkeys m1 i)).
  Proof using st Hf Hf'.
  intros Hm1 Hm2.
  unfold foldkeys.
  set (g := fun _ _ => _) in Hf'.
  change (f k) with (g k e).
  apply fold_Add; auto.
  clear - Hf. intros k k' Hk _ _ _ a a' Ha. now apply Hf.
  Qed.

  End Fold_Keys.

  (** * Cardinal *)

  Lemma cardinal_fold m :
   cardinal m = fold (fun _ _ => S) m 0.
  Proof.
  rewrite cardinal_1, fold_1.
  symmetry; apply fold_left_length; auto.
  Qed.

  Lemma cardinal_foldkeys m :
   cardinal m = foldkeys (fun _ => S) m 0.
  Proof.
  apply cardinal_fold.
  Qed.

  Lemma cardinal_Empty m :
   Empty m <-> cardinal m = 0.
  Proof.
  intros.
  rewrite cardinal_1, bindings_Empty.
  destruct (bindings m); intuition; discriminate.
  Qed.

  Lemma Eqdom_cardinal m m' :
    Eqdom m m' -> cardinal m = cardinal m'.
  Proof.
  intro. rewrite 2 cardinal_foldkeys.
  apply foldkeys_Proper with (eqA:=eq); try congruence; auto with map.
  Qed.

  Global Instance cardinal_m :
    Proper (Eqdom ==> Logic.eq) (@cardinal elt).
  Proof.
  intros m m' Hm. now apply Eqdom_cardinal.
  Qed.

  Lemma Equal_cardinal m m' :
    m == m' -> cardinal m = cardinal m'.
  Proof.
  intros. now rewrite H.
  Qed.

  Lemma cardinal_0 m : Empty m -> cardinal m = 0.
  Proof.
  intros; rewrite <- cardinal_Empty; auto.
  Qed.

  Lemma cardinal_empty : cardinal (@empty elt) = 0.
  Proof.
  apply cardinal_0. apply empty_1.
  Qed.

  Lemma cardinal_S m m' x e :
    ~ In x m -> Add x e m m' -> cardinal m' = S (cardinal m).
  Proof.
  intros. rewrite 2 cardinal_foldkeys.
  change S with ((fun _ => S) x).
  eapply foldkeys_Add with (eqA:=eq); eauto with *; congruence.
  Qed.

  Lemma cardinal_notin_add m x e :
    ~In x m -> cardinal (add x e m) = S (cardinal m).
  Proof.
  intros NI. eapply cardinal_S; eauto using Add_add.
  Qed.

  Lemma Eqdom_in_add m x e : In x m -> Eqdom m (add x e m).
  Proof.
  intros IN k. rewrite add_in_iff. split; auto. intros [E|IN']; auto.
  now rewrite <- E.
  Qed.

  Lemma cardinal_In_Add m m' x e :
    In x m -> Add x e m m' -> cardinal m' = cardinal m.
  Proof.
  intros IN AD. apply Eqdom_cardinal. apply Equal_Eqdom in AD.
  rewrite AD. now rewrite <- Eqdom_in_add.
  Qed.

  Lemma cardinal_in_add m x e :
    In x m -> cardinal (add x e m) = cardinal m.
  Proof.
  intros IN. eapply cardinal_In_Add; eauto using Add_add.
  Qed.

  Lemma cardinal_inv_1 m : cardinal m = 0 -> Empty m.
  Proof.
  intros; rewrite cardinal_Empty; auto.
  Qed.
  Hint Resolve cardinal_inv_1 : map.

  Lemma cardinal_inv_2 m n :
   cardinal m = S n -> { p : key*elt | MapsTo (fst p) (snd p) m }.
  Proof.
  intros; rewrite M.cardinal_spec in *.
  generalize (bindings_mapsto_iff m).
  destruct (bindings m); try discriminate.
  exists p; auto.
  rewrite H0; destruct p; simpl; auto.
  constructor; compute; auto with map.
  Qed.

  Lemma cardinal_inv_2b m :
   cardinal m <> 0 -> { p : key*elt | MapsTo (fst p) (snd p) m }.
  Proof.
  intros.
  generalize (@cardinal_inv_2 m); destruct cardinal.
  elim H;auto.
  eauto.
  Qed.

  Lemma cardinal_inv_in m : cardinal m <> 0 -> { k | In k m }.
  Proof.
  intros H. destruct (cardinal_inv_2b H) as ((k,e),M). simpl in *.
  exists k. now exists e.
  Qed.

  Lemma not_empty_mapsto m : ~Empty m -> exists k e, MapsTo k e m.
  Proof.
  intro.
  destruct (@cardinal_inv_2b m) as ((k,e),H').
  contradict H. now apply cardinal_inv_1.
  exists k; now exists e.
  Qed.

  Lemma not_empty_in m : ~Empty m -> exists k, In k m.
  Proof.
  intro. destruct (not_empty_mapsto H) as (k,Hk).
  now exists k.
  Qed.

  Lemma is_empty_bindings m : is_empty m = true <-> bindings m = nil.
  Proof.
  rewrite <- is_empty_iff, cardinal_Empty, cardinal_spec.
  now destruct bindings.
  Qed.

  Lemma is_empty_no_binding m :
    is_empty m = true <-> (forall x e, ~List.In (x,e) (bindings m)).
  Proof.
  rewrite is_empty_bindings.
  destruct (bindings m) as [|(x,e) l]; simpl; firstorder. easy.
  destruct (H x e). now left.
  Qed.

  Lemma not_empty_has_binding m :
    is_empty m = false <-> (exists x e, List.In (x,e) (bindings m)).
  Proof.
  rewrite <- not_true_iff_false, is_empty_bindings.
  destruct (bindings m) as [|(x,e) l]; simpl; firstorder; try congruence.
  exists x, e. now left.
  Qed.

  (** * Properties about filter, partition, for_all, exists_ *)

  (** First, alternative formulations, e.g. based on fold,
      or on filter for the other operations *)

  Lemma filter_alt (f:key->elt->bool) m :
    filter f m == fold (fun k e m => if f k e then add k e m else m) m empty.
  Proof.
  intros x.
  rewrite fold_spec_right, bindings_o, filter_spec.
  rewrite findA_rev, filter_rev by apply NoDupA_filter, bindings_spec2w.
  change K.t with key in *.
  induction (rev (bindings m)) as [|(y,e) l IH]; simpl.
  - now rewrite empty_o.
  - unfold uncurry at 1; simpl.
    destruct (f y e) eqn:E; simpl; auto.
    unfold eqb at 1. destruct K.eq_dec as [->|NE].
    + now rewrite add_spec1.
    + rewrite add_spec2; auto. now contradict NE.
  Qed.

  Lemma for_all_alt (f:key->elt->bool) m :
   for_all f m = is_empty (filter (fun k e => negb (f k e)) m).
  Proof.
   apply eq_bool_alt.
   rewrite for_all_spec, forallb_forall, is_empty_no_binding.
   setoid_rewrite filter_spec. setoid_rewrite filter_In. split.
   - intros H x e (IN,E). now rewrite (H (x,e)) in E.
   - intros H (x,e) IN. specialize (H x e). destruct (f x e) eqn:F; auto.
  Qed.

  Lemma for_all_alt2 (f : key -> elt -> bool) m :
    for_all f m = fold (fun k e b => if f k e then b else false) m true.
  Proof.
  rewrite for_all_spec, fold_spec_right, <- forallb_rev.
  induction (rev (bindings m)) as [|(x,e) l IH]; simpl; auto.
  unfold uncurry at 1; simpl. destruct f; simpl; auto.
  Qed.

  Lemma exists_alt (f:key->elt->bool) m :
   exists_ f m = negb (is_empty (filter f m)).
  Proof.
   apply eq_bool_alt.
   rewrite exists_spec, existsb_exists, negb_true_iff, not_empty_has_binding.
   setoid_rewrite filter_spec. setoid_rewrite filter_In. split.
   - intros ((x,e) & IN & E). firstorder.
   - intros (x & e & IN & E). now exists (x,e).
  Qed.

  Lemma exists_alt2 (f : key -> elt -> bool) m :
    exists_ f m = fold (fun k e b => if f k e then true else b) m false.
  Proof.
  rewrite exists_spec, fold_spec_right, <- existsb_rev.
  induction (rev (bindings m)) as [|(x,e) l IH]; simpl; auto.
  unfold uncurry at 1; simpl. destruct f; simpl; auto.
  Qed.

  Lemma partition_alt1 (f:key->elt->bool) m :
   fst (partition f m) == filter f m.
  Proof.
   intros k. rewrite !bindings_o. f_equal.
   replace (bindings (fst _)) with
          (fst (prodmap (@bindings _) (partition f m)))
     by now destruct partition.
   now rewrite partition_spec, filter_spec, partition_filter.
  Qed.

  Lemma partition_alt2 (f:key->elt->bool) m :
   snd (partition f m) == filter (fun k e => negb (f k e)) m.
  Proof.
   intros k. rewrite !bindings_o. f_equal.
   replace (bindings (snd _)) with
          (snd (prodmap (@bindings _) (partition f m)))
     by now destruct partition.
   rewrite partition_spec, filter_spec, partition_filter.
   simpl. apply filter_ext; auto. now intros (x,e).
  Qed.

  (** Morphisms *)

  Global Instance filter_m :
   Proper ((K.eq==>eq==>eq)==>Equal==>Equal) (@filter elt).
  Proof.
  intros f f' Hf m m' Hm k.
  apply eq_option_alt. intros e.
  rewrite !find_spec, <- !bindings_spec1, !filter_spec, !InA_alt.
  setoid_rewrite filter_In. split.
  - intros ((x,e') & (H,H') & IN & F). simpl in *. subst e'.
    assert (FD : find x m = Some e).
    { apply find_spec, bindings_spec1, InA_alt. now exists (x,e). }
    rewrite Hm in FD.
    apply find_spec, bindings_spec1, InA_alt in FD.
    destruct FD as ((x',e') & (H',H2) & IN'). simpl in *; subst e'.
    exists (x',e). repeat split; auto. simpl; eauto with *.
    rewrite <- F. symmetry. now apply Hf.
  - intros ((x,e') & (H,H') & IN & F). simpl in *. subst e'.
    assert (FD : find x m' = Some e).
    { apply find_spec, bindings_spec1, InA_alt. now exists (x,e). }
    rewrite <- Hm in FD.
    apply find_spec, bindings_spec1, InA_alt in FD.
    destruct FD as ((x',e') & (H',H2) & IN'). simpl in *; subst e'.
    exists (x',e). repeat split; auto. simpl; eauto with *.
    rewrite <- F. now apply Hf.
  Qed.

  Global Instance for_all_m :
   Proper ((K.eq==>Logic.eq==>Logic.eq)==>Equal==>Logic.eq) (@for_all elt).
  Proof.
  intros f f' Hf m m' Hm.
  rewrite !for_all_alt. apply is_empty_m, Equal_Eqdom, filter_m; auto.
  intros x x' Hx e e' <-. f_equal. now apply Hf.
  Qed.

  Global Instance exists_m :
   Proper ((K.eq==>Logic.eq==>Logic.eq)==>Equal==>Logic.eq) (@exists_ elt).
  Proof.
  intros f f' Hf m m' Hm.
  rewrite !exists_alt. f_equal.
  apply is_empty_m, Equal_Eqdom, filter_m; auto.
  Qed.

  (** Statements in terms of MapsTo or find. *)

  Lemma filter_iff (f : key -> elt -> bool) :
    Proper (K.eq==>eq==>eq) f ->
    forall m k e,
      MapsTo k e (filter f m) <-> MapsTo k e m /\ f k e = true.
  Proof.
  intros E m k e. rewrite <- !bindings_spec1, filter_spec, !InA_alt.
  setoid_rewrite filter_In. firstorder.
  - destruct x as (k',e'); simpl in *; subst. rewrite E; eauto.
  - destruct x as (k',e'); simpl in *; subst. exists (k',e').
    split. easy. split; auto. rewrite <- E; eauto.
  Qed.

  Lemma filter_find (f : key -> elt -> bool) :
    Proper (K.eq==>eq==>eq) f ->
    forall m x,
      find x (filter f m) =
      option_bind (find x m) (fun e => if f x e then Some e else None).
  Proof.
  intros E m x. apply eq_option_alt. intros e.
  rewrite find_spec, filter_iff, <- find_spec; auto.
  split.
  - intros (-> & H'). simpl. now rewrite H'.
  - destruct (find x m); simpl; try easy.
    destruct f eqn:F; simpl; try easy. now intros [= ->].
  Qed.

  Lemma partition_iff1 (f:key->elt->bool) :
    Proper (K.eq==>eq==>eq) f ->
    forall m k e,
    MapsTo k e (fst (partition f m)) <-> MapsTo k e m /\ f k e = true.
  Proof.
  intros. rewrite partition_alt1. now apply filter_iff.
  Qed.

  Lemma partition_iff2 (f:key->elt->bool) :
    Proper (K.eq==>eq==>eq) f ->
    forall m k e,
    MapsTo k e (snd (partition f m)) <-> MapsTo k e m /\ f k e = false.
  Proof.
  intros. rewrite partition_alt2. rewrite filter_iff.
  now rewrite negb_true_iff.
  clear -H. intros x x' Hx e e' <-. f_equal. now apply H.
  Qed.

  Lemma for_all_iff (f:key->elt->bool) :
    Proper (K.eq==>eq==>eq) f ->
    forall m,
      for_all f m = true <-> (forall x e, MapsTo x e m -> f x e = true).
  Proof.
  intros Hf m. rewrite for_all_spec, forallb_forall. split.
  - intros H x e. rewrite <- bindings_spec1, InA_alt.
    intros ((y,e') & (H1,H2) & IN). simpl in *; subst e'.
    specialize (H (y,e) IN). simpl in *. rewrite <- Hf; eauto with *.
  - intros H (x,e) IN. apply H. rewrite <- bindings_spec1, InA_alt.
    now exists (x,e).
  Qed.

  Lemma exists_iff (f:key->elt->bool) :
    Proper (K.eq==>eq==>eq) f ->
    forall m,
      exists_ f m = true <-> (exists x e, MapsTo x e m /\ f x e = true).
  Proof.
  intros Hf m. rewrite exists_spec, existsb_exists. split.
  - intros ((x,e) & IN & E). exists x, e; split; auto.
    rewrite <- bindings_spec1, InA_alt; now exists (x,e).
  - intros (x & e & IN & E).
    rewrite <- bindings_spec1, InA_alt in IN.
    destruct IN as ((y,e') & (H1,H2) & IN). simpl in *; subst e'.
    exists (y,e). split; auto. rewrite <- Hf; eauto with *.
  Qed.

  (** specialized versions analyzing only keys (resp. bindings) *)

  Definition filter_dom (f : key -> bool) := filter (fun k e => f k).
  Definition filter_range (f : elt -> bool) := filter (fun k => f).
  Definition for_all_dom (f : key -> bool) := for_all (fun k e => f k).
  Definition for_all_range (f : elt -> bool) := for_all (fun k => f).
  Definition exists_dom (f : key -> bool) := exists_ (fun k e => f k).
  Definition exists_range (f : elt -> bool) := exists_ (fun k => f).
  Definition partition_dom (f : key -> bool) := partition (fun k e => f k).
  Definition partition_range (f : elt -> bool) := partition (fun k => f).

  (** * Extra predicates on maps : Disjoint and Partition *)

  Definition Disjoint m m' := forall k, ~(In k m /\ In k m').

  Definition Partition m m1 m2 :=
    Disjoint m1 m2 /\
    (forall k e, MapsTo k e m <-> MapsTo k e m1 \/ MapsTo k e m2).

  Global Instance Disjoint_m : Proper (Eqdom ==> Eqdom ==> iff) Disjoint.
  Proof.
  intros m1 m1' Hm1 m2 m2' Hm2. unfold Disjoint. split; intros.
  rewrite <- Hm1, <- Hm2; auto.
  rewrite Hm1, Hm2; auto.
  Qed.

  Global Instance Partition_m :
   Proper (Equal ==> Equal ==> Equal ==> iff) Partition.
  Proof.
  intros m1 m1' Hm1 m2 m2' Hm2 m3 m3' Hm3. unfold Partition.
  rewrite <- Hm2, <- Hm3.
  split; intros (H,H'); split; auto; intros.
  rewrite <- Hm1, <- Hm2, <- Hm3; auto.
  rewrite Hm1, Hm2, Hm3; auto.
  Qed.

  Lemma Disjoint_alt : forall m m',
   Disjoint m m' <->
   (forall k e e', MapsTo k e m -> MapsTo k e' m' -> False).
  Proof.
  unfold Disjoint; split.
  intros H k v v' H1 H2.
  apply H with k; split.
  exists v; trivial.
  exists v'; trivial.
  intros H k ((v,Hv),(v',Hv')).
  eapply H; eauto.
  Qed.

  Lemma partition_Partition (f:key->elt->bool) :
   (Proper (K.eq==>eq==>eq) f) ->
   forall m m1 m2, partition f m = (m1,m2) -> Partition m m1 m2.
  Proof.
  intros Hf m m1 m2 E.
  replace m1 with (fst (partition f m)) by now rewrite E.
  replace m2 with (snd (partition f m)) by now rewrite E. clear E.
  split.
  - rewrite Disjoint_alt. intros k e e'.
    rewrite partition_iff1, partition_iff2; auto.
    intros (U,V) (W,Z). rewrite <- (mapsto_fun U W) in Z; congruence.
  - intros k e. rewrite partition_iff1, partition_iff2; auto.
    intuition. destruct (f k e); intuition.
  Qed.

  Lemma Partition_In m m1 m2 k :
   Partition m m1 m2 -> In k m -> {In k m1}+{In k m2}.
  Proof.
  intros Hm Hk.
  destruct (In_dec m1 k) as [H|H]; [left|right]; auto.
  destruct Hm as (Hm,Hm').
  destruct Hk as (e,He); rewrite Hm' in He; destruct He.
  elim H; exists e; auto.
  exists e; auto.
  Defined.

  Lemma Disjoint_sym m1 m2 : Disjoint m1 m2 -> Disjoint m2 m1.
  Proof.
  intros H k (H1,H2). elim (H k); auto.
  Qed.

  Lemma Partition_sym m m1 m2 : Partition m m1 m2 -> Partition m m2 m1.
  Proof.
  intros (H,H'); split.
  apply Disjoint_sym; auto.
  intros; rewrite H'; intuition.
  Qed.

  Lemma Partition_Empty m m1 m2 : Partition m m1 m2 ->
   (Empty m <-> Empty m1 /\ Empty m2).
  Proof.
  intros (Hdisj,Heq). split.
  intro He.
  split; intros k e Hke; elim (He k e); rewrite Heq; auto.
  intros (He1,He2) k e Hke. rewrite Heq in Hke. destruct Hke.
  elim (He1 k e); auto.
  elim (He2 k e); auto.
  Qed.

  Lemma Partition_Add :
    forall m m' x e , ~In x m -> Add x e m m' ->
    forall m1 m2, Partition m' m1 m2 ->
     exists m3, (Add x e m3 m1 /\ Partition m m3 m2 \/
                 Add x e m3 m2 /\ Partition m m1 m3).
  Proof.
  unfold Partition. intros m m' x e Hn Hadd m1 m2 (Hdisj,Hor).
  assert (Heq : m == remove x m').
  { change (m' == add x e m) in Hadd. rewrite Hadd.
    intro k. rewrite remove_o, add_o.
    destruct K.eq_dec as [He|Hne]; auto.
    rewrite <- He, <- not_find_in_iff; auto. }
  assert (H : MapsTo x e m').
  { change (m' == add x e m) in Hadd; rewrite Hadd.
    apply add_1; auto with map. }
  rewrite Hor in H; destruct H.

  - (* first case : x in m1 *)
    exists (remove x m1); left. split; [|split].
    + (* add *)
      change (m1 == add x e (remove x m1)).
      intro k.
      rewrite add_o, remove_o.
      destruct K.eq_dec as [He|Hne]; auto.
      rewrite <- He; apply find_1; auto.
    + (* disjoint *)
      intros k (H1,H2). elim (Hdisj k). split; auto.
      rewrite remove_in_iff in H1; destruct H1; auto.
    + (* mapsto *)
      intros k' e'.
      rewrite Heq, 2 remove_mapsto_iff, Hor.
      intuition.
      elim (Hdisj x); split; [exists e|exists e']; auto.
      apply MapsTo_1 with k'; auto with map.

  - (* second case : x in m2 *)
    exists (remove x m2); right. split; [|split].
    + (* add *)
      change (m2 == add x e (remove x m2)).
      intro k.
      rewrite add_o, remove_o.
      destruct K.eq_dec as [He|Hne]; auto.
      rewrite <- He; apply find_1; auto.
    + (* disjoint *)
      intros k (H1,H2). elim (Hdisj k). split; auto.
      rewrite remove_in_iff in H2; destruct H2; auto.
    + (* mapsto *)
      intros k' e'.
      rewrite Heq, 2 remove_mapsto_iff, Hor.
      intuition.
      elim (Hdisj x); split; [exists e'|exists e]; auto.
      apply MapsTo_1 with k'; auto with map.
  Qed.

  Lemma Partition_fold :
   forall {A}(eqA:A->A->Prop)(st:Equivalence eqA)(f:key->elt->A->A),
   Proper (K.eq==>eq==>eqA==>eqA) f ->
   Diamond eqA f ->
   forall m m1 m2 i,
   Partition m m1 m2 ->
   eqA (fold f m i) (fold f m1 (fold f m2 i)).
  Proof.
  intros A eqA st f Comp Tra.
  induction m as [m Hm|m m' IH k e Hn Hadd] using map_induction.

  - intros m1 m2 i Hp. rewrite (fold_Empty (eqA:=eqA)); auto.
    rewrite (Partition_Empty Hp) in Hm. destruct Hm.
    rewrite 2 (fold_Empty (eqA:=eqA)); auto. reflexivity.

  - intros m1 m2 i Hp.
    destruct (Partition_Add Hn Hadd Hp) as (m3,[(Hadd',Hp')|(Hadd',Hp')]).
    + (* fst case: m3 is (k,e)::m1 *)
      assert (~In k m3).
      { contradict Hn. destruct Hn as (e',He').
        destruct Hp' as (Hp1,Hp2). exists e'. rewrite Hp2; auto. }
      transitivity (f k e (fold f m i)).
      apply fold_Add with (eqA:=eqA); auto.
      symmetry.
      transitivity (f k e (fold f m3 (fold f m2 i))).
      apply fold_Add with (eqA:=eqA); auto.
      apply Comp; auto with map.
      symmetry; apply IH; auto.
    + (* snd case: m3 is (k,e)::m2 *)
      assert (~In k m3).
      { contradict Hn. destruct Hn as (e',He').
        destruct Hp' as (Hp1,Hp2). exists e'. rewrite Hp2; auto. }
      assert (~In k m1).
      { contradict Hn. destruct Hn as (e',He').
        destruct Hp' as (Hp1,Hp2). exists e'. rewrite Hp2; auto. }
      transitivity (f k e (fold f m i)).
      apply fold_Add with (eqA:=eqA); auto.
      transitivity (f k e (fold f m1 (fold f m3 i))).
      apply Comp; auto using IH with map.
      transitivity (fold f m1 (f k e (fold f m3 i))).
      symmetry.
      apply fold_commutes with (eqA:=eqA); auto.
      apply fold_init with (eqA:=eqA); auto.
      symmetry.
      apply fold_Add with (eqA:=eqA); auto.
  Qed.

  Lemma Partition_cardinal m m1 m2 : Partition m m1 m2 ->
   cardinal m = cardinal m1 + cardinal m2.
  Proof.
  intros.
  rewrite (cardinal_fold m), (cardinal_fold m1).
  set (f:=fun (_:key)(_:elt)=>S).
  setoid_replace (fold f m 0) with (fold f m1 (fold f m2 0)).
  rewrite <- cardinal_fold.
  apply fold_rel with (R:=fun u v => u = v + cardinal m2); simpl; auto.
  apply Partition_fold with (eqA:=eq); compute; auto with map. congruence.
  Qed.

  Lemma Partition_partition m m1 m2 : Partition m m1 m2 ->
    let f := fun k _ => mem k m1 in
   m1 == fst (partition f m) /\ m2 == snd (partition f m).
  Proof.
  intros Hm f.
  assert (Hf : Proper (K.eq==>eq==>eq) f).
  { intros k k' Hk e e' _; unfold f; rewrite Hk; auto. }
  split; rewrite Equal_mapsto_iff; intros k e.
  - rewrite partition_iff1; auto. unfold f.
    rewrite <- mem_in_iff. destruct Hm as (Hm,->). firstorder.
  - rewrite partition_iff2; auto. unfold f.
    rewrite <- not_mem_in_iff. destruct Hm as (Hm,->). firstorder.
  Qed.

  (** * Emulation of some functions lacking in the interface *)

  (** [update] now mimics the one of OCaml : [update x f m] returns a map
      containing the same bindings as m, except for the binding of
      x. Depending on the value of y where y is [f (find x m)], the
      binding of x is added, removed or updated. If y is None, the
      binding is removed if it exists; otherwise, if y is [Some z] then
      x is associated to z in the resulting map.
      Note : A direct implementation could do that in one tree traversal,
      here we're doing that in two, without garantee on physical equality *)

  Definition update (x:key)(f : option elt -> option elt) m :=
   match f (find x m) with
   | Some e => add x e m
   | None => remove x m
   end.

  (** [union] mimics the OCaml operation : [union f m1 m2] computes a
      map whose keys is the union of keys of m1 and of m2. When the same
      binding is defined in both arguments, the function f is used to
      combine them. This is a special case of merge. *)

  Definition union (f : key -> elt -> elt -> option elt) :=
    let f' := fun k o1 o2 =>
                match o1,o2 with
                | Some v1, Some v2 => f k v1 v2
                | o,None | None,o => o
                end
    in
    merge f'.

  (** [extend] adds to [m1] all the bindings of [m2]. It can be seen as
     an [union] operator which gives priority to its 2nd argument
     in case of binding conflit. *)

  Definition extend m1 m2 := fold (@add _) m2 m1.

  (** [restrict] keeps from [m1] only the bindings whose key is in [m2].
      It can be seen as an [inter] operator, with priority to its 1st argument
      in case of binding conflit. *)

  Definition restrict m1 m2 := filter (fun k _ => mem k m2) m1.

  (** [diff] erases from [m1] all bindings whose key is in [m2]. *)

  Definition diff m1 m2 := filter (fun k _ => negb (mem k m2)) m1.

  (** Properties of these abbreviations *)

  Lemma update_spec1 (f:option elt->option elt) m x :
   find x (update x f m) = f (find x m).
  Proof.
  unfold update. destruct f; [apply add_spec1 | apply remove_spec1].
  Qed.

  Lemma update_spec2 (f:option elt->option elt) m x y :
   ~K.eq x y -> find y (update x f m) = find y m.
  Proof.
  intros NE. unfold update.
  destruct f; [apply add_spec2 | apply remove_spec2]; auto.
  Qed.

  Global Instance update_m : Proper (K.eq==>(eq==>eq)==>Equal==>Equal) update.
  Proof.
  intros x x' Hx f f' Hf m m' Hm. unfold update.
  rewrite <- Hx. rewrite <- Hm at 1. rewrite <- (Hf (find x m)) by auto.
  destruct f; f_equiv; auto.
  Qed.

  Lemma union_spec (f:key->elt->elt->option elt) m1 m2 x :
    Proper (K.eq==>eq==>eq==>eq) f ->
    find x (union f m1 m2) =
    match find x m1, find x m2 with
    | Some e1, Some e2 => f x e1 e2
    | o,None | None,o => o
    end.
  Proof.
  intros Hf. unfold union. rewrite merge_spec1mn; auto.
  - destruct find, find; auto.
  - clear x. intros x x' Hx o1 o1' <- o2 o2' <-.
    destruct o1, o2; auto. apply Hf; auto.
  Qed.

  Global Instance union_m :
    Proper ((K.eq==>eq==>eq==>eq)==>Equal==>Equal==>Equal) union.
  Proof.
  intros f f' Hf m1 m1' Hm1 m2 m2' Hm2. unfold union.
  f_equiv; auto. clear -Hf. intros x x' Hx o1 o1' <- o2 o2' <-.
  destruct o1, o2; auto. apply Hf; auto.
  Qed.

  Lemma extend_mapsto_iff : forall m m' k e,
   MapsTo k e (extend m m') <->
    (MapsTo k e m' \/ (MapsTo k e m /\ ~In k m')).
  Proof.
  unfold extend.
  intros m m'.
  pattern m', (fold (@add _) m' m). apply fold_rec.
  - intros m0 Hm0 k e.
    assert (~In k m0) by (intros (e0,He0); apply (Hm0 k e0); auto).
    intuition.
    elim (Hm0 k e); auto.
  - intros k e m0 m1 m2 _ Hn Hadd IH k' e'.
    change (m2 == add k e m1) in Hadd.
    rewrite Hadd, 2 add_mapsto_iff, IH, add_in_iff. clear IH. intuition.
  Qed.

  Lemma extend_dec : forall m m' k e, MapsTo k e (extend m m') ->
   { MapsTo k e m' } + { MapsTo k e m /\ ~In k m'}.
  Proof.
  intros m m' k e H. rewrite extend_mapsto_iff in H.
  destruct (In_dec m' k) as [H'|H']; [left|right]; intuition.
  elim H'; exists e; auto.
  Defined.

  Lemma extend_in_iff : forall m m' k,
   In k (extend m m') <-> In k m \/ In k m'.
  Proof.
  intros m m' k. split.
  intros (e,H); rewrite extend_mapsto_iff in H.
  destruct H; [right|left]; exists e; intuition.
  destruct (In_dec m' k) as [H|H].
  destruct H as (e,H). intros _; exists e.
  rewrite extend_mapsto_iff; left; auto.
  destruct 1 as [H'|H']; [|elim H; auto].
  destruct H' as (e,H'). exists e.
  rewrite extend_mapsto_iff; right; auto.
  Qed.

  Lemma diff_mapsto_iff : forall m m' k e,
   MapsTo k e (diff m m') <-> MapsTo k e m /\ ~In k m'.
  Proof.
  intros m m' k e.
  unfold diff.
  rewrite filter_iff.
  intuition.
  rewrite mem_1 in *; auto; discriminate.
  intros ? ? Hk _ _ _; rewrite Hk; auto.
  Qed.

  Lemma diff_in_iff : forall m m' k,
   In k (diff m m') <-> In k m /\ ~In k m'.
  Proof.
  intros m m' k. split.
  intros (e,H); rewrite diff_mapsto_iff in H.
  destruct H; split; auto. exists e; auto.
  intros ((e,H),H'); exists e; rewrite diff_mapsto_iff; auto.
  Qed.

  Lemma restrict_mapsto_iff : forall m m' k e,
   MapsTo k e (restrict m m') <-> MapsTo k e m /\ In k m'.
  Proof.
  intros m m' k e.
  unfold restrict.
  rewrite filter_iff.
  intuition.
  intros ? ? Hk _ _ _; rewrite Hk; auto.
  Qed.

  Lemma restrict_in_iff : forall m m' k,
   In k (restrict m m') <-> In k m /\ In k m'.
  Proof.
  intros m m' k. split.
  intros (e,H); rewrite restrict_mapsto_iff in H.
  destruct H; split; auto. exists e; auto.
  intros ((e,H),H'); exists e; rewrite restrict_mapsto_iff; auto.
  Qed.

 End Elt.

 Fact diamond_add {elt} : Diamond Equal (@add elt).
 Proof.
  intros k k' e e' a b b' Hk <- <-. now apply add_add_2.
 Qed.

 Global Instance extend_m {elt} : Proper (Equal ==> Equal ==> Equal) (@extend elt).
 Proof.
  intros m1 m1' Hm1 m2 m2' Hm2.
  unfold extend.
  apply fold_Proper; auto using diamond_add with *.
 Qed.

 Global Instance restrict_m {elt} : Proper (Equal==>Equal==>Equal) (@restrict elt).
 Proof.
  intros m1 m1' Hm1 m2 m2' Hm2 y.
  unfold restrict.
  apply eq_option_alt. intros e.
  rewrite !find_spec, !filter_iff, Hm1, Hm2. reflexivity.
  clear. intros x x' Hx e e' He. now rewrite Hx.
  clear. intros x x' Hx e e' He. now rewrite Hx.
 Qed.

 Global Instance diff_m {elt} : Proper (Equal==>Equal==>Equal) (@diff elt).
 Proof.
  intros m1 m1' Hm1 m2 m2' Hm2 y.
  unfold diff.
  apply eq_option_alt. intros e.
  rewrite !find_spec, !filter_iff, Hm1, Hm2. reflexivity.
  clear. intros x x' Hx e e' He. now rewrite Hx.
  clear. intros x x' Hx e e' He. now rewrite Hx.
 Qed.

End Properties.

(** * Properties specific to maps with ordered keys *)

Module OrdProperties (K:OrderedType)(M:S K).
 Module Import F := OrderedTypeFacts K.
 Module Import O := KeyOrderedType K.
 Module Import P := Properties K M.
 Import M.

 Section Elt.
  Variable elt:Type.

  Definition Above x (m:t elt) := forall y, In y m -> K.lt y x.
  Definition Below x (m:t elt) := forall y, In y m -> K.lt x y.

  Section Bindings.

  Lemma bindings_spec2' (m:t elt) : sort ltk (bindings m).
  Proof. apply bindings_spec2. Qed.
  Local Hint Resolve bindings_spec2' : map.

  Lemma sort_equivlistA_eqlistA : forall l l' : list (key*elt),
   sort ltk l -> sort ltk l' -> equivlistA eqke l l' -> eqlistA eqke l l'.
  Proof.
  apply SortA_equivlistA_eqlistA; eauto with *.
  Qed.

  Ltac klean := unfold O.eqke, O.ltk, RelCompFun in *; simpl in *.
  Ltac keauto := klean; intuition; eauto.

  Definition gtb (p p':key*elt) :=
    match K.compare (fst p) (fst p') with Gt => true | _ => false end.
  Definition leb p := fun p' => negb (gtb p p').

  Definition bindings_lt p m := List.filter (gtb p) (bindings m).
  Definition bindings_ge p m := List.filter (leb p) (bindings m).

  Lemma gtb_1 : forall p p', gtb p p' = true <-> ltk p' p.
  Proof.
   intros (x,e) (y,e'); unfold gtb; klean.
   case K.compare_spec; intuition; try discriminate; F.order.
  Qed.

  Lemma leb_1 : forall p p', leb p p' = true <-> ~ltk p' p.
  Proof.
   intros (x,e) (y,e'); unfold leb, gtb; klean.
   case K.compare_spec; intuition; try discriminate; F.order.
  Qed.

  Instance gtb_compat : forall p, Proper (eqke==>eq) (gtb p).
  Proof.
   red; intros (x,e) (a,e') (b,e'') H; red in H; simpl in *; destruct H.
   generalize (gtb_1 (x,e) (a,e'))(gtb_1 (x,e) (b,e''));
    destruct (gtb (x,e) (a,e')); destruct (gtb (x,e) (b,e'')); klean; auto.
   - intros. symmetry; rewrite H2. rewrite <-H, <-H1; auto.
   - intros. rewrite H1. rewrite H, <- H2; auto.
  Qed.

  Instance leb_compat : forall p, Proper (eqke==>eq) (leb p).
  Proof.
   intros x a b H. unfold leb; f_equal; apply gtb_compat; auto.
  Qed.

  Hint Resolve gtb_compat leb_compat bindings_spec2 : map.

  Lemma bindings_split : forall p m,
    bindings m = bindings_lt p m ++ bindings_ge p m.
  Proof.
  unfold bindings_lt, bindings_ge, leb; intros.
  apply filter_split with (eqA:=eqk) (ltA:=ltk); eauto with *.
  intros; destruct x; destruct y; destruct p.
  rewrite gtb_1 in H; klean.
  apply not_true_iff_false in H0. rewrite gtb_1 in H0. klean. F.order.
  Qed.

  Lemma bindings_Add : forall m m' x e, ~In x m -> Add x e m m' ->
    eqlistA eqke (bindings m')
                 (bindings_lt (x,e) m ++ (x,e):: bindings_ge (x,e) m).
  Proof.
  intros; unfold bindings_lt, bindings_ge.
  apply sort_equivlistA_eqlistA; auto with *.
  - apply (@SortA_app _ eqke); auto with *.
    + apply (@filter_sort _ eqke); auto with *; keauto.
    + constructor; auto with map.
      * apply (@filter_sort _ eqke); auto with *; keauto.
      * rewrite (@InfA_alt _ eqke); auto with *; try (keauto; fail).
        { intros.
          rewrite filter_InA in H1; auto with *; destruct H1.
          rewrite leb_1 in H2.
          destruct y; klean.
          rewrite <- bindings_mapsto_iff in H1.
          assert (~K.eq x t0).
          { contradict H.
            exists e0; apply MapsTo_1 with t0; auto.
            F.order. }
          F.order. }
        { apply (@filter_sort _ eqke); auto with *; keauto. }
    + intros.
      rewrite filter_InA in H1; auto with *; destruct H1.
      rewrite gtb_1 in H3.
      destruct y; destruct x0; klean.
      inversion_clear H2.
      * red in H4. klean; destruct H4; simpl in *. F.order.
      * rewrite filter_InA in H4; auto with *; destruct H4.
        rewrite leb_1 in H4. klean; F.order.
  - intros (k,e').
    rewrite InA_app_iff, InA_cons, 2 filter_InA,
      <-2 bindings_mapsto_iff, leb_1, gtb_1,
      find_mapsto_iff, (H0 k), <- find_mapsto_iff,
      add_mapsto_iff by (auto with * ).
    change (eqke (k,e') (x,e)) with (K.eq k x /\ e' = e).
    klean.
    split.
    + intros [(->,->)|(Hk,Hm)].
      * right; now left.
      * destruct (lt_dec k x); intuition.
    + intros [(Hm,LT)|[(->,->)|(Hm,EQ)]].
      * right; split; trivial; F.order.
      * now left.
      * destruct (eq_dec x k) as [Hk|Hk].
        elim H. exists e'. now rewrite Hk.
        right; auto.
  Qed.

  Lemma bindings_Add_Above : forall m m' x e,
   Above x m -> Add x e m m' ->
     eqlistA eqke (bindings m') (bindings m ++ (x,e)::nil).
  Proof.
  intros.
  apply sort_equivlistA_eqlistA; auto with *.
  apply (@SortA_app _ eqke); auto with *.
  intros.
  inversion_clear H2.
  destruct x0; destruct y.
  rewrite <- bindings_mapsto_iff in H1.
  destruct H3; klean.
  rewrite H2.
  apply H; firstorder.
  inversion H3.
  red; intros a; destruct a.
  rewrite InA_app_iff, InA_cons, InA_nil, <- 2 bindings_mapsto_iff,
   find_mapsto_iff, (H0 t0), <- find_mapsto_iff,
   add_mapsto_iff by (auto with *).
  change (eqke (t0,e0) (x,e)) with (K.eq t0 x /\ e0 = e).
  intuition.
  destruct (K.eq_dec x t0) as [Heq|Hneq]; auto.
  exfalso.
  assert (In t0 m) by (exists e0; auto).
  generalize (H t0 H1).
  F.order.
  Qed.

  Lemma bindings_Add_Below : forall m m' x e,
   Below x m -> Add x e m m' ->
     eqlistA eqke (bindings m') ((x,e)::bindings m).
  Proof.
  intros.
  apply sort_equivlistA_eqlistA; auto with *.
  change (sort ltk (((x,e)::nil) ++ bindings m)).
  apply (@SortA_app _ eqke); auto with *.
  intros.
  inversion_clear H1.
  destruct y; destruct x0.
  rewrite <- bindings_mapsto_iff in H2.
  destruct H3; klean.
  rewrite H1.
  apply H; firstorder.
  inversion H3.
  red; intros a; destruct a.
  rewrite InA_cons, <- 2 bindings_mapsto_iff,
    find_mapsto_iff, (H0 t0), <- find_mapsto_iff,
    add_mapsto_iff by (auto with * ).
  change (eqke (t0,e0) (x,e)) with (K.eq t0 x /\ e0 = e).
  intuition.
  destruct (K.eq_dec x t0) as [Heq|Hneq]; auto.
  exfalso.
  assert (In t0 m) by (exists e0; auto).
  generalize (H t0 H1).
  F.order.
  Qed.

  Lemma bindings_Equal_eqlistA (m m' : t elt) :
   m == m' <-> eqlistA eqke (bindings m) (bindings m').
  Proof.
  split; intros.
  - apply sort_equivlistA_eqlistA; auto with *.
    red; intros.
    destruct x; do 2 rewrite <- bindings_mapsto_iff.
    do 2 rewrite find_mapsto_iff; rewrite H; split; auto.
  - unfold Equal. setoid_rewrite bindings_o.
    induction H; simpl; intros; auto.
    destruct x as (x,e), x' as (x',e'). compute in H. destruct H. subst e'.
    unfold eqb in *. do 2 case K.eq_dec; auto; order.
  Qed.

  Lemma bindings_Eqdom_eqlistA (m m' : t elt) :
   Eqdom m m' <-> eqlistA eqk (bindings m) (bindings m').
  Proof.
  split; intros.
  - apply SortA_equivlistA_eqlistA with (ltA:=ltk); eauto with *.
    intros (k,e). now rewrite <- !in_bindings_iff'.
  - unfold Eqdom. setoid_rewrite bindings_in_iff.
    induction H; simpl; auto.
    + now setoid_rewrite InA_nil.
    + intros y.
      setoid_rewrite InA_cons.
      destruct x as (x,e), x' as (x',e'). compute in H.
      split; intros (e2,[E|IN]); try (firstorder; fail);
       compute in E; destruct E; subst; eexists; left; compute;
       split; eauto; order.
  Qed.

  Lemma bindings_Equiv_eqlistA R (m m' : t elt) :
   Equiv R m m' <->
   eqlistA (K.eq * R)%signature (bindings m) (bindings m').
  Proof.
   intros.
   unfold Equiv. setoid_rewrite bindings_Eqdom_eqlistA.
   setoid_rewrite <- bindings_spec1.
   split.
   - intros (H,H').
     induction H; auto.
     setoid_rewrite InA_cons in H'.
     constructor; firstorder.
     destruct x as (x,e), x' as (x',e'). compute. eapply H'; now left.
   - split.
     + induction H; auto. constructor; auto. destruct x, x'; apply H.
     + assert (Hm := bindings_spec2 m); assert (Hm' := bindings_spec2 m').
       induction H; simpl; auto.
       * now setoid_rewrite InA_nil.
       * inversion_clear Hm; inversion_clear Hm'. intros k e e'.
         rewrite !InA_cons.
         destruct x as (x,v), x' as (x',v'). compute in H. destruct H.
         intros [E|IN] [E'|IN'];
           try (compute in E; destruct E);
           try (compute in E'; destruct E'); subst; eauto.
         { assert (LT : ltk (x',v') (k,e')) by
           (eapply SortA_InfA_InA with (eqA:=eqke); eauto with * ).
           compute in LT. order. }
         { assert (LT : ltk (x,v) (k,e)) by
           (eapply SortA_InfA_InA with (l:=l)(eqA:=eqke); eauto with *).
           compute in LT. order. }
  Qed.

  End Bindings.

  Section Min_Max_Elt.

  (** We emulate two [max_elt] and [min_elt] functions. *)

  Definition min_elt m : option (key*elt) := match bindings m with
   | nil => None
   | (x,e)::_ => Some (x,e)
  end.

  Lemma min_elt_Below m x e :
   min_elt m = Some (x,e) -> Below x (remove x m).
  Proof.
  unfold min_elt, Below; intros.
  rewrite remove_in_iff in H0; destruct H0.
  rewrite bindings_in_iff in H1.
  destruct H1.
  generalize (bindings_spec2' m).
  destruct (bindings m).
  try discriminate.
  destruct p; injection H; intros; subst.
  inversion_clear H1.
  red in H2; destruct H2; simpl in *; F.order.
  inversion_clear H4.
  rewrite (@InfA_alt _ eqke) in H3; eauto with *.
  apply (H3 (y,x0)); auto.
  Qed.

  Lemma min_elt_MapsTo m x e :
   min_elt m = Some (x,e) -> MapsTo x e m.
  Proof.
  intros.
  unfold min_elt in *.
  rewrite bindings_mapsto_iff.
  destruct (bindings m).
  simpl; try discriminate.
  destruct p; simpl in *.
  injection H; intros; subst; constructor; compute; auto with *.
  Qed.

  Lemma min_elt_Empty m :
   min_elt m = None -> Empty m.
  Proof.
  intros.
  unfold min_elt in *.
  rewrite bindings_Empty.
  destruct (bindings m); auto.
  destruct p; simpl in *; discriminate.
  Qed.

  Definition optrel {A} (R:relation A) : relation (option A) :=
   fun o o' =>
     match o, o' with
     | Some a, Some a' => R a a'
     | None, None => True
     | _,_ => False
     end.

  Instance optrel_equiv {A} (R:relation A) `{!Equivalence R} :
    Equivalence (optrel R).
  Proof.
  split.
  - intros [x|]; now simpl.
  - intros [x|] [y|]; now simpl.
  - intros [x|] [y|] [z|]; simpl; eauto; try easy. now transitivity y.
  Qed.

  Global Instance min_elt_m : Proper (Equal ==> optrel eqke) min_elt.
  Proof.
  intros m m' E. unfold min_elt.
  apply bindings_Equal_eqlistA in E.
  destruct E; simpl; auto.
  now destruct x as (k,e), x' as (k',e').
  Qed.

  Global Instance min_elt_m' : Proper (Eqdom ==> optrel eqk) min_elt.
  Proof.
  intros m m' E. unfold min_elt.
  apply bindings_Eqdom_eqlistA in E.
  destruct E; simpl; auto.
  now destruct x as (k,e), x' as (k',e').
  Qed.

  Fixpoint optlast {A} (l:list A) :=
  match l with
  | nil => None
  | x::nil => Some x
  | _::l => optlast l
  end.

  Definition max_elt (m : t elt) := optlast (bindings m).

  Lemma max_elt_Above m x e :
    max_elt m = Some (x,e) -> Above x (remove x m).
  Proof.
  red; intros.
  rewrite remove_in_iff in H0. destruct H0.
  rewrite bindings_in_iff in H1. destruct H1.
  unfold max_elt in *.
  generalize (bindings_spec2' m).
  revert x e H y x0 H0 H1.
  induction (bindings m); try easy.
  intros.
  destruct a; destruct l; simpl in *.
  - injection H; clear H; intros; subst.
    inversion_clear H1.
    + compute in H; simpl in *; intuition. order.
    + inversion H.
  - change (optlast (p::l) = Some (x,e)) in H.
    generalize (IHl x e H); clear IHl; intros IHl.
    inversion_clear H1; [ | inversion_clear H2; eauto ].
    compute in H3; destruct H3. subst.
    destruct p as (p1,p2).
    destruct (K.eq_dec p1 x) as [Heq|Hneq].
    + rewrite <- Heq; auto.
      inversion_clear H2.
      inversion_clear H4.
      compute in H2; F.order.
    + transitivity p1; auto.
      * inversion_clear H2.
        inversion_clear H4.
        compute in H2; F.order.
      * inversion H2; subst.
        eapply IHl; eauto with *.
        econstructor; eauto. compute; eauto with *.
  Qed.

  Lemma max_elt_MapsTo m x e :
    max_elt m = Some (x,e) -> MapsTo x e m.
  Proof.
  intros.
  unfold max_elt in *.
  rewrite bindings_mapsto_iff.
  induction (bindings m); simpl; try easy.
  rewrite InA_cons.
  destruct a; destruct l; simpl in *.
  injection H as -> ->. now left.
  right; auto.
  Qed.

  Lemma max_elt_Empty m : max_elt m = None -> Empty m.
  Proof.
  intros.
  unfold max_elt in *.
  rewrite bindings_Empty.
  induction (bindings m); auto.
  destruct a; destruct l; simpl in *; try discriminate.
  assert (H':=IHl H); discriminate.
  Qed.

  Instance optlast_m {A} R `{Equivalence A R} :
    Proper (eqlistA R ==> optrel R) (@optlast A).
  Proof.
  induction 1; simpl; auto.
  destruct l, l'; simpl; auto. inversion H1. inversion H1.
  Qed.

  Global Instance max_elt_m : Proper (Equal ==> optrel eqke) max_elt.
  Proof.
  intros m m' E. unfold max_elt.
  apply bindings_Equal_eqlistA in E. now rewrite E.
  Qed.

  Global Instance max_elt_m' : Proper (Eqdom ==> optrel eqk) max_elt.
  Proof.
  intros m m' E. unfold max_elt.
  apply bindings_Eqdom_eqlistA in E. now rewrite E.
  Qed.

  End Min_Max_Elt.

  Section Induction_Principles.

  Lemma map_induction_max :
   forall P : t elt -> Type,
   (forall m, Empty m -> P m) ->
   (forall m m', P m -> forall x e, Above x m -> Add x e m m' -> P m') ->
   forall m, P m.
  Proof.
  intros; remember (cardinal m) as n; revert m Heqn; induction n; intros.
  apply X; apply cardinal_inv_1; auto.

  case_eq (max_elt m); intros.
  destruct p.
  assert (Add k e (remove k m) m).
  { apply max_elt_MapsTo, find_spec, add_id in H.
    unfold Add. symmetry. now rewrite add_remove_1. }
  apply X0 with (remove k m) k e; auto with map.
  apply IHn.
  assert (S n = S (cardinal (remove k m))).
  { rewrite Heqn.
    eapply cardinal_S; eauto with map. }
  inversion H1; auto.
  eapply max_elt_Above; eauto.

  apply X; apply max_elt_Empty; auto.
  Qed.

  Lemma map_induction_min :
   forall P : t elt -> Type,
   (forall m, Empty m -> P m) ->
   (forall m m', P m -> forall x e, Below x m -> Add x e m m' -> P m') ->
   forall m, P m.
  Proof.
  intros; remember (cardinal m) as n; revert m Heqn; induction n; intros.
  apply X; apply cardinal_inv_1; auto.

  case_eq (min_elt m); intros.
  destruct p.
  assert (Add k e (remove k m) m).
  { apply min_elt_MapsTo, find_spec, add_id in H.
    unfold Add. symmetry. now rewrite add_remove_1. }
  apply X0 with (remove k m) k e; auto.
  apply IHn.
  assert (S n = S (cardinal (remove k m))).
  { rewrite Heqn.
    eapply cardinal_S; eauto with map. }
  inversion H1; auto.
  eapply min_elt_Below; eauto.

  apply X; apply min_elt_Empty; auto.
  Qed.

  End Induction_Principles.

  Section Fold_properties.

  Global Instance fold_m {A}(eqA:A->A->Prop)(st:Equivalence eqA) :
   Proper ((K.eq==>eq==>eqA==>eqA)==>Equal==>eqA==>eqA) (@fold elt A).
  Proof.
  intros f f' Hf m m' Hm i i' Hi.
  rewrite 2 fold_spec.
  apply bindings_Equal_eqlistA in Hm.
  generalize (bindings_spec2 m)(bindings_spec2 m').
  revert Hm i i' Hi.
  induction 1; simpl; auto.
  destruct x as (k,e), x' as (k',e').
  change (K.eq k k' /\ e = e') in H. destruct H as (Hk,He).
  intros i i' Hi. inversion 1; inversion 1; subst. simpl.
  apply IHHm; auto. apply Hf; auto.
  Qed.

  (** The following lemma has already been proved on Weak Maps,
      but with one additional hypothesis (a [Diamond] transposition). *)

  Lemma fold_Proper {A}(eqA:A->A->Prop)(st:Equivalence eqA)
   (f:key->elt->A->A) :
   Proper (K.eq==>eq==>eqA==>eqA) f ->
   Proper (Equal==>eqA==>eqA) (fold f).
  Proof.
  intros Hf m1 m2 Heq i i' Hi. f_equiv; auto.
  Qed.

  Lemma fold_Add_Above m1 m2 x e {A}(eqA:A->A->Prop)(st:Equivalence eqA)
   (f:key->elt->A->A)(i:A)(Hf:Proper (K.eq==>eq==>eqA==>eqA) f) :
   Above x m1 -> Add x e m1 m2 ->
   eqA (fold f m2 i) (f x e (fold f m1 i)).
  Proof.
  intros. rewrite 2 fold_spec_right. set (f':=uncurry f).
  transitivity (fold_right f' i (rev (bindings m1 ++ (x,e)::nil))).
  apply fold_right_eqlistA with (eqA:=eqke) (eqB:=eqA); auto.
  intros (k1,e1) (k2,e2) (Hk,He) a1 a2 Ha; unfold f'; simpl in *.
  - apply Hf; auto.
  - apply eqlistA_rev. apply bindings_Add_Above; auto.
  - rewrite distr_rev; simpl. reflexivity.
  Qed.

  Lemma fold_Add_Below m1 m2 x e {A}(eqA:A->A->Prop)(st:Equivalence eqA)
   (f:key->elt->A->A)(i:A)(Hf:Proper (K.eq==>eq==>eqA==>eqA) f) :
   Below x m1 -> Add x e m1 m2 ->
   eqA (fold f m2 i) (fold f m1 (f x e i)).
  Proof.
  intros. rewrite 2 fold_spec_right. set (f':=uncurry f).
  transitivity (fold_right f' i (rev (((x,e)::nil)++bindings m1))).
  apply fold_right_eqlistA with (eqA:=eqke) (eqB:=eqA); auto.
  intros (k1,e1) (k2,e2) (Hk,He) a1 a2 Ha; unfold f'; simpl in *.
  - apply Hf; auto.
  - apply eqlistA_rev. apply bindings_Add_Below; auto.
  - rewrite distr_rev; simpl. rewrite fold_right_app. reflexivity.
  Qed.

  End Fold_properties.

  (** Comparisons of maps *)

  Lemma Kcompare_trans : Trans K.compare.
  Proof.
   intros [ ] x y z;
    rewrite ?compare_eq_iff, ?compare_lt_iff,  ?compare_gt_iff; order.
  Qed.

  Global Instance Kcompare_symtrans : SymTrans K.compare.
  Proof.
   split. exact F.compare_antisym. exact Kcompare_trans.
  Qed.

  Definition isEq c := match c with Eq => true | _ => false end.

  Lemma isEq_spec c : isEq c = true <-> c = Eq.
  Proof. now destruct c. Qed.

  Lemma compare_Equiv cmp (m m':t elt) :
    compare cmp m m' = Eq <-> Equiv (fun e e' => cmp e e' = Eq) m m'.
  Proof.
  rewrite compare_spec.
  rewrite list_compare_eq.
  rewrite bindings_Equiv_eqlistA.
  split; induction 1; simpl; auto; constructor; auto.
  - destruct x as (x,e), y as (y,e'). compute.
    rewrite pair_compare_eq in H. now rewrite compare_eq_iff in H.
  - destruct x as (x,e), x' as (x',e').
    rewrite pair_compare_eq. now rewrite compare_eq_iff.
  Qed.

  Lemma compare_equiv cmp (m m':t elt) :
    isEq (compare cmp m m') = equal (fun e e' => isEq (cmp e e')) m m'.
  Proof.
  apply eq_true_iff_eq. rewrite equal_spec.
  rewrite isEq_spec, compare_Equiv. unfold Equivb, Equiv, Cmp.
  now setoid_rewrite isEq_spec.
  Qed.

  (** If the comparison function [cmp] on values is symmetric
      and transitive, then [compare cmp] provides a OrderedType-like
      structure on maps. *)

  Section Compare.
  Variable cmp : elt -> elt -> comparison.
  Context `(!SymTrans cmp).

  Global Instance compare_symtrans : SymTrans (compare cmp).
  Proof.
  constructor.
  - intros x y. rewrite !compare_spec; apply sym; eauto with *.
  - intros c x y z. rewrite !compare_spec; apply tra; eauto with *.
  Qed.

  Definition eq m m' := compare cmp m m' = Eq.
  Definition lt m m' := compare cmp m m' = Lt.

  Lemma compare_refl m : compare cmp m m = Eq.
  Proof.
  destruct (compare cmp m m) eqn:E; auto; assert (E':=E).
  rewrite sym, CompOpp_iff in E. simpl in E. congruence.
  rewrite sym, CompOpp_iff in E. simpl in E. congruence.
  Qed.

  Global Instance eq_equiv : Equivalence eq.
  Proof.
  split.
  - intro x. apply compare_refl.
  - intros x y E. unfold eq. now rewrite sym, CompOpp_iff.
  - intros x y z. apply tra.
  Qed.

  Global Instance lt_strorder : StrictOrder lt.
  Proof.
  split.
  - intros x. red. unfold lt. now rewrite compare_refl.
  - intros x y z. apply tra.
  Qed.

  Global Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
  intros x x' E y y' E'. unfold lt,eq in *. split; intros <-.
  - symmetry.
    rewrite SymTrans_CompatL; eauto with *.
    rewrite SymTrans_CompatR; eauto with *.
  - rewrite SymTrans_CompatL; eauto with *.
    rewrite SymTrans_CompatR; eauto with *.
  Qed.

  Lemma compare_spec' m m' :
    CompareSpec (eq m m') (lt m m') (lt m' m) (compare cmp m m').
  Proof.
   unfold eq, lt. rewrite (@sym _ (compare cmp) _ m m').
   destruct (compare cmp m m'); auto.
  Qed.

  Lemma eq_spec m m' : eq m m' <-> Equiv (fun e e' => cmp e e' = Eq) m m'.
  Proof. apply compare_Equiv. Qed.

  Definition eq_dec m m' : {eq m m'} + {~eq m m'}.
  Proof.
  destruct (compare cmp m m') eqn:E.
  - now left.
  - right. unfold eq. now rewrite E.
  - right. unfold eq. now rewrite E.
  Defined.

  End Compare.
 End Elt.
End OrdProperties.

(** Modular statement of the last group of results :
    If we have an OrderedType on elements, then we have one on maps.
    While building OrderedType of sets was both direct and useful
    (for sets of sets), here OrderedType on maps is technically
    complex (extra structure for elements) and seldom used
    (maps or sets indexed by maps ??). Hence this separate functor. *)

Module OrderedMaps (K:OrderedType)(D:OrderedType)(M:S K) <: OrderedType.
 Module P := OrdProperties K M.
 Module D' := OrdersAlt.OT_to_Alt(D).

 Definition t := M.t D.t.
 Definition eq := P.eq D.compare.
 Definition lt := P.lt D.compare.
 Definition compare := M.compare D.compare.

 Global Instance Dcompare_symtrans : SymTrans D.compare.
 Proof.
 split. exact D'.compare_sym. exact D'.compare_trans.
 Qed.

 Global Instance compare_symtrans : SymTrans compare.
 Proof. apply P.compare_symtrans, Dcompare_symtrans. Qed.

 Global Instance eq_equiv : Equivalence eq := P.eq_equiv _.
 Global Instance lt_strorder : StrictOrder lt := P.lt_strorder _.
 Global Instance lt_compat : Proper (eq ==> eq ==> iff) lt := P.lt_compat _.

 Lemma compare_spec (m m' :t) :
  CompareSpec (eq m m') (lt m m') (lt m' m) (compare m m').
 Proof. apply (P.compare_spec' _). Qed.

 Definition eq_dec : forall m m', {eq m m'}+{~eq m m'} := P.eq_dec _.

 (** Extra description of [eq] : *)

 Lemma eq_spec m m' : eq m m' <-> M.Equiv D.eq m m'.
 Proof.
  unfold eq. rewrite P.eq_spec.
  unfold M.Equiv. now setoid_rewrite D'.compare_Eq.
 Qed.

End OrderedMaps.
