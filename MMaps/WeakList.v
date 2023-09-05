
(** * Finite Modular Maps : Unordered Lists *)

(** Author : Pierre Letouzey (Université de Paris - INRIA),
    adapted from earlier works in Coq Standard Library, see README.md.
    Licence : LGPL 2.1, see file LICENSE. *)

(** This file proposes an implementation of the interface
 [Tries.MMaps.Interface.WS] using lists of pairs, unordered but without
 redundancy. Most operations are linear, with the notable exception
 of [merge] which is quadratic. *)

From Coq Require Import EqualitiesFacts.
From Tries.MMaps Require Interface Raw.
Import Interface.

Set Implicit Arguments.
Unset Strict Implicit.

Module MakeRaw (K:DecidableType) <: Raw.WS K.

Module Import P := KeyDecidableType K.

Definition key := K.t.
Definition t (elt:Type) := list (K.t * elt).

Definition eq_key {elt} := @P.eqk elt.
Definition eq_key_elt {elt} := @P.eqke elt.
Definition IsOk {elt} := NoDupA (@eqk elt).
Class Ok {elt}(m:t elt) : Prop := ok : NoDupA eqk m.

Ltac chok :=
 match goal with
 | H : context [NoDupA (@eqk ?elt)] |- _ =>
   change (NoDupA (@eqk elt)) with (@Ok elt) in H; chok
 | |- context [NoDupA (@eqk ?elt)] =>
   change (NoDupA (@eqk elt)) with (@Ok elt); chok
 | _ => idtac
 end.

Ltac autok := chok; auto with typeclass_instances.

Ltac dec := match goal with
 | |- context [ K.eq_dec ?x ?x ] =>
   let E := fresh "E" in destruct (K.eq_dec x x) as [E|E]; [ | now elim E]
 | H : K.eq ?x ?y |- context [ K.eq_dec ?x ?y ] =>
   let E := fresh "E" in destruct (K.eq_dec x y) as [_|E]; [ | now elim E]
 | H : ~K.eq ?x ?y |- context [ K.eq_dec ?x ?y ] =>
   let E := fresh "E" in destruct (K.eq_dec x y) as [E|_]; [ now elim H | ]
 | |- context [ K.eq_dec ?x ?y ] =>
   let E := fresh "E" in destruct (K.eq_dec x y) as [E|E]
end.

Section Elt.

Variable elt : Type.

(** * [find] *)

Fixpoint find (k:key) (s: t elt) : option elt :=
  match s with
   | nil => None
   | (k',x)::s' => if K.eq_dec k k' then Some x else find k s'
  end.

Lemma find_spec m x e {Hm:Ok m} :
  find x m = Some e <-> MapsTo x e m.
Proof.
 unfold P.MapsTo.
 induction m as [ | (k,v) m IH]; simpl.
 - split; inversion 1.
 - rewrite InA_cons.
   change (eqke (x,e) (k,v)) with (K.eq x k /\ e = v).
   inversion_clear Hm. dec.
   + setoid_replace (Some v = Some e) with (v = e) by (split; congruence).
     intuition. elim H. apply InA_eqk with (x,e); auto.
   + rewrite IH; intuition.
Qed.

(** * [mem] *)

Fixpoint mem (k : key) (s : t elt) : bool :=
  match s with
   | nil => false
   | (k',_) :: l => if K.eq_dec k k' then true else mem k l
  end.

Lemma mem_spec m x {Hm:Ok m} : mem x m = true <-> In x m.
Proof.
 induction m as [ | (k,e) m IH]; simpl.
 - split. discriminate. inversion_clear 1. inversion H0.
 - inversion_clear Hm. rewrite P.In_cons; simpl.
   rewrite <- IH by trivial.
   dec; intuition.
Qed.

Fixpoint isok (m: t elt) : bool :=
  match m with
   | nil => true
   | (k,_)::m' => negb (mem k m') && isok m'
  end.

Lemma isok_spec (m: t elt) : isok m = true <-> Ok m.
Proof.
 induction m as [|(x,e) m IH]; simpl.
 - split; constructor.
 - rewrite andb_true_iff, IH. split.
   + intros (H,O). constructor; auto.
     rewrite <- In_alt', <- mem_spec; auto. now destruct mem.
   + inversion 1; subst; split; auto.
     rewrite <- In_alt', <- mem_spec in H2; auto. now destruct mem.
Qed.

Lemma isok_Ok (m:t elt) : isok m = true -> Ok m.
Proof. apply isok_spec. Qed.

(** * [empty] *)

Definition empty : t elt := nil.

Lemma empty_spec x : find x empty = None.
Proof.
 reflexivity.
Qed.

Global Instance empty_ok : Ok empty.
Proof.
 unfold empty; red; auto.
Qed.

(** * [is_empty] *)

Definition is_empty (l : t elt) : bool := if l then true else false.

Lemma is_empty_spec m : is_empty m = true <-> forall x, find x m = None.
Proof.
 destruct m as [|(x,e) m]; simpl; intuition; try discriminate.
 specialize (H x).
 revert H. now dec.
Qed.

(* Not part of the exported specifications, used later for [merge]. *)

Lemma find_eq : forall m (Hm:Ok m) x x',
   K.eq x x' -> find x m = find x' m.
Proof.
 induction m; simpl; auto; destruct a; intros.
 inversion_clear Hm.
 rewrite (IHm H1 x x'); auto.
 dec; dec; trivial.
 elim E0. now transitivity x.
 elim E. now transitivity x'.
Qed.

(** * [add] *)

Fixpoint add (k : key) (x : elt) (s : t elt) : t elt :=
  match s with
   | nil => (k,x) :: nil
   | (k',y) :: l => if K.eq_dec k k' then (k,x)::l else (k',y)::add k x l
  end.

Lemma add_spec1' m x e : find x (add x e m) = Some e.
Proof.
 induction m as [ | (k,e') m IH]; simpl.
 - now dec.
 - dec; simpl; now dec.
Qed.

Lemma add_spec2' m x y e : ~K.eq x y -> find y (add x e m) = find y m.
Proof.
 intros N.
 assert (N' : ~K.eq y x) by now contradict N.
 induction m as [ | (k,e') m IH]; simpl.
 - dec; trivial.
 - repeat (dec; simpl); trivial. elim N. now transitivity k.
Qed.

Lemma add_spec1 m x e `{!Ok m} : find x (add x e m) = Some e.
Proof. apply add_spec1'. Qed.
Lemma add_spec2 m x y e `{!Ok m} : ~K.eq x y -> find y (add x e m) = find y m.
Proof. apply add_spec2'. Qed.

Lemma add_InA : forall m x y e e',
  ~ K.eq x y -> InA eqk (y,e) (add x e' m) -> InA eqk (y,e) m.
Proof.
 induction m as [ | (k,e') m IH]; simpl; intros.
 - inversion_clear H0. elim H. symmetry; apply H1. inversion_clear H1.
 - revert H0; dec; rewrite !InA_cons.
   + rewrite E. intuition.
   + intuition. right; eapply IH; eauto.
Qed.

Global Instance add_ok m x e (Hm:Ok m) : Ok (add x e m).
Proof.
 induction m as [ | (k,e') m IH]; simpl.
 - constructor; auto. now inversion 1.
 - inversion_clear Hm. dec; constructor; autok.
   + contradict H. apply InA_eqk with (x,e); auto.
   + contradict H; apply add_InA with x e; auto.
Qed.

(** * [remove] *)

Fixpoint remove (k : key) (s : t elt) : t elt :=
  match s with
   | nil => nil
   | (k',x) :: l => if K.eq_dec k k' then l else (k',x) :: remove k l
  end.

Lemma remove_spec1 m x {Hm: Ok m} : find x (remove x m) = None.
Proof.
 induction m as [ | (k,e') m IH]; simpl; trivial.
 inversion_clear Hm.
 repeat (dec; simpl); auto.
 destruct (find x m) eqn:F; trivial.
 apply find_spec in F; trivial.
 elim H. apply InA_eqk with (x,e); auto.
Qed.

Lemma remove_spec2 m x y {Hm: Ok m} : ~K.eq x y ->
  find y (remove x m) = find y m.
Proof.
 induction m as [ | (k,e') m IH]; simpl; trivial; intros E.
 inversion_clear Hm.
 repeat (dec; simpl); auto.
 elim E. now transitivity k.
Qed.

Lemma remove_InA : forall m (Hm:Ok m) x y e,
  InA eqk (y,e) (remove x m) -> InA eqk (y,e) m.
Proof.
 induction m as [ | (k,e') m IH]; simpl; trivial; intros.
 inversion_clear Hm.
 revert H; dec; rewrite !InA_cons; intuition.
 right; eapply H; eauto.
Qed.

Global Instance remove_ok m x (Hm:Ok m) : Ok (remove x m).
Proof.
 induction m.
 simpl; intuition.
 intros.
 inversion_clear Hm.
 destruct a as (x',e').
 simpl; case (K.eq_dec x x'); auto.
 constructor; autok.
 contradict H; apply remove_InA with x; auto.
Qed.

(** * [bindings] *)

Definition bindings (m : t elt) := m.

Lemma bindings_spec1 m x e : InA eqke (x,e) (bindings m) <-> MapsTo x e m.
Proof.
 reflexivity.
Qed.

Lemma bindings_spec2w m (Hm:Ok m) : Ok (bindings m).
Proof.
 trivial.
Qed.

(** * [fold] *)

Fixpoint fold (A:Type)(f:key->elt->A->A)(m:t elt) (acc : A) :  A :=
  match m with
   | nil => acc
   | (k,e)::m' => fold f m' (f k e acc)
  end.

Lemma fold_spec : forall m (A:Type)(i:A)(f:key->elt->A->A),
  fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.
Proof.
 induction m as [ | (k,e) m IH]; simpl; auto.
Qed.

(** * [singleton] *)

Definition singleton k (e:elt) : t elt := (k,e)::nil.

Lemma singleton_spec x e : bindings (singleton x e) = (x,e)::nil.
Proof. reflexivity. Qed.

Global Instance singleton_ok x e : Ok (singleton x e).
Proof.
 constructor; auto. inversion 1.
Qed.

(** * [equal] *)

Definition check (cmp : elt -> elt -> bool)(k:key)(e:elt)(m': t elt) :=
  match find k m' with
   | None => false
   | Some e' => cmp e e'
  end.

Definition submap (cmp : elt -> elt -> bool)(m m' : t elt) : bool :=
  fold (fun k e b => andb (check cmp k e m') b) m true.

Definition equal (cmp : elt -> elt -> bool)(m m' : t elt) : bool :=
  andb (submap cmp m m') (submap (fun e' e => cmp e e') m' m).

Definition Submap (cmp:elt->elt->bool) m m' :=
  (forall k, In k m -> In k m') /\
  (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).

Definition Equal m m' := forall y, find y m = find y m'.
Definition Eqdom m m' := forall y, @In elt y m <-> @In elt y m'.
Definition Equiv (R:elt->elt->Prop) m m' :=
  Eqdom m m' /\
  (forall k e e', MapsTo k e m -> MapsTo k e' m' -> R e e').
Definition Equivb (cmp:elt->elt->bool) := Equiv (Cmp cmp).

Lemma submap_1 : forall m (Hm:Ok m) m' (Hm': Ok m') cmp,
  Submap cmp m m' -> submap cmp m m' = true.
Proof.
 unfold Submap, submap.
 induction m.
 simpl; auto.
 destruct a; simpl; intros.
 destruct H.
 inversion_clear Hm.
 assert (H3 : In t0 m').
 { apply H; exists e; auto with *. }
 destruct H3 as (e', H3).
 assert (H4 : find t0 m' = Some e') by now apply find_spec.
 unfold check at 2. rewrite H4.
 rewrite (H0 t0); simpl; auto with *.
 eapply IHm; auto.
 split; intuition.
 apply H.
 destruct H6 as (e'',H6); exists e''; auto.
 apply H0 with k; auto.
Qed.

Lemma submap_2 : forall m (Hm:Ok m) m' (Hm': Ok m') cmp,
  submap cmp m m' = true -> Submap cmp m m'.
Proof.
 unfold Submap, submap.
 induction m.
 simpl; auto.
 intuition.
 destruct H0; inversion H0.
 inversion H0.

 destruct a; simpl; intros.
 inversion_clear Hm.
 rewrite andb_b_true in H.
 assert (check cmp t0 e m' = true).
  clear H1 H0 Hm' IHm.
  set (b:=check cmp t0 e m') in *.
  generalize H; clear H; generalize b; clear b.
  induction m; simpl; auto; intros.
  destruct a; simpl in *.
  destruct (andb_prop _ _ (IHm _ H)); auto.
 rewrite H2 in H.
 destruct (IHm H1 m' Hm' cmp H); auto.
 unfold check in H2.
 case_eq (find t0 m'); [intros e' H5 | intros H5];
  rewrite H5 in H2; try discriminate.
 split; intros.
 destruct H6 as (e0,H6); inversion_clear H6.
 compute in H7; destruct H7; subst.
 exists e'.
 apply P.MapsTo_eq with t0; auto with *.
 apply find_spec; auto.
 apply H3.
 exists e0; auto.
 inversion_clear H6.
 compute in H8; destruct H8; subst.
 assert (H8 : MapsTo t0 e'0 m'). { eapply P.MapsTo_eq; eauto. }
 apply find_spec in H8; trivial. congruence.
 apply H4 with k; auto.
Qed.

(** Specification of [equal] *)

Lemma equal_spec cmp m m' {Hm:Ok m}{Hm': Ok m'} :
  equal cmp m m' = true <-> Equivb cmp m m'.
Proof.
 unfold equal.
 split.
 - intros.
   destruct (andb_prop _ _ H); clear H.
   generalize (submap_2 Hm Hm' H0).
   generalize (submap_2 Hm' Hm H1).
   firstorder.
 - intuition.
   apply andb_true_intro; split; apply submap_1; unfold Submap; firstorder.
Qed.
End Elt.
Section Elt2.
Variable elt elt' : Type.

(** * [map] and [mapi] *)

Definition map (f:elt -> elt') (m:t elt) : t elt' :=
  List.map (fun '(k,e) => (k,f e)) m.

Definition mapi (f: key -> elt -> elt') (m:t elt) : t elt' :=
  List.map (fun '(k,e) => (k,f k e)) m.

(** Specification of [map] *)

Lemma map_spec (f:elt->elt')(m:t elt) :
  bindings (map f m) = List.map (fun '(k,e) => (k,f e)) (bindings m).
Proof.
 reflexivity.
Qed.

Lemma map_InA (f:elt->elt')(m:t elt) x e :
 InA eqk (x,f e) (map f m) <-> InA eqk (x,e) m.
Proof.
 induction m as [|(k,v) m IH]; simpl; rewrite ?InA_nil, ?InA_cons;
  intuition.
Qed.

Global Instance map_ok (f:elt->elt') m (Hm : Ok m) : Ok (map f m).
Proof.
 induction m as [|(x,e) m IH]; simpl. red; constructor.
 inversion_clear Hm. constructor; autok. now rewrite map_InA.
Qed.

(** Specification of [mapi] *)

Lemma mapi_spec (f:key->elt->elt')(m:t elt) :
  bindings (mapi f m) = List.map (fun '(k,e) => (k,f k e)) (bindings m).
Proof.
 reflexivity.
Qed.

Global Instance mapi_ok (f: key->elt->elt') m (Hm:Ok m) : Ok (mapi f m).
Proof.
 induction m as [|(x,e) m IH]; simpl. red; constructor.
 inversion_clear Hm; auto.
 constructor; autok.
 contradict H. clear IH H0.
 induction m as [|(y,v) m IH]; simpl in *; inversion H; auto.
Qed.

End Elt2.

Lemma mapfst_InA {elt}(m:t elt) x :
 InA K.eq x (List.map fst m) <-> In x m.
Proof.
 induction m as [| (k,e) m IH]; simpl; auto.
 - split; inversion 1. inversion H0.
 - rewrite InA_cons, In_cons. simpl. now rewrite IH.
Qed.

Lemma mapfst_ok {elt}(m:t elt) :
 NoDupA K.eq (List.map fst m) <-> NoDupA eqk m.
Proof.
 induction m as [| (k,e) m IH]; simpl.
 - split; constructor.
 - split; inversion_clear 1; constructor; try apply IH; trivial.
   + contradict H0. rewrite mapfst_InA. eapply In_alt'; eauto.
   + rewrite mapfst_InA. contradict H0. now apply In_alt'.
Qed.

Lemma list_filter_ok f (m:list key) :
 NoDupA K.eq m -> NoDupA K.eq (List.filter f m).
Proof.
 induction 1; simpl.
 - constructor.
 - destruct (f x); trivial. constructor; trivial.
   contradict H. rewrite InA_alt in *. destruct H as (y,(Hy,H)).
   exists y; split; trivial. now rewrite filter_In in H.
Qed.

Lemma NoDupA_unique_repr (l:list key) x y :
 NoDupA K.eq l -> K.eq x y -> List.In x l -> List.In y l -> x = y.
Proof.
 intros H E Hx Hy.
 induction H; simpl in *.
 - inversion Hx.
 - intuition; subst; trivial.
   elim H. apply InA_alt. now exists y.
   elim H. apply InA_alt. now exists x.
Qed.

Section Elt3.

Variable elt elt' elt'' : Type.

Definition restrict (m:t elt)(k:key) :=
 match find k m with
 | None => true
 | Some _ => false
 end.

Definition domains (m:t elt)(m':t elt') :=
 List.map fst m ++ List.filter (restrict m) (List.map fst m').

Lemma domains_InA m m' (Hm : Ok m) x :
 InA K.eq x (domains m m') <-> In x m \/ In x m'.
Proof.
 unfold domains.
 assert (Proper (K.eq==>eq) (restrict m)).
 { intros k k' Hk. unfold restrict. now rewrite (find_eq Hm Hk). }
 rewrite InA_app_iff, filter_InA, !mapfst_InA; intuition.
 unfold restrict.
 destruct (find x m) eqn:F.
 - left. apply find_spec in F; trivial. now exists e.
 - now right.
Qed.

Lemma domains_ok m m' : NoDupA eqk m -> NoDupA eqk m' ->
 NoDupA K.eq (domains m m').
Proof.
 intros Hm Hm'. unfold domains.
 apply NoDupA_app; auto with *.
 - now apply mapfst_ok.
 - now apply list_filter_ok, mapfst_ok.
 - intros x.
   rewrite mapfst_InA. intros (e,H).
   apply find_spec in H; trivial.
   rewrite InA_alt. intros (y,(Hy,H')).
   rewrite (find_eq Hm Hy) in H.
   rewrite filter_In in H'. destruct H' as (_,H').
   unfold restrict in H'. now rewrite H in H'.
Qed.

Fixpoint fold_keys (f:key->option elt'') l :=
  match l with
    | nil => nil
    | k::l =>
      match f k with
        | Some e => (k,e)::fold_keys f l
        | None => fold_keys f l
      end
  end.

Lemma fold_keys_In f l x e :
  List.In (x,e) (fold_keys f l) <-> List.In x l /\ f x = Some e.
Proof.
 induction l as [|k l IH]; simpl.
 - intuition.
 - destruct (f k) eqn:F; simpl; rewrite IH; clear IH; intuition;
   try left; congruence.
Qed.

Lemma fold_keys_ok f l :
  NoDupA K.eq l -> Ok (fold_keys f l).
Proof.
 induction 1; simpl.
 - constructor.
 - destruct (f x); trivial.
   constructor; trivial. contradict H.
   apply InA_alt in H. destruct H as ((k,e'),(E,H)).
   rewrite fold_keys_In in H.
   apply InA_alt. exists k. now split.
Qed.

Variable f : key -> option elt -> option elt' -> option elt''.

Definition merge m m' : t elt'' :=
 fold_keys (fun k => f k (find k m) (find k m')) (domains m m').

Global Instance merge_ok m m' (Hm:Ok m)(Hm':Ok m') : Ok (merge m m').
Proof.
 now apply fold_keys_ok, domains_ok.
Qed.

Lemma merge_spec1 m m' x {Hm:Ok m}{Hm':Ok m'} :
  In x m \/ In x m' ->
  exists y:key, K.eq y x /\
                find x (merge m m') = f y (find x m) (find x m').
Proof.
 assert (Hmm' : Ok (merge m m')) by now apply merge_ok.
 rewrite <- domains_InA; trivial.
 rewrite InA_alt. intros (y,(Hy,H)).
 exists y; split; [easy|].
 rewrite (find_eq Hm Hy), (find_eq Hm' Hy).
 destruct (f y (find y m) (find y m')) eqn:F.
 - apply find_spec; trivial.
   red. apply InA_alt. exists (y,e). split. now split.
   unfold merge. apply fold_keys_In. now split.
 - destruct (find x (merge m m')) eqn:F'; trivial.
   rewrite <- F; clear F. symmetry.
   apply find_spec in F'; trivial.
   red in F'. rewrite InA_alt in F'.
   destruct F' as ((y',e'),(E,F')).
   unfold merge in F'; rewrite fold_keys_In in F'.
   destruct F' as (H',F').
   compute in E; destruct E as (Hy',<-).
   replace y with y'; trivial.
   apply (@NoDupA_unique_repr (domains m m')); auto.
   now apply domains_ok.
   now transitivity x.
Qed.

Lemma merge_spec2 m m' x {Hm:Ok m}{Hm':Ok m'} :
  In x (merge m m') -> In x m \/ In x m'.
Proof.
 rewrite <- domains_InA; trivial.
 intros (e,H). red in H. rewrite InA_alt in H. destruct H as ((k,e'),(E,H)).
 unfold merge in H; rewrite fold_keys_In in H. destruct H as (H,_).
 apply InA_alt. exists k. split; trivial. now destruct E.
Qed.

End Elt3.

Definition cardinal {elt} (m:t elt) := length m.
Lemma cardinal_spec {elt} (m:t elt) : cardinal m = length (bindings m).
Proof. reflexivity. Qed.

Definition MapsTo {elt} := @P.MapsTo elt.
Definition In {elt} := @P.In elt.

Global Instance MapsTo_compat {elt} :
  Proper (K.eq==>Logic.eq==>Logic.eq==>iff) (@MapsTo elt).
Proof.
 intros x x' Hx e e' <- m m' <-. unfold MapsTo. now rewrite Hx.
Qed.

Definition filter {elt} (f:key->elt->bool) :=
  List.filter (fun '(k,e) => f k e).

Definition partition {elt} (f:key->elt->bool) :=
  List.partition (fun '(k,e) => f k e).

Definition for_all {elt} (f:key->elt->bool) :=
  List.forallb (fun '(k,e) => f k e).

Definition exists_ {elt} (f:key->elt->bool) :=
  List.existsb (fun '(k,e) => f k e).

Lemma filter_spec {elt} (f:key->elt->bool) m `{!Ok m} :
 bindings (filter f m) = List.filter (fun '(k,e) => f k e) (bindings m).
Proof. reflexivity. Qed.

Global Instance filter_ok {elt} f (m:t elt) : Ok m -> Ok (filter f m).
Proof.
 induction 1; simpl.
 - constructor.
 - destruct x as (k,e).
   destruct (f k e); trivial. constructor; trivial.
   contradict H. rewrite InA_alt in *. destruct H as (y,(Hy,H)).
   exists y; split; trivial. unfold filter in *.
   now rewrite filter_In in H.
Qed.

Lemma partition_spec {elt} (f:key->elt->bool) m `{!Ok m} :
 prodmap (@bindings _) (partition f m) =
  List.partition (fun '(k,e) => f k e) (bindings m).
Proof. unfold bindings, partition. now destruct List.partition. Qed.

Lemma partition_fst {elt} f (m:t elt) : fst (partition f m) = filter f m.
Proof.
 induction m; simpl; auto.
 rewrite <- IHm. now destruct (partition f m), a, f.
Qed.

Lemma partition_snd {elt} f (m:t elt) :
  snd (partition f m) = filter (fun k e => negb (f k e)) m.
Proof.
 induction m; simpl; auto.
 rewrite <- IHm. now destruct (partition f m), a, f.
Qed.

Global Instance partition_ok1 {elt} f (m:t elt) : Ok m -> Ok (fst (partition f m)).
Proof.
 rewrite partition_fst; eauto with *.
Qed.

Global Instance partition_ok2 {elt} f (m:t elt) : Ok m -> Ok (snd (partition f m)).
Proof.
 rewrite partition_snd; eauto with *.
Qed.

Lemma for_all_spec {elt}(f:key->elt->bool) m :
 for_all f m = List.forallb (fun '(k,e) => f k e) (bindings m).
Proof. reflexivity. Qed.

Lemma exists_spec {elt}(f:key->elt->bool) m :
 exists_ f m = List.existsb (fun '(k,e) => f k e) (bindings m).
Proof. reflexivity. Qed.

End MakeRaw.

Module Make (K:DecidableType) <: Interface.WS K.
 Module Raw := MakeRaw K.
 Include Raw.WPack K Raw.
End Make.
