
(** * Finite Modular Maps : Ordered Lists *)

(** Author : Pierre Letouzey (Université de Paris - INRIA),
    adapted from earlier works in Coq Standard Library, see README.md.
    Licence : LGPL 2.1, see file LICENSE. *)

(** This file proposes an implementation of the interface
    [Tries.MMaps.Interface.S] using lists of pairs ordered (increasing)
    with respect to left projection. Almost all operations
    have linear complexity. *)

From Coq Require Import OrdersFacts OrdersLists.
From Tries.MMaps Require Comparisons Interface Raw.
Import Comparisons Interface.

Set Implicit Arguments.
Unset Strict Implicit.

Module MakeRaw (X:OrderedType) <: Raw.S X.

Module Import MX := OrderedTypeFacts X.
Module Import PX := KeyOrderedType X.

Definition key := X.t.
Definition t (elt:Type) := list (X.t * elt).

Definition eq_key {elt} := @PX.eqk elt.
Definition lt_key {elt} := @PX.ltk elt.
Definition eq_key_elt {elt} := @PX.eqke elt.
Definition IsOk {elt} := sort (@ltk elt).
Class Ok {elt}(m:t elt) : Prop := ok : sort ltk m.

Local Hint Unfold Ok IsOk : map.
Ltac chok :=
 match goal with
 | H : context [sort (@ltk ?elt)] |- _ =>
   change (sort (@ltk elt)) with (@Ok elt) in H; chok
 | |- context [sort (@ltk ?elt)] =>
   change (sort (@ltk elt)) with (@Ok elt); chok
 | _ => idtac
 end.
Ltac autok := chok; auto with typeclass_instances map.
Ltac eautok := chok; eauto with typeclass_instances map.

Local Notation Sort := (sort ltk).
Local Notation Inf := (lelistA (ltk)).

Section Elt.
Variable elt : Type.

Ltac SortLt :=
 match goal with
   | H1 : Sort ?m, H2:Inf (?k',?e') ?m, H3:In ?k ?m |- _  =>
     assert (X.lt k' k);
     [let e := fresh "e" in destruct H3 as (e,H3);
      change (ltk (k',e') (k,e));
      apply (Sort_Inf_In H1 H2 (InA_eqke_eqk H3)) | ]
   | H1:Sort ?m, H2:Inf (?k',?e') ?m, H3:MapsTo ?k ?e ?m |- _  =>
     assert (X.lt k' k);
     [change (ltk (k',e') (k,e));
      apply (Sort_Inf_In H1 H2 (InA_eqke_eqk H3)) | ]
   | H1:Sort ?m, H2:Inf (?k',?e') ?m, H3:InA eqke (?k,?e) ?m |- _  =>
     assert (X.lt k' k);
     [change (ltk (k',e') (k,e));
      apply (Sort_Inf_In H1 H2 (InA_eqke_eqk H3)) | ]
 end.

(** [isok] : deciding [Ok]. Not used here, see [Mkt_bool] in [Raw.v] *)

Fixpoint isok (m:t elt) :=
  match m with
  | nil => true
  | _ :: nil => true
  | (x,_) :: (((y,_) :: _) as m') =>
    match X.compare x y with
    | Lt => isok m'
    | _ => false
    end
  end.

Lemma isok_spec (m:t elt) : isok m = true <-> Ok m.
Proof.
 induction m as [|(x,e) m IH]; simpl.
 - intuition.
 - destruct m as [|(y,e') m].
   + intuition.
   + case X.compare_spec; intros C.
     * split. easy. inversion 1; subst. inversion H3; subst.
       compute in H1. order.
     * rewrite IH. split. intros; constructor; autok.
       inversion 1; auto.
     * split. easy. inversion 1; subst. inversion H3; subst.
       compute in H1. order.
Qed.

Lemma isok_Ok (m:t elt) : isok m = true -> Ok m.
Proof. apply isok_spec. Qed.

(** * [find] *)

Fixpoint find (k:key) (m: t elt) : option elt :=
 match m with
  | nil => None
  | (k',x)::m' =>
     match X.compare k k' with
      | Lt => None
      | Eq => Some x
      | Gt => find k m'
     end
 end.

Lemma find_spec m x e {Hm:Ok m}:
 find x m = Some e <-> MapsTo x e m.
Proof.
 induction m as [|(k,e') m IH]; simpl.
 - split. discriminate. inversion 1.
 - inversion_clear Hm.
   unfold MapsTo in *. rewrite InA_cons, eqke_def.
   case X.compare_spec; intros.
   + split. injection 1 as ->; auto.
     intros [(_,<-)|IN]; trivial. SortLt. MX.order.
   + split. discriminate.
     intros [(E,<-)|IN]; trivial; try SortLt; MX.order.
   + rewrite IH; trivial. split; auto.
     intros [(E,<-)|IN]; trivial. MX.order.
Qed.

(** * [mem] *)

Fixpoint mem (k : key) (m : t elt) : bool :=
 match m with
  | nil => false
  | (k',_) :: l =>
     match X.compare k k' with
      | Lt => false
      | Eq => true
      | Gt => mem k l
     end
 end.

Lemma mem_spec m x {Hm:Ok m} : mem x m = true <-> In x m.
Proof.
 induction m as [|(k,e') m IH]; simpl.
 - split. discriminate. inversion 1. inversion_clear H0.
 - inversion_clear Hm.
   rewrite In_cons; simpl.
   case X.compare_spec; intros.
   + intuition.
   + split. discriminate. intros [E|(e,IN)]. MX.order.
     SortLt. MX.order.
   + rewrite IH; trivial. split; auto. intros [E|IN]; trivial.
     MX.order.
Qed.

(** * [empty] *)

Definition empty : t elt := nil.

Lemma empty_spec x : find x empty = None.
Proof.
 reflexivity.
Qed.

Global Instance empty_ok : Ok empty.
Proof.
 unfold empty; autok.
Qed.

(** * [is_empty] *)

Definition is_empty (l : t elt) : bool := if l then true else false.

Lemma is_empty_spec m :
 is_empty m = true <-> forall x, find x m = None.
Proof.
 destruct m as [|(k,e) m]; simpl; split; trivial; try discriminate.
 intros H. specialize (H k). now rewrite compare_refl in H.
Qed.

(** * [add] *)

Fixpoint add (k : key) (x : elt) (s : t elt) : t elt :=
 match s with
  | nil => (k,x) :: nil
  | (k',y) :: l =>
     match X.compare k k' with
      | Lt => (k,x)::s
      | Eq => (k,x)::l
      | Gt => (k',y) :: add k x l
     end
 end.

Lemma add_spec1' m x e : find x (add x e m) = Some e.
Proof.
 induction m as [|(k,e') m IH]; simpl.
 - now rewrite compare_refl.
 - case X.compare_spec; simpl; rewrite ?compare_refl; trivial.
   rewrite <- compare_gt_iff. now intros ->.
Qed.

Lemma add_spec2' m x y e : ~X.eq x y -> find y (add x e m) = find y m.
Proof.
 induction m as [|(k,e') m IH]; simpl.
 - case X.compare_spec; trivial; MX.order.
 - case X.compare_spec; simpl; intros; trivial.
   + rewrite <-H. case X.compare_spec; trivial; MX.order.
   + do 2 (case X.compare_spec; trivial; try MX.order).
   + now rewrite IH.
Qed.

Lemma add_spec1 m x e `{!Ok m} : find x (add x e m) = Some e.
Proof. apply add_spec1'. Qed.

Lemma add_spec2 m x y e `{!Ok m} :
 ~X.eq x y -> find y (add x e m) = find y m.
Proof. apply add_spec2'. Qed.

Lemma add_Inf : forall (m:t elt)(x x':key)(e e':elt),
  Inf (x',e') m -> ltk (x',e') (x,e) -> Inf (x',e') (add x e m).
Proof.
 induction m.
 simpl; intuition.
 intros.
 destruct a as (x'',e'').
 inversion_clear H.
 compute in H0,H1.
 simpl; case X.compare; intuition.
Qed.
Local Hint Resolve add_Inf : map.

Global Instance add_ok m x e {Hm:Ok m} : Ok (add x e m).
Proof.
 induction m as [|(y,v) m IH].
 - simpl; intuition.
 - simpl; case (X.compare_spec x y); intuition; inversion_clear Hm;
     constructor; autok.
   apply Inf_eq with (y,v); auto.
Qed.

(** * [remove] *)

Fixpoint remove (k : key) (s : t elt) : t elt :=
 match s with
  | nil => nil
  | (k',x) :: l =>
     match X.compare k k' with
      | Lt => s
      | Eq => l
      | Gt => (k',x) :: remove k l
     end
 end.

Lemma remove_spec1 m x {Hm:Ok m} : find x (remove x m) = None.
Proof.
 induction m as [|(k,e') m IH]; simpl; trivial.
 inversion_clear Hm; chok.
 case X.compare_spec; simpl.
 - intros E. rewrite <- E in H0.
   apply Sort_Inf_NotIn in H0; trivial.
   assert (F := @find_spec m x).
   destruct (find x m); trivial.
   elim H0; exists e. rewrite <- (F e); auto.
 - rewrite <- compare_lt_iff. now intros ->.
 - rewrite <- compare_gt_iff. intros ->; auto.
Qed.

Lemma remove_spec2 m x y {Hm:Ok m} :
  ~X.eq x y -> find y (remove x m) = find y m.
Proof.
 induction m as [|(k,e') m IH]; simpl; trivial.
 inversion_clear Hm.
 case X.compare_spec; simpl; intros E E'; try rewrite IH; auto.
 case X.compare_spec; simpl; trivial; try MX.order.
 intros. rewrite <- E in H0,H1. clear E E'.
 destruct (find y m) eqn:F; trivial.
 apply find_spec in F; trivial.
 SortLt. MX.order.
Qed.

Lemma remove_Inf (m:t elt){Hm : Ok m}(x x':key)(e':elt) :
  Inf (x',e') m -> Inf (x',e') (remove x m).
Proof.
 induction m.
 simpl; intuition.
 intros.
 destruct a as (x'',e'').
 inversion_clear H.
 compute in H0.
 simpl; case X.compare; intuition.
 inversion_clear Hm.
 apply Inf_lt with (x'',e''); auto.
Qed.
Local Hint Resolve remove_Inf : map.

Global Instance remove_ok m x {Hm:Ok m} : Ok (remove x m).
Proof.
 induction m.
 simpl; intuition.
 intros.
 destruct a as (x',e').
 simpl; case X.compare_spec; intuition; inversion_clear Hm; auto.
 constructor; autok.
Qed.

(** * [bindings] *)

Definition bindings (m: t elt) := m.

Lemma bindings_spec1 m x e :
  InA eqke (x,e) (bindings m) <-> MapsTo x e m.
Proof.
 reflexivity.
Qed.

Lemma bindings_spec2 m {Hm:Ok m} : sort ltk (bindings m).
Proof.
 auto.
Qed.

Lemma bindings_spec2w m {Hm:Ok m} : NoDupA eqk (bindings m).
Proof.
 now apply Sort_NoDupA.
Qed.

(** * [singleton] *)

Definition singleton k (e:elt) : t elt := (k,e)::nil.

Lemma singleton_spec x e : bindings (singleton x e) = (x,e)::nil.
Proof. reflexivity. Qed.

Global Instance singleton_ok x e : Ok (singleton x e).
Proof.
 constructor; auto.
Qed.

(** * [fold] *)

Fixpoint fold (A:Type)(f:key->elt->A->A)(m:t elt) (acc:A) :  A :=
  match m with
   | nil => acc
   | (k,e)::m' => fold f m' (f k e acc)
  end.

Lemma fold_spec m : forall (A:Type)(i:A)(f:key->elt->A->A),
  fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (bindings m) i.
Proof.
 induction m as [|(k,e) m IH]; simpl; auto.
Qed.

(** * [equal] *)

Fixpoint equal (cmp:elt->elt->bool)(m m' : t elt) : bool :=
  match m, m' with
   | nil, nil => true
   | (x,e)::l, (x',e')::l' =>
      match X.compare x x' with
       | Eq => cmp e e' && equal cmp l l'
       | _  => false
      end
   | _, _ => false
  end.

Definition Equal m m' := forall y, find y m = find y m'.
Definition Eqdom m m' := forall y, @In elt y m <-> @In elt y m'.
Definition Equiv (R:elt->elt->Prop) m m' :=
  Eqdom m m' /\
  (forall k e e', MapsTo k e m -> MapsTo k e' m' -> R e e').
Definition Equivb (cmp:elt->elt->bool) := Equiv (Cmp cmp).

Lemma equal_1 : forall m m' {Hm:Ok m}{Hm': Ok m'} cmp,
  Equivb cmp m m' -> equal cmp m m' = true.
Proof.
 induction m as [|(k,e) m IH]; destruct m' as [|(k',e') m']; simpl.
 - trivial.
 - intros _ _ cmp (H,_). exfalso. specialize (H k').
   rewrite In_nil, In_cons in H. rewrite H. now left.
 - intros _ _ cmp (H,_). exfalso. specialize (H k).
   rewrite In_nil, In_cons in H. rewrite <- H. now left.
 - intros Hm Hm' cmp E.
   inversion_clear Hm; inversion_clear Hm'.
   case X.compare_spec; intros E'.
   + apply andb_true_intro; split.
     * eapply E; eauto. apply InA_cons; now left.
     * apply IH; clear IH; trivial.
       destruct E as (E1,E2). split.
       { intros x. clear E2.
         split; intros; SortLt.
         specialize (E1 x); rewrite 2 In_cons in E1; simpl in E1.
         destruct E1 as ([E1|E1],_); eauto. MX.order.
         specialize (E1 x); rewrite 2 In_cons in E1; simpl in E1.
         destruct E1 as (_,[E1|E1]); eauto. MX.order. }
       { intros x xe xe' Hx HX'. eapply E2; eauto. }
   + assert (IN : In k ((k',e')::m')).
     { apply E. apply In_cons; now left. }
     apply In_cons in IN. simpl in IN. destruct IN as [?|IN]. MX.order.
     SortLt. MX.order.
   + assert (IN : In k' ((k,e)::m)).
     { apply E. apply In_cons; now left. }
     apply In_cons in IN. simpl in IN. destruct IN as [?|IN]. MX.order.
     SortLt. MX.order.
Qed.

Lemma equal_2 m m' {Hm:Ok m}{Hm':Ok m'} cmp :
  equal cmp m m' = true -> Equivb cmp m m'.
Proof.
 revert m' Hm'.
 induction m as [|(k,e) m IH]; destruct m' as [|(k',e') m']; simpl;
  try discriminate.
 - split. red. reflexivity. inversion 1.
 - intros Hm'. case X.compare_spec; try discriminate.
   rewrite andb_true_iff. intros E (C,EQ).
   inversion_clear Hm; inversion_clear Hm'.
   apply IH in EQ; trivial.
   destruct EQ as (E1,E2).
   split.
   + intros x. rewrite 2 In_cons; simpl. rewrite <- (E1 x).
     intuition; now left; MX.order.
   + intros x ex ex'. unfold MapsTo in *. rewrite 2 InA_cons, 2 eqke_def.
     intuition; subst.
     * trivial.
     * SortLt. MX.order.
     * SortLt. MX.order.
     * eapply E2; eauto.
Qed.

Lemma equal_spec cmp m m' {Hm:Ok m}{Hm':Ok m'} :
  equal cmp m m' = true <-> Equivb cmp m m'.
Proof.
 split. now apply equal_2. now apply equal_1.
Qed.

(** This lemma isn't part of the spec of [Equivb], but is used in [Tries.MMaps.AVL] *)

Lemma equal_cons : forall cmp l1 l2 x y, Ok (x::l1) -> Ok (y::l2) ->
  eqk x y -> cmp (snd x) (snd y) = true ->
  (Equivb cmp l1 l2 <-> Equivb cmp (x :: l1) (y :: l2)).
Proof.
 intros.
 inversion H; subst.
 inversion H0; subst.
 destruct x; destruct y; compute in H1, H2.
 split; intros.
 apply equal_2; auto.
 simpl.
 case X.compare_spec; intros; try MX.order.
 rewrite H2; simpl.
 apply equal_1; auto.
 apply equal_2; auto.
 generalize (equal_1 H3).
 simpl.
 case X.compare_spec; try discriminate.
 rewrite andb_true_iff. intuition.
Qed.

Variable elt':Type.

(** * [map] and [mapi] *)

Definition map (f:elt -> elt') (m:t elt) : t elt' :=
  List.map (fun '(k,e) => (k,f e)) m.

Definition mapi (f: key -> elt -> elt') (m:t elt) : t elt' :=
  List.map (fun '(k,e) => (k,f k e)) m.

End Elt.
Arguments find {elt} k m.
Section Elt2.
Variable elt elt' : Type.

(** Specification of [map] *)

Lemma map_spec (f:elt->elt')(m:t elt) :
  bindings (map f m) = List.map (fun '(k,e) => (k,f e)) (bindings m).
Proof.
 reflexivity.
Qed.

Lemma map_Inf (f:elt->elt') m x e e' :
  Inf (x,e) m -> Inf (x,e') (map f m).
Proof.
 induction m as [|(x0,e0) m IH]; simpl; auto.
 inversion_clear 1; auto.
Qed.
Local Hint Resolve map_Inf : map.

Global Instance map_ok (f:elt->elt')(m: t elt){Hm : Ok m} : Ok (map f m).
Proof.
 induction m as [|(x,e) m IH]; simpl; autok.
 inversion_clear Hm. constructor; eautok.
Qed.

(** Specification of [mapi] *)

Lemma mapi_spec (f:key->elt->elt')(m:t elt) :
  bindings (mapi f m) = List.map (fun '(k,e) => (k,f k e)) (bindings m).
Proof.
 reflexivity.
Qed.

Lemma mapi_Inf (f:key->elt->elt') m x e :
  Inf (x,e) m -> Inf (x,f x e) (mapi f m).
Proof.
 induction m as [|(x0,e0) m IH]; simpl; auto.
 inversion_clear 1; auto.
Qed.
Local Hint Resolve mapi_Inf : map.

Global Instance mapi_ok (f:key->elt->elt') m {Hm : Ok m} :
  Ok (mapi f m).
Proof.
 induction m as [|(x,e) m IH]; simpl; autok.
 inversion_clear Hm; constructor; autok.
Qed.

End Elt2.
Section Elt3.

(** * [merge] *)

Variable elt elt' elt'' : Type.
Variable f : key -> option elt -> option elt' -> option elt''.

Definition option_cons {A}(k:key)(o:option A)(l:list (key*A)) :=
  match o with
   | Some e => (k,e)::l
   | None => l
  end.

Fixpoint merge_l (m : t elt) : t elt'' :=
  match m with
   | nil => nil
   | (k,e)::l => option_cons k (f k (Some e) None) (merge_l l)
  end.

Fixpoint merge_r (m' : t elt') : t elt'' :=
  match m' with
   | nil => nil
   | (k,e')::l' => option_cons k (f k None (Some e')) (merge_r l')
  end.

Fixpoint merge (m : t elt) : t elt' -> t elt'' :=
  match m with
   | nil => merge_r
   | (k,e) :: l =>
      fix merge_aux (m' : t elt') : t elt'' :=
        match m' with
         | nil => merge_l m
         | (k',e') :: l' =>
            match X.compare k k' with
             | Lt => option_cons k (f k (Some e) None) (merge l m')
             | Eq => option_cons k (f k (Some e) (Some e')) (merge l l')
             | Gt => option_cons k' (f k' None (Some e')) (merge_aux l')
            end
        end
  end.

Notation oee' := (option elt * option elt')%type.

Fixpoint combine (m : t elt) : t elt' -> t oee' :=
  match m with
   | nil => map (fun e' => (None,Some e'))
   | (k,e) :: l =>
      fix combine_aux (m':t elt') : list (key * oee') :=
        match m' with
         | nil => map (fun e => (Some e,None)) m
         | (k',e') :: l' =>
            match X.compare k k' with
             | Lt => (k,(Some e, None))::combine l m'
             | Eq => (k,(Some e, Some e'))::combine l l'
             | Gt => (k',(None,Some e'))::combine_aux l'
            end
        end
  end.

Definition fold_right_pair {A B C}(f: A->B->C->C)(l:list (A*B))(i:C) :=
  List.fold_right (fun p => f (fst p) (snd p)) i l.

Definition merge' m m' :=
  let m0 : t oee' := combine m m' in
  let m1 : t (option elt'') := mapi (fun k p => f k (fst p) (snd p)) m0 in
  fold_right_pair (option_cons (A:=elt'')) m1 nil.

Lemma merge_equiv : forall m m', merge' m m' = merge m m'.
Proof.
 unfold merge'.
 induction m as [|(k,e) m IHm]; intros.
 - (* merge_r *)
   simpl.
   induction m' as [|(k',e') m' IHm']; simpl; rewrite ?IHm'; auto.
 - induction m' as [|(k',e') m' IHm']; simpl.
   + f_equal.
     (* merge_l *)
     clear k e IHm.
     induction m as [|(k,e) m IHm]; simpl; rewrite ?IHm; auto.
   + elim X.compare_spec; intros; simpl; f_equal.
     * apply IHm.
     * apply IHm.
     * apply IHm'.
Qed.

Lemma combine_Inf :
  forall m m' (x:key)(e:elt)(e':elt')(e'':oee'),
  Inf (x,e) m ->
  Inf (x,e') m' ->
  Inf (x,e'') (combine m m').
Proof.
 induction m.
 - intros. simpl. eapply map_Inf; eauto.
 - induction m'; intros.
   + destruct a.
     replace (combine ((t0, e0) :: m) nil) with
      (map (fun e => (Some e,None (A:=elt'))) ((t0,e0)::m)); auto.
     eapply map_Inf; eauto.
   + simpl.
     destruct a as (k,e0); destruct a0 as (k',e0').
     elim X.compare_spec.
     * inversion_clear H; auto.
     * inversion_clear H; auto.
     * inversion_clear H0; auto.
Qed.
Local Hint Resolve combine_Inf : map.

Global Instance combine_ok m m' {Hm : Ok m}{Hm' : Ok m'} :
 Ok (combine m m').
Proof.
 revert m' Hm'.
 induction m.
 - intros; clear Hm. simpl. apply map_ok; auto.
 - induction m'; intros.
   + clear Hm'.
     destruct a.
     replace (combine ((t0, e) :: m) nil) with
      (map (fun e => (Some e,None (A:=elt'))) ((t0,e)::m)); auto.
     apply map_ok; auto.
   + simpl.
     destruct a as (k,e); destruct a0 as (k',e').
     inversion_clear Hm; inversion_clear Hm'.
     case X.compare_spec; [intros Heq| intros Hlt| intros Hlt];
      constructor; autok.
     * assert (Inf (k, e') m') by (apply Inf_eq with (k',e'); auto).
       exact (combine_Inf _ H0 H3).
     * assert (Inf (k, e') ((k',e')::m')) by auto.
       exact (combine_Inf _ H0 H3).
     * assert (Inf (k', e) ((k,e)::m)) by auto.
       exact (combine_Inf _  H3 H2).
Qed.

Global Instance merge_ok m m' {Hm : Ok m}{Hm' : Ok m'} :
  Ok (merge m m').
Proof.
 intros.
 rewrite <- merge_equiv.
 unfold merge'.
 assert (Hmm':=@combine_ok m m' _ _).
 set (l0:=combine m m') in *; clearbody l0.
 set (f':= fun k p => f k (fst p) (snd p)).
 assert (H1:=@mapi_ok _ _ f' l0 _).
 set (l1:=mapi f' l0) in *; clearbody l1.
 clear f' f Hmm' l0 Hm Hm' m m'.
 (* Ok fold_right_pair *)
 induction l1.
 - simpl; autok.
 - inversion_clear H1. chok.
   destruct a; destruct o; auto.
   simpl.
   constructor; autok.
   clear IHl1.
   (* Inf fold_right_pair *)
   induction l1.
   + simpl; auto.
   + destruct a; destruct o; simpl; autok.
     * inversion_clear H0; auto.
     * inversion_clear H0. inversion_clear H.
       compute in H1.
       apply IHl1; auto.
       apply Inf_lt with (t1, None); auto.
Qed.

Definition at_least_one (o:option elt)(o':option elt') :=
  match o, o' with
   | None, None => None
   | _, _  => Some (o,o')
  end.

Lemma combine_spec m m' {Hm : Ok m}{Hm' : Ok m'} (x:key) :
  find x (combine m m') = at_least_one (find x m) (find x m').
Proof.
 revert m' Hm'.
 induction m.
 intros.
 simpl.
 induction m'.
 intros; simpl; auto.
 simpl; destruct a.
 simpl; destruct (X.compare x t0); simpl; auto.
 inversion_clear Hm'; auto.
 induction m'.
 (* m' = nil *)
 intros; destruct a; simpl.
 destruct (X.compare_spec x t0) as [ |Hlt|Hlt]; simpl; auto.
 inversion_clear Hm; clear H0 Hlt Hm' IHm t0.
 induction m; simpl; auto.
 inversion_clear H.
 destruct a.
 simpl; destruct (X.compare x t0); simpl; auto.
 (* m' <> nil *)
 intros.
 destruct a as (k,e); destruct a0 as (k',e'); simpl.
 inversion Hm; inversion Hm'; subst.
 destruct (X.compare_spec k k'); simpl;
  destruct (X.compare_spec x k);
   MX.order || destruct (X.compare_spec x k');
               simpl; try MX.order; auto.
 - rewrite IHm; auto; simpl. elim X.compare_spec; auto; MX.order.
 - rewrite IHm; auto; simpl. elim X.compare_spec; auto; MX.order.
 - rewrite IHm; auto; simpl. elim X.compare_spec; auto; MX.order.
 - change (find x (combine ((k, e) :: m) m') = Some (Some e, find x m')).
   rewrite IHm'; auto; simpl. elim X.compare_spec; auto; MX.order.
 - change (find x (combine ((k, e) :: m) m') = at_least_one None (find x m')).
   rewrite IHm'; auto; simpl. elim X.compare_spec; auto; MX.order.
 - change (find x (combine ((k, e) :: m) m') =
         at_least_one (find x m) (find x m')).
   rewrite IHm'; auto; simpl. elim X.compare_spec; auto; MX.order.
Qed.

Definition at_least_one_then_f k (o:option elt)(o':option elt') :=
  match o, o' with
   | None, None => None
   | _, _  => f k o o'
  end.

Lemma merge_spec0 m m' {Hm : Ok m}{Hm' : Ok m'} (x:key) :
  exists y, X.eq y x /\
  find x (merge m m') = at_least_one_then_f y (find x m) (find x m').
Proof.
 intros.
 rewrite <- merge_equiv.
 unfold merge'.
 assert (H:=combine_spec x).
 assert (H2:=@combine_ok m m' _ _).
 set (f':= fun k p => f k (fst p) (snd p)).
 set (m0 := combine m m') in *; clearbody m0.
 set (o:=find x m) in *; clearbody o.
 set (o':=find x m') in *; clearbody o'.
 clear Hm Hm' m m'. revert H.
 match goal with |- ?G =>
   assert (G/\(find x m0 = None ->
               find x (fold_right_pair option_cons (mapi f' m0) nil) = None));
    [|intuition] end.
 induction m0; simpl in *; intuition.
 - exists x; split; [easy|].
   destruct o; destruct o'; simpl in *; try discriminate; auto.
 - destruct a as (k,(oo,oo')); simpl in *.
   inversion_clear H2.
   destruct (X.compare_spec x k) as [Heq|Hlt|Hlt]; simpl in *.
   + (* x = k *)
     exists k; split; [easy|].
     assert (at_least_one_then_f k o o' = f k oo oo').
     { destruct o; destruct o'; simpl in *; inversion_clear H; auto. }
     rewrite H2.
     unfold f'; simpl.
     destruct (f k oo oo'); simpl.
     * elim X.compare_spec; trivial; try MX.order.
     * destruct (IHm0 H0) as (_,H4); apply H4; auto.
       case_eq (find x m0); intros; auto.
       assert (eqk (elt:=oee') (k,(oo,oo')) (x,(oo,oo'))).
       now compute.
       symmetry in H5.
       destruct (Sort_Inf_NotIn H0 (Inf_eq H5 H1)).
       exists p; apply find_spec; auto.
   + (* x < k *)
     destruct (f' k (oo,oo')); simpl.
     * elim X.compare_spec; trivial; try MX.order.
       destruct o; destruct o'; simpl in *; try discriminate; auto.
       now exists x.
     * apply IHm0; trivial.
       rewrite <- H.
       case_eq (find x m0); intros; auto.
       assert (ltk (elt:=oee') (x,(oo,oo')) (k,(oo,oo'))).
       red; auto.
       destruct (Sort_Inf_NotIn H0 (Inf_lt H3 H1)).
       exists p; apply find_spec; auto.
   + (* k < x *)
     unfold f'; simpl.
     destruct (f k oo oo'); simpl.
     * elim X.compare_spec; trivial; try MX.order.
       intros. apply IHm0; auto.
     * apply IHm0; auto.

 - (* None -> None *)
   destruct a as (k,(oo,oo')).
   simpl.
   inversion_clear H2.
   destruct (X.compare_spec x k) as [Hlt|Heq|Hlt]; try discriminate.
   + (* x < k *)
     unfold f'; simpl.
     destruct (f k oo oo'); simpl.
     elim X.compare_spec; trivial; try MX.order. intros.
     apply IHm0; auto.
     case_eq (find x m0); intros; auto.
     assert (ltk (elt:=oee') (x,(oo,oo')) (k,(oo,oo'))).
     now compute.
     destruct (Sort_Inf_NotIn H0 (Inf_lt H3 H1)).
     exists p; apply find_spec; auto.
   + (* k < x *)
     unfold f'; simpl.
     destruct (f k oo oo'); simpl.
     elim X.compare_spec; trivial; try MX.order. intros.
     apply IHm0; auto.
     apply IHm0; auto.
Qed.

(** Specification of [merge] *)

Lemma merge_spec1 m m' x {Hm : Ok m}{Hm' : Ok m'} :
  In x m \/ In x m' ->
  exists y, X.eq y x /\
    find x (merge m m') = f y (find x m) (find x m').
Proof.
 intros.
 destruct (merge_spec0 x) as (y,(Hy,H')).
 exists y; split; [easy|]. rewrite H'.
 destruct H as [(e,H)|(e,H)];
  apply find_spec in H; trivial; rewrite H; simpl; auto.
 now destruct (find x m).
Qed.

Lemma merge_spec2 m m' x {Hm : Ok m}{Hm' : Ok m'} :
  In x (merge m m') -> In x m \/ In x m'.
Proof.
 intros.
 destruct H as (e,H).
 apply find_spec in H; auto using merge_ok.
 destruct (merge_spec0 x) as (y,(Hy,H')).
 rewrite H in H'.
 destruct (find x m) eqn:F.
 - apply find_spec in F; eauto.
 - destruct (find x m') eqn:F'.
   + apply find_spec in F'; eauto.
   + simpl in H'. discriminate.
Qed.

End Elt3.

Definition cardinal {elt} (m:t elt) := length m.
Lemma cardinal_spec {elt} (m:t elt) : cardinal m = length (bindings m).
Proof. reflexivity. Qed.

Definition MapsTo {elt} := @PX.MapsTo elt.
Definition In {elt} := @PX.In elt.

Instance MapsTo_compat {elt} :
  Proper (X.eq==>Logic.eq==>Logic.eq==>iff) (@MapsTo elt).
Proof.
 intros x x' Hx e e' <- m m' <-. unfold MapsTo. now rewrite Hx.
Qed.

Definition compare {elt} cmp (m m':t elt) :=
  list_compare (pair_compare X.compare cmp) m m'.

Definition compare_spec {elt} cmp (m m':t elt) {Hm : Ok m}{Hm' : Ok m'}:
 compare cmp m m' =
 list_compare (pair_compare X.compare cmp) m m'.
Proof. reflexivity. Qed.

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

Lemma partition_spec {elt} (f:key->elt->bool) m `{!Ok m} :
 prodmap (@bindings _) (partition f m) =
  List.partition (fun '(k,e) => f k e) (bindings m).
Proof. unfold bindings, partition. now destruct List.partition. Qed.

Lemma for_all_spec {elt}(f:key->elt->bool) m :
 for_all f m = List.forallb (fun '(k,e) => f k e) (bindings m).
Proof. reflexivity. Qed.

Lemma exists_spec {elt}(f:key->elt->bool) m :
 exists_ f m = List.existsb (fun '(k,e) => f k e) (bindings m).
Proof. reflexivity. Qed.

Instance filter_ok {elt} f (m:t elt) : Ok m -> Ok (filter f m).
Proof.
 eapply filter_sort with (eqA:=eqke); eauto with *.
Qed.

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

Instance partition_ok1 {elt} f (m:t elt) : Ok m -> Ok (fst (partition f m)).
Proof.
 rewrite partition_fst; eauto with *.
Qed.

Instance partition_ok2 {elt} f (m:t elt) : Ok m -> Ok (snd (partition f m)).
Proof.
 rewrite partition_snd; eauto with *.
Qed.

End MakeRaw.

Module Make (X: OrderedType) <: S X.
 Module Raw := MakeRaw X.
 Include Raw.Pack X Raw.
End Make.
