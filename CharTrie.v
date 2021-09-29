(** * Dictionaries implemented as character-based tries *)

(* Author: Xavier Leroy, Collège de France and Inria.
   Copyright: Inria.
   License: BSD-3-Clause. *)

From Coq Require Import Ascii String OrderedType.
From Tries Require Import AsciiOrder.

Module AO := OrderedAscii.
Module AOF := OrderedTypeFacts AO.

Ltac inv H := inversion H; subst; clear H.

Module Stringmap.

Module Raw.

Section STRINGMAP.

Context {A: Type}.

(** ** Representation of tries *)

(** The data structure is a trie where each node carries a mapping from
    characters (Coq type [ascii]) to subtrees.  In other words, this is
    a trie with a branching factor of 256 at each node.
    The mapping from characters to subtrees is represented sparsely
    as a sorted association list, with type [forest] below. *)

Inductive tree :=
  | Empty: tree
  | Node : option A -> forest -> tree
with forest : Type :=
  | Nil : forest
  | Cons: ascii -> tree -> forest -> forest.

Fixpoint In_forest (x: ascii) (f: forest) : Prop :=
  match f with
  | Nil => False
  | Cons k t f => x = k \/ In_forest x f
  end.

(** The well-formedness invariant states that the association lists
    are sorted, i.e. characters occur in increasing order. *)

Inductive wf: tree -> Prop :=
  | wf_Empty: wf Empty
  | wf_Node: forall ov f, wff f -> wf (Node ov f)
with wff: forest -> Prop :=
  | wff_Nil: wff Nil
  | wff_Cons: forall k t f, 
      wf t -> wff f ->
      (forall x, In_forest x f -> AO.lt k x) ->
      wff (Cons k t f).

(** ** Basic operations: [empty], [get], [set], [remove] *)

Fixpoint get (s: string) (m: tree) {struct m} : option A :=
  match m, s with
  | Empty, _ => None
  | Node v _, EmptyString => v
  | Node _ cl, String x s => getf x s cl
  end
with getf (x: ascii) (s: string) (f: forest) : option A :=
  match f with
  | Nil => None
  | Cons k t f =>
      match AO.compare x k with
      | LT _ => None
      | EQ _ => get s t
      | GT _ => getf x s f
      end
  end.

Fixpoint singleton (s: string) (v: A) : tree :=
  match s with
  | EmptyString => Node (Some v) Nil
  | String x s => Node None (Cons x (singleton s v) Nil)
  end.

Fixpoint set (s: string) (v: A) (m: tree) {struct m} : tree :=
  match m, s with
  | Empty, _ => singleton s v
  | Node _ cl, EmptyString => Node (Some v) cl
  | Node v0 cl, String x s => Node v0 (setf x s v cl)
  end
with setf (x: ascii) (s: string) (v: A) (f: forest) {struct f} : forest :=
  match f with
  | Nil => Cons x (singleton s v) Nil
  | Cons k c f' =>
      match AO.compare x k with
      | LT _ => Cons x (singleton s v) f
      | EQ _ => Cons k (set s v c) f'
      | GT _ => Cons k c (setf x s v f')
      end
  end.

(** Smart constructors for [Node] and [Cons] that avoid the creation
    of trivially empty trees or forests. *)

Definition Node' (ov: option A) (f: forest) : tree :=
  match ov, f with
  | None, Nil => Empty
  | _, _ => Node ov f
  end.

Definition Cons' (x: ascii) (t: tree) (f: forest) : forest :=
  match t with Empty => f | _ => Cons x t f end.

Fixpoint remove (s: string) (m: tree) {struct m} : tree :=
  match m, s with
  | Empty, _ => Empty
  | Node _ cl, EmptyString => Node' None cl
  | Node v0 cl, String x s => Node' v0 (removef x s cl)
  end
with removef (x: ascii) (s: string) (f: forest) {struct f} : forest :=
  match f with
  | Nil => Nil
  | Cons k c f' =>
      match AO.compare x k with
      | LT _ => f
      | EQ _ => Cons' k (remove s c) f'
      | GT _ => Cons k c (removef x s f')
      end
  end.

(** ** Well-formedness properties for the basic operations *)

Lemma getf_In:
  forall x s v f, getf x s f = Some v -> In_forest x f.
Proof.
  induction f; simpl; intros.
- discriminate.
- destruct (AO.compare x a).
+ discriminate.
+ red in e; auto.
+ auto.
Qed.

Lemma getf_notIn:
  forall x s f, ~(In_forest x f) -> getf x s f = None.
Proof.
  intros. destruct (getf x s f) as [v|] eqn:G; auto. elim H. eapply getf_In; eauto.
Qed.

Lemma wf_singleton: forall v s, wf (singleton s v).
Proof.
  induction s as [ | x s]; simpl.
- repeat constructor.
- repeat constructor. auto. simpl; tauto.
Qed.

Remark In_setf:
  forall k x s v f, In_forest k (setf x s v f) <-> k = x \/ In_forest k f.
Proof.
  induction f; simpl.
- tauto.
- destruct (AO.compare x a); simpl.
+ tauto.
+ red in e; subst x. tauto.
+ rewrite IHf. tauto.
Qed.

Lemma wf_set: forall m, wf m -> forall s v, wf (set s v m)
with wf_setf: forall f, wff f -> forall x s v, wff (setf x s v f).
Proof.
- destruct 1; simpl; intros.
+ apply wf_singleton.
+ destruct s as [ | x s]. constructor; auto. constructor; apply wf_setf; auto.
- destruct 1; simpl; intros.
+ repeat constructor. apply wf_singleton. simpl; tauto.
+ destruct (AO.compare x k).
* constructor. apply wf_singleton. constructor; auto. 
  simpl; intros y [E|E]. subst; auto. eapply AO.lt_trans; eauto.
* constructor. apply wf_set; auto. auto. auto.
* constructor. auto. apply wf_setf; auto. 
  intros y I. rewrite In_setf in I; destruct I as [I|I].
  subst; auto. auto.
Qed.

Lemma wf_Node': forall ov f, wff f -> wf (Node' ov f).
Proof.
  unfold Node'; intros; destruct ov, f; constructor; auto.
Qed.

Lemma get_Node': forall s ov f,
  get s (Node' ov f) = get s (Node ov f).
Proof.
  intros. unfold Node'; destruct ov, f; auto. simpl. destruct s; auto.
Qed.

Lemma wf_Cons': forall k t f,
  wff (Cons k t f) -> wff (Cons' k t f).
Proof.
  unfold Cons'; intros. destruct t; auto. inv H; auto.
Qed.

Lemma In_Cons': forall x k t f,
  In_forest x (Cons' k t f) -> x = k \/ In_forest x f.
Proof.
  unfold Cons'; intros. destruct t; auto.
Qed. 

Lemma getf_Cons': forall x s k t f,
  wff (Cons k t f) ->
  getf x s (Cons' k t f) = getf x s (Cons k t f).
Proof.
  unfold Cons'; intros. destruct t; auto. simpl. inv H.
  assert (P: ~AO.lt k x -> getf x s f = None).
  { intros. apply getf_notIn. red; intros; elim H; auto. }
  destruct (AO.compare x k); auto.
  apply P. apply AOF.lt_not_gt; auto.
  apply P. apply AOF.eq_not_gt; auto.
Qed.

Remark In_removef:
  forall k x s f, In_forest k (removef x s f) -> In_forest k f.
Proof.
  induction f; simpl.
- tauto.
- destruct (AO.compare x a); simpl.
+ tauto.
+ red in e; subst x. intros. eapply In_Cons'; eauto.
+ tauto.
Qed.

Lemma wf_remove: forall m, wf m -> forall s, wf (remove s m)
with wf_removef: forall f, wff f -> forall x s, wff (removef x s f).
Proof.
Local Opaque Node'.
- destruct 1; simpl; intros.
+ constructor.
+ destruct s as [ | x s]; apply wf_Node'; auto.
- destruct 1; simpl; intros.
+ constructor.
+ destruct (AO.compare x k).
* constructor; auto.
* apply wf_Cons'. constructor; auto.
* constructor; auto. intros. apply H1. eapply In_removef; eauto.
Qed.

(** ** Good variable properties for the basic operations *)

Lemma gsings: forall v s, get s (singleton s v) = Some v.
Proof.
  induction s as [ | x s]; simpl. 
- auto.
- AOF.elim_comp_eq x x. auto.
Qed.

Lemma gsingo: forall v s s', s' <> s -> get s' (singleton s v) = None.
Proof.
  induction s as [ | x s]; destruct s' as [ | x' s']; intros; simpl.
- congruence.
- auto.
- auto.
- destruct (AO.compare x' x); auto. 
  apply IHs. red in e; congruence.
Qed.

Lemma gss: forall m, wf m -> forall v s, get s (set s v m) = Some v
with gssf: forall f, wff f -> forall x s v, getf x s (setf x s v f) = Some v.
Proof.
- destruct 1; simpl; intros.
+ apply gsings.
+ destruct s as [ | x s]. auto. apply gssf; auto.
- destruct 1; simpl; intros.
+ AOF.elim_comp_eq x x. apply gsings.
+ destruct (AO.compare x k); simpl.
* AOF.elim_comp_eq x x. apply gsings.
* AOF.elim_comp_eq x k. apply gss; auto.
* AOF.elim_comp_gt x k. apply gssf; auto.
Qed.

Lemma gso:
  forall m, wf m ->
  forall v s s', 
  s' <> s -> get s' (set s v m) = get s' m
with gsof:
  forall f, wff f ->
  forall x s v x' s',
  String x' s' <> String x s -> getf x' s' (setf x s v f) = getf x' s' f.
Proof.
- destruct 1; simpl; intros.
+ apply gsingo; auto.
+ destruct s as [ | x s]; destruct s' as [ | x' s']; simpl.
* congruence.
* auto.
* auto.
* apply gsof; auto.
- destruct 1; intros; simpl.
+ destruct (AO.compare x' x); auto.
  red in e. apply gsingo; congruence.
+ destruct (AO.compare x k); simpl.
* destruct (AO.compare x' x).
** AOF.elim_comp_lt x' k. auto. eapply AO.lt_trans; eauto.
** red in e; subst x'. AOF.elim_comp_lt x k. apply gsingo. congruence.
** auto.
* destruct (AO.compare x' k); auto. apply gso; auto. red in e; red in e0; congruence.
* destruct (AO.compare x' k); auto.
Qed.

Lemma grs: forall m, wf m -> forall s, get s (remove s m) = None
with grsf: forall f, wff f -> forall x s, getf x s (removef x s f) = None.
Proof.
- destruct 1; intros; simpl.
+ auto.
+ destruct s as [ | x s]; rewrite get_Node'. auto. apply grsf; auto.
- destruct 1; intros; simpl.
+ auto.
+ destruct (AO.compare x k); simpl.
* AOF.elim_comp_lt x k. auto.
* rewrite getf_Cons'. simpl. AOF.elim_comp_eq x k. apply grs; auto. 
  constructor; auto using wf_remove.
* AOF.elim_comp_gt x k. apply grsf; auto.
Qed.

Lemma gro: forall m, wf m -> forall s s', s' <> s -> get s' (remove s m) = get s' m
with grof: forall f, wff f -> forall x s x' s', String x' s' <> String x s -> getf x' s' (removef x s f) = getf x' s' f.
Proof.
- destruct 1; intros; simpl.
+ auto.
+ destruct s as [ | x s]; destruct s' as [ | x' s']; subst; rewrite get_Node'; simpl.
* congruence.
* auto.
* auto.
* apply grof; auto.
- destruct 1; intros; simpl.
+ auto.
+ destruct (AO.compare x k); simpl.
* auto.
* rewrite getf_Cons'. simpl. destruct (AO.compare x' k); auto. 
  apply gro; auto. red in e; red in e0; congruence.
  constructor; auto using wf_remove.
* destruct (AO.compare x' k); auto.
Qed.

End STRINGMAP.

Arguments tree: clear implicits.

End Raw.

(** ** Wrapping the data type and its well-formedness invariant in a sigma type *)

Definition t (A: Type) := { m: Raw.tree A | Raw.wf m }.

Definition empty (A: Type) : t A := exist _ Raw.Empty Raw.wf_Empty.

Definition get {A: Type} (s: string) (m: t A) : option A :=
  Raw.get s (proj1_sig m).

Definition set {A: Type} (s: string) (v: A) (m: t A) : t A :=
  exist _ (Raw.set s v (proj1_sig m)) (Raw.wf_set (proj1_sig m) (proj2_sig m) s v).

Definition remove {A: Type} (s: string) (m: t A) : t A :=
  exist _ (Raw.remove s (proj1_sig m)) (Raw.wf_remove (proj1_sig m) (proj2_sig m) s).

Theorem gempty: forall (A: Type) s, get s (empty A) = None.
Proof. intros; reflexivity. Qed.

Theorem gss: forall (A: Type) s v (m: t A), get s (set s v m) = Some v.
Proof. intros; apply Raw.gss. apply proj2_sig. Qed.

Theorem gso: forall (A: Type) s s' v (m: t A), s' <> s -> get s' (set s v m) = get s' m.
Proof. intros; apply Raw.gso; auto. apply proj2_sig. Qed.

Theorem gsspec: forall (A: Type) s s' v (m: t A),
  get s' (set s v m) = if string_dec s' s then Some v else get s' m.
Proof. intros. destruct (string_dec s' s). subst; apply gss. apply gso; auto. Qed.

Theorem grs: forall (A: Type) s (m: t A), get s (remove s m) = None.
Proof. intros; apply Raw.grs. apply proj2_sig. Qed.

Theorem gro: forall (A: Type) s s' (m: t A), s' <> s -> get s' (remove s m) = get s' m.
Proof. intros; apply Raw.gro; auto. apply proj2_sig. Qed.

Theorem grspec: forall (A: Type) s s' (m: t A),
  get s' (remove s m) = if string_dec s' s then None else get s' m.
Proof. intros. destruct (string_dec s' s). subst; apply grs. apply gro; auto. Qed.

End Stringmap.
