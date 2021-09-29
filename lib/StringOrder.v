(** * Ordering strings *)

From Coq Require Import Ascii String Orders OrderedType.
From Tries Require Import AsciiOrder.

Fixpoint string_compare (x y: string) : comparison :=
  match x, y with
  | EmptyString, EmptyString => Eq
  | EmptyString, String _ _ => Lt
  | String _ _, EmptyString => Gt
  | String x1 xs, String y1 ys =>
      match ascii_compare x1 y1 with
      | Eq => string_compare xs ys
      | Lt => Lt
      | Gt => Gt
      end
  end.

Lemma string_compare_refl:
  forall x, string_compare x x = Eq.
Proof.
  induction x; simpl. auto. rewrite ascii_compare_refl. auto.
Qed.

Lemma string_compare_eq:
  forall x y, string_compare x y = Eq -> x = y.
Proof.
  induction x; destruct y; simpl; intros.
- auto.
- discriminate.
- discriminate.
- destruct (ascii_compare a a0) eqn:E; try discriminate.
  apply ascii_compare_eq in E. apply IHx in H. congruence.
Qed.

Lemma string_compare_lt_trans:
  forall x y z, string_compare x y = Lt -> string_compare y z = Lt -> string_compare x z = Lt.
Proof.
  induction x; destruct y, z; simpl; intros; try congruence.
  destruct (ascii_compare a a0) eqn:C1; try discriminate.
- apply ascii_compare_eq in C1; subst a0.
  destruct (ascii_compare a a1); eauto.
- destruct (ascii_compare a0 a1) eqn:C2; try discriminate.
  + apply ascii_compare_eq in C2; subst a0. rewrite C1. auto.
  + erewrite ascii_compare_lt_trans by eauto. auto.
Qed.

Lemma string_compare_antisym:
  forall x y, CompOpp (string_compare x y) = string_compare y x.
Proof.
  induction x; destruct y; simpl; auto.
  rewrite <- (ascii_compare_antisym a0 a).
  destruct (ascii_compare a0 a); simpl; auto.
Qed.

(** Implementing the [OrderedType] interface *)

Module OrderedString <: OrderedType.

Definition t := string.
Definition eq (x y: t) := x = y.
Definition lt (x y: t) := string_compare x y = Lt.

Lemma eq_refl : forall x : t, eq x x.
Proof (@eq_refl t).
Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof (@eq_sym t).
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof (@eq_trans t).

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof string_compare_lt_trans.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof.
  unfold lt, eq; intros; red; intros. subst y. 
  rewrite string_compare_refl in H. discriminate.
Qed.

Definition compare (x y : t) : Compare lt eq x y.
Proof.
  destruct (string_compare x y) eqn:AC.
- apply EQ. apply string_compare_eq; auto.  
- apply LT. assumption.
- apply GT. red. rewrite <- string_compare_antisym. rewrite AC; auto.
Defined.

Definition eq_dec (x y : t) : {x = y} + {x <> y}.
Proof.
  destruct (string_compare x y) eqn:AC.
- left. apply string_compare_eq; auto.
- right; red; intros; subst y. rewrite string_compare_refl in AC; discriminate.
- right; red; intros; subst y. rewrite string_compare_refl in AC; discriminate.
Defined.

End OrderedString.

Require Import Extraction ExtrOcamlBasic ExtrOcamlString.

Extract Constant ascii_compare =>
  "fun (c1: char) (c2: char) -> if c1 = c2 then Eq else if c1 < c2 then Lt else Gt".
