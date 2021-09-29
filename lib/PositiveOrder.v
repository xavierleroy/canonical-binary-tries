(** * Ordering positive numbers *)

From Coq Require Import ZArith Lia Orders OrderedType.

Local Open Scope positive_scope.

(** Implementing the [OrderedType] interface *)

Module OrderedPositive <: OrderedType.

Definition t := positive.
Definition eq (x y: t) := x = y.
Definition lt (x y: t) := x < y.

Lemma eq_refl : forall x : t, eq x x.
Proof (@eq_refl t).
Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof (@eq_sym t).
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof (@eq_trans t).

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof. unfold lt; lia. Qed.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof.
  unfold lt, eq; lia.
Qed.

Definition compare (x y : t) : Compare lt eq x y.
Proof.
  destruct (Pos.compare x y) eqn:C.
- apply EQ. apply Pos.compare_eq; auto.
- apply LT. apply Pos.compare_lt_iff; auto.
- apply GT. apply Pos.compare_nle_iff in C. red; lia.
Defined.

Definition eq_dec (x y : t) : {x = y} + {x <> y} := Pos.eq_dec x y.

End OrderedPositive.

