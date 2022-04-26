
(** * Finite Modular Maps : AVL Proofs *)

(** Author : Pierre Letouzey (Université de Paris - INRIA),
    adapted from earlier works in Coq Standard Library, see README.md.
    Licence : LGPL 2.1, see file LICENSE. *)

(** This is a complement to [Tries.MMaps.AVL], proving the AVL balancing
    invariants for the code in [Tries.MMaps.AVL], and hence the logarithmic
    depth bound. These extra proofs are not even loaded during a regular
    usage of [Tries.MMaps.AVL], which already provides proofs of observational
    correctness (the binary search tree invariants).

    This is an adapation of Coq [MSetFullAVL] to maps. *)

From Coq Require Import ZArith Int Lia PeanoNat FunInd Orders.
From Tries.MMaps Require Import GenTree AVL.

Set Implicit Arguments.

Module AvlProofs (Import I:Int)(X:OrderedType).
Include Tries.MMaps.AVL.MakeRaw I X.
Module Import II := MoreInt I.
Local Open Scope Int_scope.
Import GenTree.PairNotations. (* #1 and #2 for fst and snd *)

Ltac lia_max := i2z_refl; lia.
Ltac mysubst :=
 match goal with
   | E : _=_ |- _ => rewrite E in *; clear E; mysubst
   | _ => idtac
 end.

(** * AVL trees *)

(** [avl s] : [s] is a properly balanced AVL tree,
    i.e. for any node the heights of the two children
    differ by at most 2 *)

Inductive avl elt : tree elt -> Prop :=
  | RBLeaf : avl (Leaf _)
  | RBNode : forall x e l r h, avl l -> avl r ->
      -(2) <= height l - height r <= 2 ->
      h = max (height l) (height r) + 1 ->
      avl (Node h l x e r).

Class Avl elt (t:tree elt) : Prop := mkAvl : avl t.

Instance avl_Avl elt (s:tree elt) (Hs : avl s) : Avl s := Hs.

(** * Automation and dedicated tactics *)

Local Hint Constructors avl : map.

(** A tactic for cleaning hypothesis after use of functional induction. *)

Ltac clearf :=
 match goal with
  | H : (@Logic.eq (sumbool _ _) _ _) |- _ => clear H; clearf
  | H : (_ =? _) = true |- _ => rewrite II.eqb_eq in H; clearf
  | H : (_ <? _) = true |- _ => rewrite II.ltb_lt in H; clearf
  | H : (_ <=? _) = true |- _ => rewrite II.leb_le in H; clearf
  | H : (_ =? _) = false |- _ => rewrite II.eqb_neq in H; clearf
  | H : (_ <? _) = false |- _ => rewrite II.ltb_nlt in H; clearf
  | H : (_ <=? _) = false |- _ => rewrite II.leb_nle in H; clearf
  | _ => idtac
 end.

Ltac avl2Avl := change avl with Avl in *.
Ltac Avl2avl := change Avl with avl in *.
Ltac inv_avl := Avl2avl; inv avl; avl2Avl.
(* Similar, but non-recursive *)
Ltac inv_avl' :=
  match goal with H : Avl (Node _ _ _ _ _) |- _ =>
    inversion_clear H; avl2Avl
  end.

(** * AVL trees have indeed logarithmic depth *)

Module LogDepth.

Local Open Scope nat_scope.

(** The minimal cardinal of an AVL tree of a given height.
    NB: this minimal cardinal is optimal, i.e. for any height,
    we could build an AVL tree of this cardinal. *)

Fixpoint mincard n :=
 match n with
 | O => O
 | 1 => 1
 | 2 => 2
 | S (S (S n) as p) => S (mincard n + mincard p)
 end.

(** First, some basic properties of [mincard] *)

Lemma mincard_eqn n :
 mincard (S (S (S n))) = S (mincard n + mincard (2+n)).
Proof.
 reflexivity.
Qed.

Lemma mincard_incr n : mincard n < mincard (S n).
Proof.
 induction n using lt_wf_ind.
 do 3 (destruct n; auto).
 rewrite 2 mincard_eqn.
 apply -> Nat.succ_lt_mono.
 apply Nat.add_lt_mono; eauto.
Qed.

Lemma mincard_lt_mono n m : n < m -> mincard n < mincard m.
Proof.
 induction m; inversion_clear 1.
 - apply mincard_incr.
 - transitivity (mincard m); auto using mincard_incr.
Qed.

Lemma mincard_le_mono n m : n <= m -> mincard n <= mincard m.
Proof.
 induction 1; auto.
 transitivity (mincard m); auto using mincard_incr with arith.
Qed.

Lemma mincard_bound n m : m <= 2+n ->
 mincard (S m) <= S (mincard n + mincard m).
Proof.
 intros H.
 destruct m as [|[|m]].
 - simpl. auto with arith.
 - simpl. auto with arith.
 - rewrite mincard_eqn.
   apply -> Nat.succ_le_mono.
   apply Nat.add_le_mono; eauto.
   apply mincard_le_mono; lia.
Qed.

(** [mincard] has an exponential behavior *)

Lemma mincard_twice n : 2 * mincard n < mincard (2+n).
Proof.
 induction n as [n IH] using lt_wf_ind.
 do 3 (destruct n; [simpl; auto with arith|]).
 change (2 + S (S (S n))) with (S (S (S (2+n)))).
 rewrite 2 mincard_eqn.
 generalize (IH n) (IH (2+n)). lia.
Qed.

Lemma mincard_even n : n<>0 -> 2^n <= mincard (2*n).
Proof.
 induction n.
 - now destruct 1.
 - intros _.
   destruct (Nat.eq_dec n 0).
   * subst; simpl; auto.
   * rewrite Nat.pow_succ_r', Nat.mul_succ_r, Nat.add_comm.
     transitivity (2 * mincard (2*n)).
     + apply Nat.mul_le_mono_l; auto.
     + apply Nat.lt_le_incl. apply mincard_twice.
Qed.

Lemma mincard_odd n : 2^n <= mincard (2*n+1).
Proof.
 destruct (Nat.eq_dec n 0).
 - subst; auto.
 - transitivity (mincard (2*n)).
   * now apply mincard_even.
   * apply mincard_le_mono. lia.
Qed.

Lemma mincard_log n : n <= 2 * Nat.log2 (mincard n) + 1.
Proof.
 rewrite (Nat.div2_odd n).
 set (m := Nat.div2 n); clearbody m.
 destruct (Nat.odd n); simpl Nat.b2n; rewrite ?Nat.add_0_r; clear n.
 + apply Nat.add_le_mono_r, Nat.mul_le_mono_l.
   apply Nat.log2_le_pow2.
   apply (@mincard_lt_mono 0); auto with arith.
   apply mincard_odd.
 + destruct (Nat.eq_dec m 0); [subst; simpl; auto|].
   transitivity (2*Nat.log2 (mincard (2*m))); [|lia].
   apply Nat.mul_le_mono_l.
   apply Nat.log2_le_pow2.
   apply (@mincard_lt_mono 0); lia.
   now apply mincard_even.
Qed.

(** We now prove that [mincard] gives indeed a lower bound
    of the cardinal of AVL trees. *)

Lemma maxdepth_heigth elt (s:t elt) : Avl s ->
 Z.of_nat (maxdepth s) = i2z (height s).
Proof.
 induction 1.
 simpl. lia_max.
 simpl maxdepth. simpl height. subst h.
 rewrite Nat2Z.inj_succ, Nat2Z.inj_max. lia_max.
Qed.

Lemma mincard_maxdepth elt (s:t elt) :
 Avl s -> mincard (maxdepth s) <= cardinal s.
Proof.
 induction 1.
 - simpl; auto.
 - simpl maxdepth. simpl cardinal. subst h.
   destruct (Nat.max_spec (maxdepth l) (maxdepth r)) as [(U,->)|(U,->)].
   * rewrite mincard_bound.
     apply -> Nat.succ_le_mono.
     apply Nat.add_le_mono; eauto.
     apply Nat2Z.inj_le. rewrite Nat2Z.inj_add.
     rewrite 2 maxdepth_heigth by auto. simpl Z.of_nat.
     i2z. lia.
   * rewrite Nat.add_comm, mincard_bound.
     apply -> Nat.succ_le_mono.
     apply Nat.add_le_mono; eauto.
     apply Nat2Z.inj_le. rewrite Nat2Z.inj_add.
     rewrite 2 maxdepth_heigth by auto. simpl Z.of_nat.
     i2z. lia.
Qed.

(** We can now prove that the depth of an AVL tree is
    logarithmic in its size. *)

Lemma maxdepth_upperbound elt (s:t elt) : Avl s ->
 maxdepth s <= 2 * Nat.log2 (cardinal s) + 1.
Proof.
 intros.
 transitivity (2 * Nat.log2 (mincard (maxdepth s)) + 1).
 apply mincard_log.
 apply Nat.add_le_mono_r, Nat.mul_le_mono_l, Nat.log2_le_mono.
 now apply mincard_maxdepth.
Qed.

Lemma maxdepth_lowerbound elt (s:t elt) : s<>Leaf _ ->
 Nat.log2 (cardinal s) < maxdepth s.
Proof.
 apply maxdepth_log_cardinal.
Qed.

End LogDepth.

Section Elt.
Variable elt : Type.
Implicit Type t s l r : tree elt.
Implicit Type e v : elt.

(** Tactics about [avl] *)

Lemma height_non_negative : forall s `{!Avl s}, height s >= 0.
Proof.
 induction s; simpl; intros; auto with zarith.
 inv_avl; intuition; lia_max.
Qed.

(** When [H:Avl r], typing [avl_nn H] adds [height r >= 0] *)

Ltac avl_nn H :=
  let nz := fresh "nz" in assert (nz := @height_non_negative _ H).

(* Repeat the previous tactic, clearing the [Avl _] hyps *)

Ltac avl_nns :=
  match goal with
     | H:Avl _ |- _ => avl_nn H; clear H; avl_nns
     | _ => idtac
  end.

(** Results about [height] *)

Lemma height_0 : forall s `{!Avl s}, height s = 0 -> s = Leaf _.
Proof.
 destruct 1; avl2Avl; intuition; simpl in *.
 avl_nns. simpl in *; exfalso; lia_max.
Qed.

(** Results about [avl] *)

Lemma avl_node :
 forall x e l r `{!Avl l, !Avl r},
 -(2) <= height l - height r <= 2 ->
 Avl (Node (max (height l) (height r) + 1) l x e r).
Proof.
  autok.
Qed.
Local Hint Resolve avl_node : map.

(** * The AVL invariant is preserved by set operations *)

(** empty *)

Instance empty_avl : Avl (empty elt).
Proof.
 autok.
Qed.

(** singleton *)

Instance singleton_avl x e : Avl (singleton x e).
Proof.
 unfold singleton. constructor; autom; simpl; lia_max.
Qed.

(** create *)

Lemma create_avl :
 forall l x e r `{!Avl l, !Avl r},
   -(2) <= height l - height r <= 2 ->
   Avl (create l x e r).
Proof.
 unfold create; autom.
Qed.

Lemma create_height :
 forall l x e r `{!Avl l, !Avl r},
   -(2) <= height l - height r <= 2 ->
   height (create l x e r) = max (height l) (height r) + 1.
Proof.
 unfold create; autom.
Qed.

(** bal *)

Ltac when f :=
 match goal with |- context [f] => idtac | _ => fail end.

Lemma bal_avl :
  forall l x e r `{!Avl l, !Avl r},
    -(3) <= height l - height r <= 3 ->
    Avl (bal l x e r).
Proof.
 intros l x e r; functional induction (bal l x e r); intros; clearf;
 inv_avl; simpl in *; try (when assert_false; avl_nns);
 repeat apply create_avl; simpl in *; auto; lia_max.
Qed.

Lemma bal_height_1 :
  forall l x e r `{!Avl l, !Avl r},
    -(3) <= height l - height r <= 3 ->
    0 <= height (bal l x e r) - max (height l) (height r) <= 1.
Proof.
 intros l x e r; functional induction (bal l x e r); intros; clearf;
 inv_avl; avl_nns; simpl in *; lia_max.
Qed.

Lemma bal_height_2 :
 forall l x e r `{!Avl l, !Avl r},
   -(2) <= height l - height r <= 2 ->
   height (bal l x e r) == max (height l) (height r) +1.
Proof.
 intros l x e r; functional induction (bal l x e r); intros; clearf;
 inv_avl; simpl in *; lia_max.
Qed.

Ltac lia_bal := match goal with
  | Hl:Avl ?l, Hr:Avl ?r |- context [ bal ?l ?x ?e ?r ] =>
     generalize (@bal_height_1 l x e r Hl Hr) (@bal_height_2 l x e r Hl Hr);
     lia_max
  end.

(** add *)

Ltac induct m :=
 induction m as [|i l IHl x' e' r IHr]; simpl; intros;
 [|case X.compare_spec; intros].

Lemma add_avl_1 : forall s x e `{!Avl s},
 Avl (add x e s) /\ 0 <= height (add x e s) - height s <= 1.
Proof.
 induct s; inv_avl.
 - intuition; try constructor; simpl; autom; lia_max.
 - (* Eq *)
   simpl. intuition; lia_max.
 - (* Lt *)
   destruct (IHl x e); trivial.
   split.
   * apply bal_avl; trivial; lia_max.
   * lia_bal.
 - (* Gt *)
   destruct (IHr x e); trivial.
   split.
   * apply bal_avl; trivial; lia_max.
   * lia_bal.
Qed.

Instance add_avl s x e `{!Avl s} : Avl (add x e s).
Proof.
 now destruct (@add_avl_1 s x e).
Qed.

(** join *)

Ltac remtree t s :=
 match t with Node ?h _ _ _ _ =>
  assert (height t = h) by trivial;
  set (s := t) in *; clearbody s
 end.

Lemma join_avl_1 l x e r : forall `{!Avl l, !Avl r},
 Avl (join l x e r) /\
 0<= height (join l x e r) - max (height l) (height r) <= 1.
Proof.
 join_tac l x e r; clearf.

 - simpl. destruct (@add_avl_1 r x e); auto. split; trivial.
   avl_nns; lia_max.

 - remtree (Node lh ll lx ld lr) l.
   split; autok.
   destruct (@add_avl_1 l x e); auto.
   simpl. avl_nns; lia_max.

 - remtree (Node rh rl rx rd rr) r.
   inv_avl.
   destruct (Hlr x e r); trivial; clear Hrl Hlr.
   set (j := join lr x e r) in *; clearbody j.
   simpl.
   assert (-(3) <= height ll - height j <= 3) by lia_max.
   split.
   * apply bal_avl; trivial.
   * lia_bal.

 - remtree (Node lh ll lx ld lr) l.
   inv_avl.
   destruct Hrl; trivial; clear Hlr.
   set (j := join l x e rl) in *; clearbody j.
   simpl.
   assert (-(3) <= height j - height rr <= 3) by lia_max.
   split.
   * apply bal_avl; trivial.
   * lia_bal.

 - clear Hrl Hlr.
   remtree (Node lh ll lx ld lr) l.
   remtree (Node rh rl rx rd rr) r.
   assert (-(2) <= height l - height r <= 2) by lia_max.
   split.
   * apply create_avl; trivial.
   * rewrite create_height; trivial; lia_max.
Qed.

Instance join_avl l x e r `{!Avl l, !Avl r} : Avl (join l x e r).
Proof.
 now destruct (@join_avl_1 l x e r).
Qed.

(** remove_min *)

Lemma remove_min_avl_1 : forall l x e r h `{!Avl (Node h l x e r)},
 Avl (remove_min l x e r)#1 /\
 0 <= height (Node h l x e r) - height (remove_min l x e r)#1 <= 1.
Proof.
 intros l x e r; functional induction (remove_min l x e r);
 subst; simpl in *; intros.
 - inv_avl; simpl in *; split; auto. avl_nns; lia_max.
 - mysubst. inv_avl'; simpl in *.
   edestruct IHp; clear IHp; [eauto|].
   split.
   * apply bal_avl; trivial; lia_max.
   * lia_bal.
Qed.

Instance remove_min_avl l x e r h `{!Avl (Node h l x e r)} :
  Avl (remove_min l x e r)#1.
Proof.
 now destruct (@remove_min_avl_1 l x e r h).
Qed.

(** append *)

Lemma append_avl_1 : forall s1 s2 `{!Avl s1, !Avl s2},
 -(2) <= height s1 - height s2 <= 2 ->
 Avl (append s1 s2) /\
 0<= height (append s1 s2) - max (height s1) (height s2) <=1.
Proof.
 intros s1 s2; functional induction (append s1 s2); intros;
 try (factornode s1).
 - simpl; split; auto; avl_nns; lia_max.
 - simpl; split; auto; avl_nns; simpl in *; lia_max.
 - generalize (@remove_min_avl_1 l2 x2 d2 r2 _ _).
   mysubst. destruct 1; simpl in *.
   split.
   * apply bal_avl; trivial. simpl; lia_max.
   * lia_bal.
Qed.

Lemma append_avl s1 s2 `{!Avl s1, !Avl s2} :
  -(2) <= height s1 - height s2 <= 2 -> Avl (append s1 s2).
Proof.
 intros; now destruct (@append_avl_1 s1 s2).
Qed.


(** remove *)

Lemma remove_avl_1 : forall s x `{!Avl s},
 Avl (remove x s) /\ 0 <= height s - height (remove x s) <= 1.
Proof.
 induct s; inv_avl.
 - intuition; lia_max.
 - (* Eq *)
   generalize (@append_avl_1 l r).
   intuition lia_max.
 - (* Lt *)
   destruct (IHl x); trivial.
   split.
   * apply bal_avl; trivial; lia_max.
   * lia_bal.
 - (* Gt *)
   destruct (IHr x); trivial.
   split.
   * apply bal_avl; trivial; lia_max.
   * lia_bal.
Qed.

Instance remove_avl s x `{!Avl s} : Avl (remove x s).
Proof.
 now destruct (@remove_avl_1 s x).
Qed.

(** concat *)

Instance concat_avl s1 s2 `{!Avl s1, !Avl s2} : Avl (concat s1 s2).
Proof.
 functional induction (concat s1 s2); auto.
 apply join_avl; auto.
 generalize (@remove_min_avl l2 x2 d2 r2 _ _). now mysubst.
Qed.

(** split *)

Lemma split_avl : forall s x `{!Avl s},
  Avl (t_left (split x s)) /\ Avl (t_right (split x s)).
Proof.
 intros s x. functional induction (split x s); simpl; auto.
 - intros. inv_avl; auto.
 - mysubst; simpl in *; inversion_clear 1; intuition.
 - mysubst; simpl in *; inversion_clear 1; intuition.
Qed.

(** filter *)

Instance filter_avl (f:key->elt->bool) m `{!Avl m} : Avl (filter f m).
Proof.
 induction m; simpl; auto. inv_avl.
 destruct f; [apply join_avl | apply concat_avl ]; auto.
Qed.

Instance partition_avl1 (f:key->elt->bool) m `{!Avl m} :
 Avl (fst (partition f m)).
Proof.
 induction m; simpl; auto. inv_avl.
 destruct partition, partition, f; simpl in *;
 [apply join_avl | apply concat_avl]; auto.
Qed.

Instance partition_avl2 (f:key->elt->bool) m `{!Avl m} :
 Avl (snd (partition f m)).
Proof.
 induction m; simpl; auto. inv_avl.
 destruct partition, partition, f; simpl in *;
 [apply concat_avl | apply join_avl]; auto.
Qed.

End Elt.

Lemma map_height {elt elt'}(f:elt->elt') m : height (map f m) = height m.
Proof.
 induction m; simpl; auto.
Qed.

Instance map_avl {elt elt'}(f:elt->elt') m `(!Avl m) : Avl (map f m).
Proof.
 induction m; simpl; inv_avl; intuition.
 constructor; intuition; rewrite ?map_height; auto.
Qed.

Lemma mapi_height {elt elt'}(f:key->elt->elt') m :
  height (mapi f m) = height m.
Proof.
 induction m; simpl; auto.
Qed.

Instance mapi_avl {elt elt'}(f:key->elt->elt') m `(!Avl m) : Avl (mapi f m).
Proof.
 induction m; simpl; inv_avl; intuition.
 constructor; intuition; rewrite ?mapi_height; auto.
Qed.

Instance mapo_avl {elt elt'}(f:key->elt->option elt') m `{!Avl m} :
  Avl (mapo f m).
Proof.
 induction m; simpl; inv_avl; intuition.
 destruct f.
 - apply join_avl; auto.
 - apply concat_avl; auto.
Qed.

Section Gmerge.
Variable elt elt' elt'' : Type.
Variable f : key -> elt -> option elt' -> option elt''.
Variable mapl : t elt -> t elt''.
Variable mapr : t elt' -> t elt''.
Hypothesis mapl_avl : forall m, Avl m -> Avl (mapl m).
Hypothesis mapr_avl : forall m', Avl m' -> Avl (mapr m').

Instance gmerge_avl m m' `{!Avl m, !Avl m'} :
  Avl (gmerge f mapl mapr m m').
Proof.
  functional induction (gmerge f mapl mapr m m');
    auto; factornode m2; inv_avl;
    apply join_avl || apply concat_avl; auto;
    apply IHt0 || apply IHt2; auto; cleansplit; apply split_avl; auto.
Qed.
End Gmerge.

Instance merge_avl {elt elt' elt''}
 (f:key -> option elt -> option elt' -> option elt'') m m'
 `(!Avl m, !Avl m') :
   Avl (merge f m m').
Proof.
 apply gmerge_avl; auto using mapo_avl.
Qed.

End AvlProofs.

(** We could hence define [Ok m] as [Bst m /\ Avl m] and re-validate
    the [Raw.S] signature. This would be more robust in case new ops
    are added in the signature. But that would be yet another wrapper,
    so we don't do it for the moment. *)
