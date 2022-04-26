
(** * Finite Modular Maps : RBT Proofs *)

(** This is a complement to [Tries.MMaps.RBT], proving the Red/Black balancing
    invariants for the code in [Tries.MMaps.RBT], and hence the logarithmic
    depth bound. These extra proofs are not even loaded during a regular
    usage of [Tries.MMaps.RBT], which already provides proofs of observational
    correctness (the binary search tree invariants).

    This is an adapation of Coq [MSetRBT.BalanceProps] to maps. *)

From Coq Require Import Bool BinPos Pnat Setoid SetoidList Arith.
From Coq Require Import Orders OrdersFacts OrdersLists.
From Tries.MMaps Require Import Interface GenTree RBT.

Local Set Implicit Arguments.
Local Unset Strict Implicit.
Import ListNotations.

(* For nicer extraction, we create inductive principles
   only when needed *)
Local Unset Elimination Schemes.

Module BalanceProps(K:OrderedType).
Include Tries.MMaps.RBT.MakeRaw K.
Import GenTree.PairNotations. (* #1 and #2 for fst and snd *)
Local Open Scope lazy_bool_scope.
Local Notation color := Color.t.
Local Arguments Leaf {elt}.
Local Notation Rd := (@Node _ Red).
Local Notation Bk := (@Node _ Black).

(** ** Red-Black invariants *)

(** In a red-black tree :
    - a red node has no red children
    - the black depth at each node is the same along all paths.
    The black depth is here an argument of the predicate. *)

Inductive rbt elt : nat -> tree elt -> Prop :=
 | RB_Leaf : rbt 0 Leaf
 | RB_Rd n l k e r :
   notred l -> notred r -> rbt n l -> rbt n r -> rbt n (Rd l k e r)
 | RB_Bk n l k e r : rbt n l -> rbt n r -> rbt (S n) (Bk l k e r).

(** A red-red tree is almost a red-black tree, except that it has
    a _red_ root node which _may_ have red children. Note that a
    red-red tree is hence non-empty, and all its strict subtrees
    are red-black. *)

Inductive rrt elt (n:nat) : tree elt -> Prop :=
 | RR_Rd l k e r : rbt n l -> rbt n r -> rrt n (Rd l k e r).

(** An almost-red-black tree is almost a red-black tree, except that
    it's permitted to have two red nodes in a row at the very root (only).
    We implement this notion by saying that a quasi-red-black tree
    is either a red-black tree or a red-red tree. *)

Inductive arbt elt (n:nat)(t:tree elt) : Prop :=
 | ARB_RB : rbt n t -> arbt n t
 | ARB_RR : rrt n t -> arbt n t.

(** The main exported invariant : being a red-black tree for some
    black depth. *)

Class Rbt elt (t:tree elt) :=  RBT : exists d, rbt d t.

(** ** Basic tactics and results about red-black *)

Scheme rbt_ind := Induction for rbt Sort Prop.
Local Hint Constructors rbt rrt arbt : map.
Local Hint Extern 0 (notred _) => (exact I) : map.
Ltac invrb := intros; inv rrt; inv rbt; try contradiction.
Ltac descolor := destruct_all Color.t.
Ltac destree t := destruct t as [|[|] ? ? ? ?].
Ltac desarb := match goal with H:arbt _ _ |- _ => destruct H end.
Ltac nonzero n := destruct n as [|n]; [try split; invrb|].

Notation notredred := (rrcase (fun _ _ _ _ _ _ _ => False) (fun _ => True)).

Section Elt.
Variable elt : Type.
Implicit Type t s l r : tree elt.
Implicit Type e v : elt.

Lemma rr_nrr_rb n t :
 rrt n t -> notredred t -> rbt n t.
Proof.
 destruct 1 as [l x e r Hl Hr].
 unfold rrcase; destmatch; now autom.
Qed.

Local Hint Resolve rr_nrr_rb : map.

Lemma arb_nrr_rb n t :
 arbt n t -> notredred t -> rbt n t.
Proof.
 destruct 1; autom.
Qed.

Lemma arb_nr_rb n t :
 arbt n t -> notred t -> rbt n t.
Proof.
 destruct 1; destruct t; descolor; invrb; autom.
Qed.

Local Hint Resolve arb_nrr_rb arb_nr_rb : map.

(** ** A Red-Black tree has indeed a logarithmic depth *)

Definition redcarac s :=
 rcase (elt:=elt) (fun _ _ _ _ => 1) (fun _ => 0) s.

Lemma rb_maxdepth s n : rbt n s -> maxdepth s <= 2*n + redcarac s.
Proof.
 induction 1.
 - simpl; auto.
 - replace (redcarac l) with 0 in * by now destree l.
   replace (redcarac r) with 0 in * by now destree r.
   simpl maxdepth. simpl redcarac.
   rewrite Nat.add_succ_r, <- Nat.succ_le_mono.
   now apply Nat.max_lub.
 - simpl. rewrite <- Nat.succ_le_mono.
   apply Nat.max_lub; eapply Nat.le_trans; eauto;
   [destree l | destree r]; simpl;
   rewrite !Nat.add_0_r, ?Nat.add_1_r; auto with arith.
Qed.

Lemma rb_mindepth s n : rbt n s -> n + redcarac s <= mindepth s.
Proof.
 induction 1; simpl.
 - trivial.
 - rewrite Nat.add_succ_r.
   apply -> Nat.succ_le_mono.
   replace (redcarac l) with 0 in * by now destree l.
   replace (redcarac r) with 0 in * by now destree r.
   now apply Nat.min_glb.
 - apply -> Nat.succ_le_mono. rewrite Nat.add_0_r.
   apply Nat.min_glb; eauto with arith.
Qed.

Lemma maxdepth_upperbound s : Rbt s ->
 maxdepth s <= 2 * Nat.log2 (S (cardinal s)).
Proof.
 intros (n,H).
 eapply Nat.le_trans; [eapply rb_maxdepth; eauto|].
 transitivity (2*(n+redcarac s)).
 - rewrite Nat.mul_add_distr_l. apply Nat.add_le_mono_l.
   rewrite <- Nat.mul_1_l at 1. apply Nat.mul_le_mono_r.
   auto with arith.
 - apply Nat.mul_le_mono_l.
   transitivity (mindepth s).
   + now apply rb_mindepth.
   + apply mindepth_log_cardinal.
Qed.

Lemma maxdepth_lowerbound s : s<>Leaf ->
 Nat.log2 (cardinal s) < maxdepth s.
Proof.
 apply maxdepth_log_cardinal.
Qed.


(** ** Singleton *)

Lemma singleton_rb x e : Rbt (singleton x e).
Proof.
 unfold singleton. exists 1; autom.
Qed.

(** ** [makeBlack] and [makeRed] *)

Lemma makeBlack_rb n t : arbt n t -> Rbt (makeBlack t).
Proof.
 destruct t as [|[|] l x e r].
 - exists 0; simpl; autom.
 - destruct 1; invrb; exists (S n); simpl; autom.
 - exists n; autom.
Qed.

Lemma makeRed_rr t n :
 rbt (S n) t -> notred t -> rrt n (makeRed t).
Proof.
 destruct t as [|[|] l x e r]; invrb; simpl; autom.
Qed.

(** ** Balancing *)

Lemma lbal_rb n l k e r :
 arbt n l -> rbt n r -> rbt (S n) (lbal l k e r).
Proof.
case lbal_match; intros; desarb; invrb; autom.
Qed.

Lemma rbal_rb n l k e r :
 rbt n l -> arbt n r -> rbt (S n) (rbal l k e r).
Proof.
case rbal_match; intros; desarb; invrb; autom.
Qed.

Lemma rbal'_rb n l k e r :
 rbt n l -> arbt n r -> rbt (S n) (rbal' l k e r).
Proof.
case rbal'_match; intros; desarb; invrb; autom.
Qed.

Lemma lbalS_rb n l x e r :
 arbt n l -> rbt (S n) r -> notred r -> rbt (S n) (lbalS l x e r).
Proof.
 intros Hl Hr Hr'.
 destruct r as [|[|] rl rx rv rr]; invrb. clear Hr'.
 revert Hl.
 case lbalS_match.
 - destruct 1; invrb; autom.
 - intros. apply rbal'_rb; autom.
Qed.

Lemma lbalS_arb n l x e r :
 arbt n l -> rbt (S n) r -> arbt (S n) (lbalS l x e r).
Proof.
 case lbalS_match.
 - destruct 1; invrb; autom.
 - clear l. intros l Hl Hl' Hr.
   destruct r as [|[|] rl rx rv rr]; invrb.
   * destruct rl as [|[|] rll rlx rlv rlr]; invrb.
     right; auto using rbal'_rb, makeRed_rr with map.
   * left; apply rbal'_rb; autom.
Qed.

Lemma rbalS_rb n l x e r :
 rbt (S n) l -> notred l -> arbt n r -> rbt (S n) (rbalS l x e r).
Proof.
 intros Hl Hl' Hr.
 destruct l as [|[|] ll lx lv lr]; invrb. clear Hl'.
 revert Hr.
 case rbalS_match.
 - destruct 1; invrb; autom.
 - intros. apply lbal_rb; autom.
Qed.

Lemma rbalS_arb n l x e r :
 rbt (S n) l -> arbt n r -> arbt (S n) (rbalS l x e r).
Proof.
 case rbalS_match.
 - destruct 2; invrb; autom.
 - clear r. intros r Hr Hr' Hl.
   destruct l as [|[|] ll lx lv lr]; invrb.
   * destruct lr as [|[|] lrl lrx lrv lrr]; invrb.
     right; auto using lbal_rb, makeRed_rr with map.
   * left; apply lbal_rb; autom.
Qed.


(** ** Insertion *)

(** The next lemmas combine simultaneous results about rbt and arbt.
    A first solution here: statement with [if ... then ... else] *)

Definition ifred s (A B:Prop) := rcase (fun _ _ _ _ => A) (fun _ => B) s.

Lemma ifred_notred s A B : notred s -> (ifred s A B <-> B).
Proof.
 destruct s; descolor; simpl; intuition.
Qed.

Lemma ifred_or s A B : ifred s A B -> A\/B.
Proof.
 destruct s; descolor; simpl; intuition.
Qed.

Lemma ins_rr_rb x e s n : rbt n s ->
 ifred s (rrt n (ins x e s)) (rbt n (ins x e s)).
Proof.
induction 1 as [ | n l k v r | n l k v r Hl IHl Hr IHr ].
- simpl; autom.
- simpl. rewrite ifred_notred in * by trivial.
  destmatch; autom.
- rewrite ifred_notred by autom.
  cbn. destmatch; intro.
  * autom.
  * apply lbal_rb; trivial. apply ifred_or in IHl; intuition.
  * apply rbal_rb; trivial. apply ifred_or in IHr; intuition.
Qed.

Lemma ins_arb x e s n : rbt n s -> arbt n (ins x e s).
Proof.
 intros H. apply (ins_rr_rb x e), ifred_or in H. intuition.
Qed.

Instance add_rb x e s : Rbt s -> Rbt (add x e s).
Proof.
 intros (n,H). unfold add. now apply (@makeBlack_rb n), ins_arb.
Qed.

(** ** Deletion *)

(*TODO: share with RBT *)

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

Fact append_rr_match ll lx lv lr rl rx rv rr :
 rspec
  (fun a x e b => Rd (Rd ll lx lv a) x e (Rd b rx rv rr))
  (fun t => Rd ll lx lv (Rd t rx rv rr))
  (append lr rl)
  (append (Rd ll lx lv lr) (Rd rl rx rv rr)).
Proof.
 exact (rmatch _ _ _).
Qed.

Fact append_bb_match ll lx lv lr rl rx rv rr :
 rspec
  (fun a x e b => Rd (Bk ll lx lv a) x e (Bk b rx rv rr))
  (fun t => lbalS ll lx lv  (Bk t rx rv rr))
  (append lr rl)
  (append (Bk ll lx lv lr) (Bk rl rx rv rr)).
Proof.
 exact (rmatch _ _ _).
Qed.

(** A second approach here: statement with ... /\ ... *)

Lemma append_arb_rb n l r : rbt n l -> rbt n r ->
 (arbt n (append l r)) /\
 (notred l -> notred r -> rbt n (append l r)).
Proof.
revert r n.
append_tac l r.
- split; autom.
- split; autom.
- (* Red / Red *)
  intros n. invrb.
  case (IHlr n); auto; clear IHlr.
  case append_rr_match.
  + intros a x v b _ H; split; invrb.
    assert (rbt n (Rd a x v b)) by autom. invrb. autom.
  + split; invrb; autom.
- (* Red / Black *)
  split; invrb. destruct (IHlr n) as (_,IH); autom.
- (* Black / Red *)
  split; invrb. destruct (IHrl n) as (_,IH); autom.
- (* Black / Black *)
  nonzero n.
  invrb.
  destruct (IHlr n) as (IH,_); auto; clear IHlr.
  revert IH.
  case append_bb_match.
  + intros a x v b IH; split; destruct IH; invrb; autom.
  + split; [left | invrb]; auto using lbalS_rb with map.
Qed.

Ltac induct' m :=
 induction m as [|c l IHl x' vx' r IHr]; simpl; intros;
 [|case K.compare_spec; intros].

(** A third approach : Lemma ... with ... *)

Lemma del_arb s x n : rbt (S n) s -> isblack s -> arbt n (del x s)
with del_rb s x n : rbt n s -> notblack s -> rbt n (del x s).
Proof.
{ revert n.
  induct' s; descolor; try easy; invrb.
  - apply append_arb_rb; assumption.
  - assert (IHl' := del_rb l x). clear IHr del_arb del_rb.
    destruct l as [|[|] ll lx lv lr]; autom.
    nonzero n. apply lbalS_arb; autom.
  - assert (IHr' := del_rb r x). clear IHl del_arb del_rb.
    destruct r as [|[|] rl rx rv rr]; autom.
    nonzero n. apply rbalS_arb; auto. }
{ revert n.
  induct' s; descolor; try easy; invrb.
  - apply append_arb_rb; assumption.
  - assert (IHl' := del_arb l x). clear IHr del_arb del_rb.
    destruct l as [|[|] ll lx lv lr]; autom.
    nonzero n. destruct n as [|n]; [invrb|]; apply lbalS_rb; autom.
  - assert (IHr' := del_arb r x). clear IHl del_arb del_rb.
    destruct r as [|[|] rl rx rv rr]; autom.
    nonzero n. apply rbalS_rb; auto. }
Qed.

Instance remove_rb s x : Rbt s -> Rbt (remove x s).
Proof.
 intros (n,H). unfold remove.
 destruct s as [|[|] l y v r].
 - apply (@makeBlack_rb n). autom.
 - apply (@makeBlack_rb n). left. apply del_rb; simpl; autom.
 - nonzero n. apply (@makeBlack_rb n). apply del_arb; simpl; autom.
Qed.

(** ** Treeify *)

Local Notation ifpred p n := (if p then pred n else n%nat).
Local Notation treeify_t := (klist elt -> tree elt * klist elt).

Definition treeify_rb_invariant size depth (f:treeify_t) :=
 forall acc,
 size <= length acc ->
  rbt depth (fst (f acc)) /\
  size + length (snd (f acc)) = length acc.

Lemma treeify_zero_rb : treeify_rb_invariant 0 0 (@treeify_zero elt).
Proof.
 intros acc _; simpl; autom.
Qed.

Lemma treeify_one_rb : treeify_rb_invariant 1 0 (@treeify_one elt).
Proof.
 intros [|(x,e) acc]; simpl; autom; inversion 1.
Qed.

Lemma treeify_cont_rb f g size1 size2 size d :
 treeify_rb_invariant size1 d f ->
 treeify_rb_invariant size2 d g ->
 size = S (size1 + size2) ->
 treeify_rb_invariant size (S d) (treeify_cont f g).
Proof.
 intros Hf Hg H acc Hacc.
 unfold treeify_cont.
 specialize (Hf acc).
 destruct (f acc) as (l, acc1). simpl in *.
 destruct Hf as (Hf1, Hf2). { subst. eauto with arith. }
 destruct acc1 as [|(x,e) acc2]; simpl in *.
 - exfalso. revert Hacc. apply Nat.lt_nge. rewrite H, <- Hf2.
   auto with arith.
 - specialize (Hg acc2).
   destruct (g acc2) as (r, acc3). simpl in *.
   destruct Hg as (Hg1, Hg2).
   { revert Hacc.
     rewrite H, <- Hf2, Nat.add_succ_r, <- Nat.succ_le_mono.
     apply Nat.add_le_mono_l. }
   split; autom.
   now rewrite H, <- Hf2, <- Hg2, Nat.add_succ_r, Nat.add_assoc.
Qed.

Lemma treeify_aux_rb n :
 exists d, forall (b:bool),
  treeify_rb_invariant (ifpred b (Pos.to_nat n)) d (treeify_aux b n).
Proof.
 induction n as [n (d,IHn)|n (d,IHn)| ].
 - exists (S d). intros b.
   eapply treeify_cont_rb; [ apply (IHn false) | apply (IHn b) | ].
   rewrite Pos2Nat.inj_xI.
   assert (H := Pos2Nat.is_pos n). apply Nat.neq_0_lt_0 in H.
   destruct b; simpl; intros; rewrite Nat.add_0_r; trivial.
   now rewrite <- Nat.add_succ_r, Nat.succ_pred; trivial.
 - exists (S d). intros b.
   eapply treeify_cont_rb; [ apply (IHn b) | apply (IHn true) | ].
   rewrite Pos2Nat.inj_xO.
   assert (H := Pos2Nat.is_pos n). apply Nat.neq_0_lt_0 in H.
   rewrite <- Nat.add_succ_r, Nat.succ_pred by trivial.
   destruct b; simpl; intros; rewrite Nat.add_0_r; trivial.
   symmetry. now apply Nat.add_pred_l.
 - exists 0; destruct b;
    [ apply treeify_zero_rb | apply treeify_one_rb ].
Qed.

(** The black depth of [treeify l] is actually a log2, but
    we don't need to mention that. *)

Instance treeify_rb (l:klist elt) : Rbt (treeify l).
Proof.
 unfold treeify.
 destruct (treeify_aux_rb (plength l)) as (d,H).
 exists d.
 apply H.
 now rewrite plength_spec.
Qed.

Instance filter_rb (f:key->elt->bool) m : Rbt m -> Rbt (filter f m).
Proof.
 unfold filter. intros. apply treeify_rb.
Qed.

Instance partition_rb1 (f:key->elt->bool) m :
 Rbt m -> Rbt (fst (partition f m)).
Proof.
 unfold partition. intros. destruct partition_aux. apply treeify_rb.
Qed.

Instance partition_rb2 (f:key->elt->bool) m :
 Rbt m -> Rbt (snd (partition f m)).
Proof.
 unfold partition. intros. destruct partition_aux. apply treeify_rb.
Qed.

End Elt.

Instance map_rb {elt elt'}(f:elt->elt') m : Rbt m -> Rbt (map f m).
Proof.
 intros (n,H). exists n. induction H; simpl; constructor; auto.
 destruct l; auto.
 destruct r; auto.
Qed.

Instance mapi_rb {elt elt'}(f:key->elt->elt') m : Rbt m -> Rbt (mapi f m).
Proof.
 intros (n,H). exists n. induction H; simpl; constructor; auto.
 destruct l; auto.
 destruct r; auto.
Qed.

Instance merge_rb {elt elt' elt''}
 (f:key -> option elt -> option elt' -> option elt'') m m' :
 Rbt m -> Rbt m' -> Rbt (merge f m m').
Proof.
 unfold merge. intros. apply treeify_rb.
Qed.

End BalanceProps.

(** We could hence define [Ok m] as [Bst m /\ Rbt m] and re-validate
    the [Raw.S] signature. This would be more robust in case new ops
    are added in the signature. But that would be yet another wrapper,
    so we don't do it for the moment. *)
