
(** MMaps Library : the demo *)

(** Author : Pierre Letouzey (Université de Paris - INRIA),
    adapted from earlier works in Coq Standard Library, see README.md.
    Licence : LGPL 2.1, see file LICENSE. *)

From Coq Require Import ZArith String Orders List.
From Tries.MMaps Require Import Tries.MMaps.

Set Implicit Arguments.
Open Scope string.
Open Scope Z.
Import ListNotations.

(** This MMaps library provides finite maps (e.g. key/value structure).
    It is an improved version of the former FMaps library, which is
    itself derived from the OCaml Map library.
    The "M" in the current name is for Module (and to be different
    from FMaps), nothing to see with the unix system call "mmap". *)

(** In these maps, we associate keys to values.
    The key type is rigidly fixed at the creation of the module
    (usually by giving an OrderedType module to the creating functor).
    while the value type is polymorphic and may vary from map to map,
    even in the same MMaps instance. *)

(** The OrderedType notion is the one of Coq Stdlib,
    already used in [MSets]. The main function is [compare],
    which has a ternary [comparison] output, and is specified
    w.r.t. an equivalence [eq] and a strict order [lt]. *)

Print Orders.OrderedType.
Print comparison.
Print CompareSpec.

(** Many datatype modules of Coq are already implementing OrderedType.
    For instance, let's build some maps with [nat] numbers as keys,
    and then maps with [Z] numbers as keys. *)

Module NatMaps := Tries.MMaps.RBT.Make(Nat).
Module ZM := Tries.MMaps.RBT.Make(Z).

(* Let's play with them : *)

Definition map1 :=
  ZM.add 3 "yes" (ZM.add 0 "no" (ZM.add 2 "foo" ZM.empty)).
Definition map2 :=
  ZM.add 3 [1;2] (ZM.add 0 [3;4;5] (ZM.add 7 [] ZM.empty)).

Compute ZM.find 3 map1.
Compute ZM.find 3 map2.
Compute ZM.bindings map1.
Compute ZM.bindings (ZM.remove 0 map1).

(* Some examples of more advanced operations : *)

Compute ZM.fold (fun _ => String.append) map1 "".

Compute ZM.bindings (ZM.map (@List.length Z) map2).

Definition reconciliate(z:Z)(o:option string)(o':option (list Z)) :=
 match o,o' with None, Some _ => Some "new" | _,_ => o end.

Definition map3 := ZM.merge reconciliate map1 map2.
Compute ZM.bindings map3.

(* ZM also provides some basic properties, for instance: *)

Check (ZM.cardinal_spec map1).
(* The number of bindings in [map1] is the length of [bindings map1]. *)

Check (ZM.bindings_spec2 map1).
(* bindings always returns a sorted list
   with respect to the underlying order on keys. *)

(* The ZM.t type for maps is meant to be used as an abstract type
   since it will vary among the different implementations of Tries.MMaps.
   An ZM.t can and should always be inspected by using [find],
   [bindings], etc.
   But for once, let's have a look at the raw aspect of a map: *)
Compute map1.
(* Here for RBT (Red-Black-Tree), a map is a record combining
   a tree (field ZM.this) and a proof (field ZM.ok). *)

(* Note that the proof part will grow at each operation of the map.
   In order to avoid that, we can work on the underlying "raw"
   datatype (i.e. without built-in invariants). *)

Module R:=ZM.Raw.

Definition raw1 := R.add 3 "yes" (R.add 0 "no" (R.add 2 "foo" (R.empty _))).

Compute raw1.
Compute (R.bindings raw1).

(* But then proving properties is a bit more complex. *)

Check (@R.bindings_spec2 _ raw1 _).

(* The second "_" is a proof that raw1 is "Ok". Fortunately, the system
   has infered it here via some class resolution, and it should be
   the case when using the provided operations. If you have built
   your own map without using the provided operations, you could
   consider the "isok" boolean function to check it, and [Mkt_bool]
   to "repack" it into a map with correctness proof. *)

Compute R.isok raw1.
Check (eq_refl : R.isok raw1 = true).
Check (@ZM.Mkt_bool _ raw1 eq_refl).

(** * Some more intense tests. *)

Fixpoint multiples (m:Z)(start:Z)(n:nat) {struct n} : list Z :=
  match n with
   | O => nil
   | S n => start::(multiples m (m+start) n)
  end.

Eval compute in (multiples 2 0 200%nat).

Definition bigmap1 :=
  fold_right (fun z => ZM.add z z) ZM.empty (multiples 2 0 400%nat).
Definition bigmap2 :=
  fold_right (fun z => ZM.add z z) ZM.empty (multiples 3 0 400%nat).

Definition both (z:Z)(o:option Z)(o':option Z) :=
 match o,o' with Some _, Some _ => o | _,_=>None end.
Time Compute ZM.bindings (ZM.merge both bigmap1 bigmap2).

Definition bigmap3 :=
  fold_right (fun z => ZM.add z z) ZM.empty (multiples 2 0 (100*100)%nat).
Definition bigmap4 :=
  fold_right (fun z => ZM.add z z) ZM.empty (multiples 3 0 (100*100)%nat).
Time Compute ZM.bindings (ZM.merge both bigmap3 bigmap4).


(** * the Facts *)

(* The properties provided by ZM are deliberately minimalistic.
   They correspond to the minimal specifications present in Interface.S.
   This way, building new implementations is relatively simple.
   Now, lots of additional facts can be derived from this common interface. *)

Module ZMF := Tries.MMaps.Facts.Properties Z ZM.

(* It contains mainly rephrasing of the specifications. *)
Check ZMF.add_1.
Check ZMF.add_b.

(* And some basic things about the operations. *)
Check ZMF.cardinal_notin_add.

(* Also useful: induction principles *)
Check ZMF.map_induction.

(* And lot of stuff concerning the hard-to-handle [fold] function *)
Check ZMF.fold_add.

(* Concerning [compare], we need a ternary decidable comparison
 over datas. We hence diverge slightly apart from Ocaml, by placing
 this [compare] in a separate functor requiring 2 [OrderedType],
 one for the keys and one for the datas, see Interface.Sord
 and for instance RBT.Make_ord *)


(** * The Weak Maps *)

(* Sometimes, one may need finite sets and maps over a base type
   that does not come with a decidable order. As long as this type
   can still be equipped with a decidable equality, the weak
   interface [Interface.WS] and its implementation [Tries.MMaps.WeakList]
   provide such structures.
*)

Module W := Tries.MMaps.WeakList.Make(Z).

(* Of course, we cannot provide efficient functions anymore : the
   underlying structure is unsorted lists (but without redundancies). *)

Compute W.bindings (W.add 1 "yes" (W.add 3 "no" (W.add 2 "foo" W.empty))).

(* For now, [Interface.WS] provides the same operations as [Interface.S]
   (minus [compare]), and the only different specification concerns [bindings],
   which isn't sorted, but only without redundancies. *)
