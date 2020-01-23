(**************************************************************************)
(**                                                                       *)
(**  This file is part of octant-proof.                                   *)
(**                                                                       *)
(**  Copyright (C) 2019-2020 Orange                                       *)
(**  License: LGPL-3.0-or-later                                           *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, either version 3 of the License, or (at your option)      *)
(*  any later version.                                                    *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  You should have received a copy of the GNU Lesser General Public      *)
(*  License along with the software. If not, see                          *)
(*  <https://www.gnu.org/licenses/>.                                      *)
(*                                                                        *)
(**************************************************************************)

Require Import utils.
Require Import finseqs.

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset.

From Equations Require Import Equations Signature.
Require Import Sumbool.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensive.

(** * HTrees: syntactically bounded trees *)
Section HTree.
(** The width of the tree (maximum degree) *)
Variable w: nat.

Section InducType.
(** The type of the nodes of the tree *)
Variable A: Type.
(** The type of the leaves *)
Variable B: Type.

(** The inductive type of bounded tree. n is a bound on the height.
  - a leaf specifies the element
  - a node specifies the node element and the bounded list of its children *)
Inductive Htree: nat -> Type :=
  BLeaf : forall n, B -> (Htree n)
| BNode : forall n, A -> (Wlist (Htree n) w) -> (Htree n.+1).

(** Defines a leaf from an element in B *)
Definition gl (x: B) := (BLeaf 0 x).

(** A tree of height 0 is a leaf. technical version for dependent typing *)
Lemma aux_leaf0 : forall n (x: Htree n), (n = 0) -> { y & x=(BLeaf n y)}.
intros n x; elim x; [
  intros n0 wit eq0; exists wit; trivial
| intros n0 x1 x2 H; contradict H; auto].
Defined.

(** A tree of height 0 is a leaf. *)
Lemma leaf0 : forall (x: Htree 0), { y & x=(BLeaf 0 y)}.

intros x; apply (@aux_leaf0 0); trivial.
Defined.

(** Extraction of the B element from the  tree of height 0. Technical version *)
Definition fl_aux n (x: (Htree n)): (n = 0) -> B.
case x; [
  intros n0 x0 H; exact x0
| intros; contradict H; auto ].
Defined.

(** Extraction of the B element from the
tree of height 0 *)
Definition fl x := (@fl_aux 0 x (@refl_equal nat 0)).

(** The pair [fl], [gl] makes a cancelable with B *)
Lemma cancelflgl : cancel fl gl.
intro x; elim (leaf0 x).
intros y R; rewrite R; trivial.
Defined.

(** Transforms an element that is either
of the type of the leaves or a pair of
the type of the inner node and a bounded list of Htree of height at most [n] in a
tree of height [n+1]*)
Definition ggl n (x: B + (A * (Wlist (Htree n) w))) : (Htree n.+1) :=
  match x with
  | inl y => (BLeaf n.+1 y)
  | inr p => (BNode (fst p) (snd p))
  end.

(** Reciprocal function - technical version with height as an equality *)
Definition ffl_aux n m (x: Htree m): (m = n.+1) -> B + (A * (Wlist (Htree n) w)).
case x; [
  intros n0 wit E; exact (inl wit)
| intros n0 hd tl E; rewrite <- (eq_add_S _ _ E); exact (inr (hd, tl))].
Defined.

(** From trees to representation. *)
Definition ffl n (x: Htree (n.+1)) : B + (A * (Wlist (Htree n) w)) := (@ffl_aux n (n.+1)) x (@refl_equal nat n.+1).

(** We have a cancelable pair *)
Lemma cancel_fflggl : forall n, (cancel (@ffl n) (@ggl n)).
intros n x; dependent elimination x; compute; auto.
Defined.
End InducType.

(** ** Trees are an equality type *)
Section HtreeEqType.
Variable A B: eqType.
(** Base case for trees of height 0 *)
Definition htree0_eqMixin := CanEqMixin (@cancelflgl A B).
Definition htree0_eqType := EqType (Htree A B 0) htree0_eqMixin.

(** We define the eqMixin by induction on n using the proof as code approach *)
Fixpoint htreen_eqMixin n : Equality.mixin_of (Htree A B n).
elim n.
  exact htree0_eqMixin.
  intros n0 EM; apply  (@CanEqMixin _ (sum_eqType B (prod_eqType A (wlistn_eqType (Equality.Pack EM) w))) (@ffl A B n0) (@ggl A B n0) (@cancel_fflggl A B n0)).
Defined.

Definition htreen_eqType n := Eval hnf in EqType (Htree A B n) (htreen_eqMixin n).
End HtreeEqType.

(** ** Htree is a choice type *)
Section HtreeChoiceType.
Variable A B: choiceType.

Definition htree0_choiceMixin := CanChoiceMixin (@cancelflgl A B).
Definition htree0_choiceType := ChoiceType (htree0_eqType A B) htree0_choiceMixin.

Fixpoint htreen_choiceMixin (n:nat) :  Choice.mixin_of (Htree A B n).
elim n.
exact htree0_choiceMixin.
intros n0 EC.

apply  (@CanChoiceMixin (sum_choiceType B (prod_choiceType A (wlistn_choiceType (ChoiceType (htreen_eqType A B n0) EC) w)  ))
                        (Htree A B n0.+1) (@ffl A B n0) (@ggl A B n0) (@cancel_fflggl A B n0)).
Defined.

Definition htreen_choiceType n := Eval hnf in (@ChoiceType (htreen_eqType A B n) (htreen_choiceMixin n)).
End HtreeChoiceType.

(** ** Htree is a countable type *)
Section HtreeCountType.
Variable A B: countType.

Definition htree0_countMixin := (@CanCountMixin B (Htree A B 0) (@fl A B) (@gl A B) (@cancelflgl A B)).
Definition htree0_countType := CountType (htree0_choiceType A B) htree0_countMixin.


Fixpoint htreen_countMixin (n:nat): Countable.mixin_of (Htree A B n).
elim n.
exact htree0_countMixin.
intros n0 EN.

apply (@CanCountMixin
           (sum_countType B (prod_countType A (wlistn_countType (CountType (htreen_choiceType A B n0) EN) w) ))
           _ (@ffl A B n0) (@ggl A B n0) (@cancel_fflggl A B n0)).
Defined.

Definition htreen_countType n := Eval hnf in (@CountType (htreen_choiceType A B n) (htreen_countMixin n)).

Lemma cteql: htreen_countType 0 = htree0_countType.
compute. trivial.
Defined.

End HtreeCountType.

(** ** Htree is a finite type *)
Section HtreeFinType.
Variable A B: finType.

Definition htree0_finMixin := @CanFinMixin (htree0_countType A B) B (@fl A B) (@gl A B) (@cancelflgl A B).
Definition htree0_finType := FinType (htree0_countType A B) htree0_finMixin.

Fixpoint htreen_finMixin (n:nat): Finite.mixin_of (htreen_countType A B n).
elim n.
rewrite cteql.
exact htree0_finMixin.
intros n0 EF.
apply (@CanFinMixin
           (htreen_countType A B n0.+1)
           (sum_finType B (prod_finType A (wlistn_finType (FinType (htreen_countType A B n0) EF) w)  ))
           (@ffl A B n0) (@ggl A B n0) (@cancel_fflggl A B n0)).
Defined.

Definition htreen_finType n := Eval hnf in (@FinType (htreen_choiceType A B n) (htreen_finMixin n)).
End HtreeFinType.

Section HtreeUtils.

(** Thanks to Théo Winterhalter *)
(** An induction principle for a boolean
  predicate [P] on Htrees of height [n]:

   - it is valid for any leaf  onstructible from any element of B
   - it is valid for any node built from  an element of A and a bounded list of    trees verifying the property

  then it is valid for all trees. *)
Lemma htree_uniq_ind {A B : Type} {m : nat} : forall (P : forall n, Htree A B n -> bool),
(forall (x : B) (n : nat), P n (BLeaf A n x)) ->
(forall (he : A) (n : nat), forall l : (Wlist (Htree A B n) w), ((wall (P n) l) -> P n.+1 (BNode he l))) ->
forall t : (Htree A B m), P m t.
Proof.
  intros until t. revert t. revert m.
  fix aux 2. move aux at top.
  destruct t ;
  match goal with
  | H : _ |- _ => apply H
  end ;
  auto.
  revert w0. move:w.
  fix auxl 2.
  destruct w1.
  - econstructor.
  - cbn. apply/andP. split.
    + apply aux.
    + apply auxl.
Defined.

(** An induction principle for a property
  [P] on Htrees of height [n] *)
Lemma htree_uniq_ind_prop {A B : Type} {m : nat}: forall (P : forall n, Htree A B n -> Prop),
(forall (x : B) (n : nat), P n (BLeaf A n x)) ->
(forall (he : A) (n : nat), forall l : (Wlist (Htree A B n) w), ((w_all_prop (P n) w l) -> P n.+1 (BNode he l))) ->
forall t : (Htree A B m), P m t.
Proof.
  intros until t. revert t. revert m.
  fix aux 2. move aux at top.
  destruct t ;
  match goal with
  | H : _ |- _ => apply H
  end ;
  auto.
  revert w0. move:w.
  fix auxl 2.
  destruct w1.
  - econstructor.
  - cbn. split.
    + apply aux.
    + apply auxl.
Defined.

(** Auxiliary lemma *)
Lemma neq_sym {A : eqType} : forall (x y : A), x != y -> y != x.
Proof.
move => x y Hneq.
destruct (eqVneq y x) as [Hxy | Hxny].
+ by rewrite Hxy eq_refl in Hneq.
+ apply Hxny.
Qed.

(** Technical lemma. If [a] not in any
  sequence elements of [l] and [a] different from [b], then [a] not in
  the sequences obtained by concatenating [b] at the heads of the elements of [l] *)
Lemma all_prop_cons_notin {A : eqType} : forall (a b: A) l,
all_prop (fun sl : seq A => a \notin sl) l -> b != a -> all_prop (fun sl : seq A => a \notin sl)
  [seq b :: i | i <- l].
Proof.
induction l.
- auto.
- move => /= [Hnotina0 Hnotinl] Hneq. split.
  + rewrite negb_or. apply/andP ; split.
    - apply/neq_sym/Hneq.
    - apply Hnotina0.
  + by apply IHl.
Qed.

 (* NOT USED : Reciprocal lemma: we remove the head
 b from the elements of the list
Lemma all_prop_notin_cons {A : eqType} : forall (a b: A) l,
all_prop (fun sl : seq A => a \notin sl) [seq b :: i | i <- l] ->
all_prop (fun sl : seq A => a \notin sl) l.
Proof.
induction l.
- auto.
- move => /= [Hnotina0 Hnotinl]. rewrite negb_or in Hnotina0.
  destruct (andP Hnotina0) as [Hneq Ha0a]. split.
  + apply Ha0a.
  + by apply IHl.
Qed. *)

(** An induction principle for a property
  [P] on Htrees of height [n]. It differs
  from [htree_uniq_ind_prop] because [l]
  is a bounded sequence not a regular
  sequence that is translated to a bounded one *)

Lemma htree_uniq_ind_prop_seq {A B : Type} {m : nat}: forall (P : forall n, Htree A B n -> Prop),
(forall (x : B) (n : nat), P n (BLeaf A n x)) ->
(forall (he : A) (n : nat), forall l : (Wlist (Htree A B n) w), ((all_prop (P n) (wlist_to_seq l)) -> P n.+1 (BNode he l))) ->
forall t : (Htree A B m), P m t.

Proof.
  intros until t. revert t. revert m.
  fix aux 2. move aux at top.
  destruct t ;
  match goal with
  | H : _ |- _ => apply H
  end ;
  auto.
  revert w0. move:w.
  fix auxl 2.
  destruct w1.
  - econstructor.
  - cbn. split.
    + apply aux.
    + apply auxl.
Defined.

End HtreeUtils.

End HTree.

(** * ABTrees: generic trees with different node / leaf types *)
Section ABtree.

Section InducType.
Variable A: Type.
Variable B: Type.

(** ABtree are trees with internal node A and leaf B. They are similar to Htree but
without any bound. *)
Inductive ABtree: Type :=
  ABLeaf : B -> ABtree
| ABNode : A -> seq ABtree -> ABtree.

(** An induction principle for ABTrees for a boolean property P *)
Lemma abtree_ind : forall (P : ABtree -> bool),
(forall x : B, P (ABLeaf x)) ->
(forall h : A, forall l : (seq ABtree), ((all P l) -> P (ABNode h l))) ->
forall t : ABtree, P t.
Proof.
  intros until t. revert t.
  fix aux 1. move aux at top.
  destruct t ;
  match goal with
  | H : _ |- _ => apply H
  end ;
  auto.
  revert l.
  fix auxl 1.
  destruct l.
  - econstructor.
  - cbn. apply/andP. split.
    + apply aux.
    + apply auxl.
Defined.

(** An induction principle for ABTrees for a predicate P in Prop *)
Lemma abtree_ind_prop : forall (P : ABtree -> Prop),
(forall x : B, P (ABLeaf x)) ->
(forall h : A, forall l : (seq ABtree), ((all_prop P l) -> P (ABNode h l))) ->
forall t : ABtree, P t.
Proof.
  intros until t. revert t.
  fix aux 1. move aux at top.
  destruct t ;
  match goal with
  | H : _ |- _ => apply H
  end ;
  auto.
  revert l.
  fix auxl 1.
  destruct l.
  - econstructor.
  - cbn. split.
    + apply aux.
    + apply auxl.
Defined.

End InducType.

(** ABtrees are an equality type *)
Section ABtree_eqType.

(** A boolean equality for ABTrees *)
Fixpoint abtree_eq {A B : eqType} (t t2 : @ABtree A B) {struct t} : bool :=
    match t,t2 with
      | ABLeaf c, ABLeaf c2 => c == c2
      | ABNode a l, ABNode a2 l2 => let fix sabtree_eq (st st2 : seq (@ABtree A B)) :=
  match st,st2 with
  | [::],[::] => true
  | a::t,b::t2 => abtree_eq a b && sabtree_eq t t2
  | _,_ => false end in
(a == a2) && sabtree_eq l l2
      | _,_ => false end.

(** reflexivity *)
Lemma abtree_eq_refl {A B : eqType} : forall x : (@ABtree A B), abtree_eq x x = true.
Proof.
apply abtree_ind.

  by move => x /=.

  move => h l H /=.
  apply /andP ; split ; [auto | ].
  induction l. auto.
  apply /andP ; split.

    simpl in H ; assert (abtree_eq a a /\ all (fun t : @ABtree A B => abtree_eq t t) l).
    apply/andP ; apply H. destruct H0 as [Ha Hl] ; apply Ha.

    apply IHl.
    simpl in H ; assert (abtree_eq a a /\ all (fun t : @ABtree A B => abtree_eq t t) l).
    apply/andP ; apply H. destruct H0 as [Ha Hl] ; apply Hl.
Defined.

 (* Useless: Adding a child to two equal ABTrees  preserve equality
Lemma cons_eq_pres {A B : Type} (r : A) (a : @ABtree A B) (l l2 : seq (@ABtree A B)) :
(ABNode r l = ABNode r l2) -> (@ABNode A B r (a :: l) = ABNode r (a :: l2)).
Proof.
move => H. by inversion H.
Defined.


 If two ABTree are equal, removing the first child keeps them equal.
Lemma abtree_eq_pres_inv {A B : eqType} (r : A) (a : @ABtree A B) (l l2 : seq (@ABtree A B)) :
(abtree_eq (ABNode r (a :: l)) (ABNode r (a :: l2))) -> abtree_eq (ABNode r l)  (ABNode r l2).
Proof.
move => /= H. apply/andP. split. auto.
apply (bool_to_prop_r (bool_to_prop_r H)).
Defined.
*)

(** If two ABtrees are equal for the boolean equality, they are indeed equal *)
Lemma abtree_inv {A B : eqType} : forall x y : (@ABtree A B), abtree_eq x y = true -> x = y.
Proof.
induction x using @abtree_ind_prop.
- move => [b|a l] H /=.
  + by rewrite (eqP H).
  + by exfalso.
- move => [b|a tl] //=.
  move=>/andP [/eqP -> Hteq].
  apply/f_equal. move:tl Hteq.
  induction l;move=>[htl|tltl] // l0 /andP [H1 H2].
  apply/f_equal2.
  + destruct H as [Hheq Hreq].
    apply/Hheq/H1.
  + apply IHl;auto.
    apply H.
Qed.

(** abtree_eq is an equality *)
Lemma abtree_eq_axiom {A B : eqType} : Equality.axiom (@abtree_eq A B).
Proof.
move => x y; apply Bool.iff_reflect.
split.
  move => -> ; apply abtree_eq_refl.
  apply abtree_inv.
Defined.

(** So abtree is an equality type *)
Definition ABtree_eqMixin {A B : eqType} := EqMixin (@abtree_eq_axiom A B).

Canonical ABtree_eqType {A B : eqType} := Eval hnf in EqType (@ABtree A B) (@ABtree_eqMixin A B).

End ABtree_eqType.

(** ** abtree is a countable type *)
Section ABtree_countType.

(** Translation to ssreflect [GenTree.tree] using the fact A is a countable type. *)
Fixpoint AB_to_gen {A B : countType} (t : @ABtree A B) : GenTree.tree B := match t with
  | ABLeaf x => GenTree.Leaf x
  | ABNode x l => GenTree.Node (pickle x) (map (@AB_to_gen A B) l) end.

(** Reverse translation. Defined when we have an A value associated to each integer  *)
Fixpoint gen_to_AB {A B : countType} (t : GenTree.tree B) : option (@ABtree A B) := match t with
  | GenTree.Leaf x => Some (@ABLeaf A B x)
  | GenTree.Node x l => match (unpickle x) with
      | Some n => Some (@ABNode A B n (pmap (@gen_to_AB A B) l))
      | None   => None end end.

(** Cancelation lemma *)
Lemma canc_abtree_gentree {A B : countType} : pcancel (@AB_to_gen A B) (@gen_to_AB A B).
Proof.
move => t.
induction t using abtree_ind_prop.
- auto.
- simpl. rewrite pickleK. apply/f_equal/f_equal. induction l.
  + auto.
  + destruct H as [Ha Hl]. simpl. rewrite Ha. simpl. apply/f_equal.
    apply/IHl/Hl.
Qed.

(** ABTree is a choice type *)
Definition AB_choiceMixin {A B : countType} := PcanChoiceMixin (@canc_abtree_gentree A B).

Canonical ABtree_choiceType {A B : countType} :=
Eval hnf in ChoiceType (@ABtree A B) (@AB_choiceMixin A B).

(** ABTree is a countable type *)
Definition AB_countMixin {A B : countType} := PcanCountMixin (@canc_abtree_gentree A B).

Canonical ABtree_countType {A B : countType} :=
Eval hnf in CountType (@ABtree A B) (@AB_countMixin A B).

End ABtree_countType.

Section ABtree_utils.

(** Yet another induction principle on ABTree for boolean property *)
Lemma tst_uniq_ind {A B : Type} : forall (P : ABtree A B -> bool),
(forall x : B, P (@ABLeaf A B x)) ->
(forall h : A, forall l : (seq (@ABtree A B)), ((all P l) -> P (ABNode h l))) ->
forall t : @ABtree A B, P t.
Proof.
  intros until t. revert t.
  fix aux 1. move aux at top.
  destruct t ;
  match goal with
  | H : _ |- _ => apply H
  end ;
  auto.
  revert l.
  fix auxl 1.
  destruct l.
  - econstructor.
  - cbn. apply/andP. split.
    + apply aux.
    + apply auxl.
Defined.

(** Yet another induction principle on ABTree for predicate on Prop *)
Lemma tst_uniq_ind_prop {A B : Type} : forall (P : ABtree A B -> Prop),
(forall x : B, P (@ABLeaf A B x)) ->
(forall h : A, forall l : (seq (@ABtree A B)), ((all_prop P l) -> P (ABNode h l))) ->
forall t : @ABtree A B, P t.
Proof.
  intros until t. revert t.
  fix aux 1. move aux at top.
  destruct t ;
  match goal with
  | H : _ |- _ => apply H
  end ;
  auto.
  revert l.
  fix auxl 1.
  destruct l.
  - econstructor.
  - cbn. split.
    + apply aux.
    + apply auxl.
Defined.

(** A function transforming an [ABtree A B]
 in an [ABtree C D] given a function [f: A -> C] translating nodes and a function [g: C -> D] translating leaves *)
Fixpoint ABmap {A B C D : Type} (f  : A -> C) (g : B -> D) (t : @ABtree A B) : @ABtree C D :=
  match t with
    | ABLeaf x => ABLeaf C (g x)
    | ABNode x l => ABNode (f x) (map (ABmap f g) l) end.

(** Gives back the root element in either [A] or [B] of an [ABtree A B]*)
Definition ABroot {A B : Type} (t : @ABtree A B) : A + B := match t with
  | ABLeaf x => inr x
  | ABNode x _ => inl x end.

(** Height of an [ABtree]*)
Fixpoint ABheight {A B : Type} (t : @ABtree A B) : nat := match t with
  | ABLeaf _ => 0
  | ABNode _ l => (foldr maxn 0 (map ABheight l)).+1 end.

(** Check if an element of A is in an [ABtree A B] (in a node) *)
Fixpoint ABin {A B : eqType} (x : A) (t : @ABtree A B) : bool :=
  match t with
    | ABLeaf _ => false
    | ABNode y l => ((x == y) || (has (ABin x) l)) end.

(** Check if an element of A is not in an [ABtree A B] (in a node) *)
Definition ABnotin {A B : eqType} (x : A) (t : @ABtree A B) : bool :=
  ~~ ABin x t.

(** If x is not in a tree, it is not the element of the root and it is not in
  the children of the root *)
Lemma ABnotin_node_and {A B : eqType} (x : A) (y : A) (l : seq (@ABtree A B)) :
  ABnotin x (ABNode y l) = ((x != y) && (all (ABnotin x) l)).
Proof.
unfold ABnotin. simpl. apply/norP.
destruct (x == y).
- by move => [Habs].
- simpl. destruct (Sumbool.sumbool_of_bool(all (fun t : ABtree A B => ~~ ABin x t) l)) as [e | e].
  + by rewrite e ; split ; [ | rewrite <- all_predC].
  + by rewrite e ; move => [Htrue Hhas] ; rewrite <- all_predC in Hhas ; assert (false) ; [rewrite <- e | ].
Qed.

(** if x is not in a tree [t] and [f] injective, then (f x) is not in (ABmap f g t),
  the mapping of the tree by functions f and g *)
Lemma ABnotin_map {A B C D : eqType} (f : A -> C) (g : B -> D) (t : @ABtree A B) (x : A)
                 (Hu : ABnotin x t) (Hinjf : injective f) :
                 ABnotin (f x) (ABmap f g t).
Proof.
induction t using tst_uniq_ind_prop ; [auto | ].
unfold ABnotin in Hu. simpl in Hu. destruct (norP Hu) as [Hxh Hhas].
unfold ABnotin. unfold ABin. apply/norP ; split.
- unfold injective in Hinjf.
  assert (Habs : f x = f h -> ~~ true).
  + move => Hfeq. by rewrite (Hinjf x h Hfeq) eq_refl in Hxh.
  by apply (contraTneq Habs).
- apply/hasPn. move => y Hy. fold (@ABmap A B C D) in Hy.
  destruct (mapP Hy) as [ypred Hypredin Hypredeq].
  rewrite Hypredeq.
  apply (all_prop_in H Hypredin ((hasPn Hhas) ypred Hypredin)).
Qed.

(** Checks that a [t1] is a subtree of [t2] for the shape *)
Fixpoint subtree {A B : eqType} (t1 t2 : @ABtree A B) : bool :=
  match t2 with
    | ABLeaf _ => t1 == t2
    | ABNode y l => (t1 == t2) || has (subtree t1) l end.

(** subtree reflexive *)
Lemma subtree_refl {A B : eqType} (t : @ABtree A B) :
  subtree t t.
Proof.
destruct t. by apply/eqP.
by apply/orP;left.
Qed.

(** Checks that a [t1] is a strict subtree of [t2] for the shape *)
Definition strict_subtree {A B : eqType} (t1 t2 : @ABtree A B) : bool :=
  match t2 with
    | ABLeaf _ => false
    | ABNode y l => has (subtree t1) l end.

(** If [t1] is a subtree of [t2], any child of the root of [t1] is a strict
  subtree of [t2] *)
Lemma subtree_ssubtree {A B : eqType} (h1 : A) (x t2 : @ABtree A B)
  (l1 : seq (@ABtree_eqType A B)) :
   subtree (ABNode h1 l1) t2
 -> x \in l1 -> strict_subtree x t2.
Proof.
move:l1.
apply (@abtree_ind_prop _ _ (fun t2 => forall l1 : seq ABtree_eqType,
subtree (ABNode h1 l1) t2 -> x \in l1 -> strict_subtree x t2)).
move=>u l /eqP //.
move=>h2 l2 Hall l1 /orP [/eqP [<- <-]|/hasP [d2 Hd2in Hd2s]] Hin.
apply/hasP. exists x. apply Hin. apply subtree_refl.
simpl.
apply/hasP. exists d2. apply Hd2in.
pose Hss := (all_prop_in Hall Hd2in l1 Hd2s Hin). clearbody Hss.
destruct d2 as [|hd2 ld2]. pose Hf := eqP Hd2s. inversion Hf.
apply/orP. right. apply Hss.
Qed.

(** If [t1] is a strict subtree of [t2], the height of [t1] is strictly
   smaller than the height of [t2] *)
Lemma sstree_height {A B : eqType} (t1 t2 : @ABtree A B) :
  strict_subtree t1 t2 -> ABheight t1 < ABheight t2.
Proof.
move:t2.
apply (@abtree_ind_prop _ _ (fun t1 => forall t2,
  strict_subtree t1 t2 -> ABheight t1 < ABheight t2)).
by destruct t2.
move=>h1 l1 Hall [|h2 l2] // /hasP [st2 Hst2in Hst2sub].
simpl. rewrite ltnS. apply/fold_maxn_n_map_gtn/hasP.
exists st2. apply Hst2in. destruct st2.
pose Hf := eqP Hst2sub. inversion Hf.
apply fold_maxn_n_map_ltn. auto.
apply (all_prop_prop_decr Hall).
move=>x Hxin Hx. apply Hx.
apply (subtree_ssubtree Hst2sub Hxin).
Qed.

(** if [t] a tree and [x] in that tree, then there is a subtree of [t] whose
  root is [x] *)
Lemma ABin_extract {A B : eqType} (x : A) (t : @ABtree A B) (Hin : ABin x t):
  exists2 tbis, subtree tbis t & ABroot tbis = inl x.
Proof.
  (* y a une tactique à faire là, j'ai vu ce pattern ailleurs *)
induction t using tst_uniq_ind_prop.
- by simpl in Hin.
- destruct (orP Hin) as [Heq | Hssub].
  + by exists (ABNode h l) ; [apply/orP ; left | rewrite (eqP Heq)].
  + destruct (hasP Hssub) as [desc Hdescin Hindesc].
    destruct (all_prop_in H Hdescin Hindesc) as [tb Htbsub Htbeq].
    exists tb.
    - apply/orP ; right.
      apply/hasP. by exists desc.
    - apply Htbeq.
Qed.

(** A tree is ABuniq, if on any path, the values associated to nodes appear
   only once *)
Fixpoint ABuniq {A B : eqType} (t : @ABtree A B) : bool := match t with
  | ABLeaf _ => true
  | ABNode x l => ((all (ABnotin x) l) && (all ABuniq l)) end.

(** technical: if t is ABuniq, so is its first child *)
Lemma uniq_desc_l {A B : eqType} : forall h (a : ABtree A B) l,  ABuniq (ABNode h (a :: l)) -> ABuniq  a.
Proof.
move => h a l /= Hu.
destruct (andP Hu) as [H0 H1]. by destruct (andP H1).
Qed.

Lemma uniq_desc_r {A B : eqType} : forall h (a : ABtree A B) l,  ABuniq (ABNode h (a :: l)) -> ABuniq (ABNode h l).
Proof.
move => h a l /= Hu.
destruct (andP Hu) as [H0 H1]. apply/andP. split.
- by destruct (andP H0).
- by destruct (andP H1).
Qed.

Lemma uniq_desc {A B : eqType} : forall h (a : ABtree A B) l,  ABuniq (ABNode h l) ->
                                  a \in l -> ABuniq a.
Proof.
induction l.
- move => Hu Habs. inversion Habs.
- move => Hu Hin.
  rewrite in_cons in Hin ; destruct (orP Hin) as [Haa0 | Hal].
  + rewrite (eqP Haa0). destruct (andP Hu) as [H0 H1]. by destruct (andP H1).
  + apply/IHl/Hal/uniq_desc_r/Hu.
Qed.

Lemma ABuniq_map {A B C D : eqType} (f : A -> C) (g : B -> D) (t : @ABtree A B) 
                 (Hu : ABuniq t) (Hinjf : injective f) :
                 ABuniq (ABmap f g t).
Proof.
induction t using tst_uniq_ind_prop ; [ by [] | apply/andP ; split].
- (*destruct (andP Hu) as [Hallnotin Halluniq].*)
  apply Bool.not_false_is_true.
  move => /allP Habss. destruct Habss. move => y Hy. fold (@ABmap A B C D) in Hy.
  destruct (mapP Hy) as [yor Hyorin Hyoreq].
  pose Hhnotinyor := allP (bool_to_prop_l Hu) _ Hyorin.
  rewrite Hyoreq.
  pose Hyor := all_prop_in H Hyorin (uniq_desc Hu Hyorin). 
  apply (ABnotin_map g Hhnotinyor Hinjf).
- apply/allP. move => x /mapP Hx. fold (@ABuniq C D).
  destruct Hx as [xpred Hxpredin Hxpredeq].
  rewrite Hxpredeq.
  apply (all_prop_in H Hxpredin (uniq_desc Hu Hxpredin)).
Qed.

Fixpoint ABwidth {A B : Type} (t : @ABtree A B) : nat := match t with
  | ABLeaf _ => 0
  | ABNode _ l => (foldr maxn (size l) (map ABwidth l)) end.

Lemma ABwidth_cons {A B : Type} {w : nat} (x : A) (tl : seq (@ABtree A B)) (Hsize : size tl <= w)
(Hwidth : all_prop (fun x => ABwidth x <= w) tl) : ABwidth (ABNode x tl) <= w.
Proof.
apply (fold_maxn_n_map_leq Hsize Hwidth).
Qed.

Lemma width_desc_l {A B : Type} {w : nat} : forall h (a : ABtree A B) l,  ABwidth (ABNode h (a :: l)) <= w -> ABwidth a <= w.
Proof.
move => h a l /= Hw.
rewrite geq_max in Hw.
by destruct (andP Hw).
Qed.

Lemma width_desc_r {A B : Type} {w : nat} : forall h (a : ABtree A B) l,
  ABwidth (ABNode h (a :: l)) <= w -> (foldr maxn (size l) (map ABwidth l) <= w).
Proof.
move => h a l /= Hw.
rewrite geq_max in Hw.
destruct (andP Hw) as [Ha Hl].
by apply/foldr_maxn_base/Hl.
Qed.

(** After a map, the width cannot increase *)
Lemma ABwidth_map {A B C D : eqType} {w : nat} (f : A -> C) (g : B -> D)
                  (t : @ABtree A B) (Hw : ABwidth t <= w) : ABwidth (ABmap f g t) <= w.
Proof.
induction t using tst_uniq_ind_prop ; [ by [] | ].
simpl. rewrite size_map.
apply/fold_maxn_n_map_leq.
- apply/leq_fold_base/Hw.
- induction l ; [auto | destruct H as [Ha Hl] ; rewrite geq_max in Hw ; destruct (andP Hw) as [Hwa Hwl] ; split ].
  + apply/Ha/Hwa.
  + apply/IHl/Hl/(foldr_maxn_base (leqnSn (size l)))/Hwl.
Qed.

(** ABbranches Computes the sequence of node labels along a path from the root to the leaves.*)
Fixpoint ABbranches {A B : Type} (t : @ABtree A B) : seq (seq A) := match t with
  | ABLeaf _ => [:: [::]]
  | ABNode a l => [:: [:: a]] ++ map (cons a) (flatten (map ABbranches l)) end.

Lemma sub_branches_head {A B : eqType} : forall (s : seq A) (h : A) (l : seq (ABtree A B)),
all_prop (fun x : seq_predType A => {subset x <= s}) (ABbranches (ABNode h l)) -> h \in s.
Proof.
simpl. move=>s h l [H1 H2].
apply/H1. by rewrite mem_seq1.
Qed.

Lemma ABnotin_branches {A B : eqType} : forall (a : ABtree A B) h, 
ABnotin h a -> all_prop (fun sl : seq A => h \notin sl) (ABbranches a).
Proof. 
induction a using tst_uniq_ind_prop;
move => // h0. rewrite ABnotin_node_and.
move=> /andP [Hh Hbr] /=;split.
- rewrite mem_seq1. apply Hh.
- induction l as [|a l Hl];auto.
  destruct H as [H1 H2].
  destruct (andP Hbr) as [H3 H4]. clear Hbr.
  rewrite map_cat; apply all_prop_cat;split.
  + apply (all_prop_cons_notin).
    apply/H1/H3. apply/neq_sym/Hh.
  + by apply Hl.
Qed.

(** If all the branches [t] are subsequences of [s], the height of [t]
   is smaller than the size of [s] *)
Lemma uniq_ab_size {A B : eqType} (t : @ABtree A B) (s : seq A) :
  ABuniq t -> (all_prop (fun x => {subset x <= s}) (ABbranches t)) -> ABheight t <= size s.
Proof.
move:s.
induction t using tst_uniq_ind_prop;auto.
move => /= s Hu [Hh Hl]. 
pose s' := rem h s.
assert (HhIns : h \in s).
- apply/sub_branches_head;split;[apply Hh| apply Hl].  
apply fold_maxn_n_map_ltn.
- by destruct s.
- apply (all_prop_prop_decr H).
  move=>x Hxin Hp.
  assert (Hsize : size s = (size s').+1).
  + unfold s'. apply (seq_in_rem_size HhIns).
  destruct (andP Hu) as [Hu1 Hu2].
  rewrite Hsize. apply Hp.
  apply (allP Hu2 _ Hxin).
  apply sub_rem_seq. 
  + apply (all_prop_seq_decr Hl).
    move=>y /mapP [z Hz ->].
    apply/mapP. exists z. apply/flattenP.
    exists (ABbranches x). apply/mapP.
    by exists x. apply Hz. reflexivity.
  + apply (ABnotin_branches (allP Hu1 _ Hxin)).
Qed.

Equations h_to_ab_tree {A B : Type} {w h : nat} (t : @Htree w A B h) : @ABtree A B by wf h :=
  h_to_ab_tree (@BLeaf _ x) := @ABLeaf A B x ;
  h_to_ab_tree (@BNode n y l) := ABNode y (map (fun tb : @Htree w A B n => @h_to_ab_tree A B w n tb) (wlist_to_seq l)).

Lemma h_to_ab_w_bound {A B : Type} {w h : nat} (t : @Htree w A B h) : ABwidth (h_to_ab_tree t) <= w.
Proof.
induction t using htree_uniq_ind_prop_seq.
  - auto.
  - rewrite h_to_ab_tree_equation_2. simpl.
    apply fold_maxn_n_map_leq.
      + rewrite size_map ; apply wlist_to_seq_size.
      + pose sl := (wlist_to_seq l). fold sl. fold sl in H. induction sl.
          - auto.
          - simpl in H. destruct H as [Ha Hsl]. split.
            + apply Ha.
            + apply/IHsl/Hsl.
Defined.

(** Translation of an ABTree to a HTree, we use [BLeaf def] to not exceed
   the height. *)
Fixpoint ABtree_to_H {A B : eqType} (w h : nat) (def : B) (s : ABtree A B) : Htree w A B h := match h with
   0 => match s with
              | ABLeaf x => BLeaf _ A 0 x
              | ABNode _ _ => BLeaf _ A 0 def end
  | h'.+1 => match s with
              | ABLeaf x => BLeaf _ A h'.+1 x
              | ABNode x l => BNode x (seq_to_wlist w (map (@ABtree_to_H A B w h' def) l)) end end.

(** Converting a HTree to an ABtree and back gives the original tree *)
Lemma htree_abtreeK {A B : eqType} {w h : nat} (def : B) (t : Htree w A B h) : (ABtree_to_H w h def (h_to_ab_tree t)) = t.
Proof.
induction t using htree_uniq_ind_prop_seq.
  - by destruct n.
  - rewrite h_to_ab_tree_equation_2 ; simpl ; apply f_equal.
    induction l.
      + by destruct n0.
      + simpl. destruct H as [Hx Hl].
        rewrite Hx ; apply f_equal.
        apply/IHl/Hl.
Qed.

(** If the width and height are within bounds, the conversion of an ABTree to
 an HTree and back gives also the original tree *)
Lemma abtree_htreeK {A B : eqType} {w h : nat} (def : B) (t : ABtree A B) (Hw : ABwidth t <= w) (Hh : ABheight t <= h) :
 (h_to_ab_tree (ABtree_to_H w h def t)) = t.
Proof.
move : w h Hw Hh.
induction t using tst_uniq_ind_prop.
  - by destruct h.
  - move => w h0 Hw Hh.
    destruct h0.
    + inversion Hh.
    + simpl. rewrite h_to_ab_tree_equation_2 ; simpl ; apply f_equal.
      rewrite seq_wlistK. rewrite <- map_comp.
      move : w Hw H.
      induction l.
      - by destruct w.
      - move => w Hw H. destruct w.
        + simpl in Hw. assert ((foldr maxn (size l).+1 [seq ABwidth i | i <- l]) <= 0). apply leq_trans with (n := maxn (ABwidth a) (foldr maxn (size l).+1 [seq ABwidth i | i <- l])).
          apply leq_maxr. apply Hw.
          assert (size l < 0). apply leq_trans with (n := foldr maxn (size l).+1 [seq ABwidth i | i <- l]). apply leq_fold_maxl. apply H0.
          inversion H1.
        + simpl. destruct H as [Ha Hl]. rewrite Ha. apply f_equal. apply IHl.
      simpl ; simpl in Hh. apply leq_ltn_trans with (n := maxn (ABheight a) (foldr maxn 0 [seq ABheight i | i <- l])).
      apply/leq_maxr. apply Hh.
      simpl ; simpl in Hw. apply leq_trans with (n := maxn (ABwidth a) (foldr maxn (size l).+1 [seq ABwidth i | i <- l])).
      apply leq_trans with (n := (foldr maxn (size l).+1 [seq ABwidth i | i <- l])). by apply (@foldr_maxn_base (size l).+1).
      apply leq_maxr. apply Hw. apply Hl. simpl in Hw. apply leq_trans with (n := maxn (ABwidth a) (foldr maxn (size l).+1 [seq ABwidth i | i <- l])).
      apply/leq_maxl. apply Hw. simpl in Hh. apply leq_trans with (n := maxn (ABheight a) (foldr maxn 0 [seq ABheight i | i <- l])).
      apply leq_maxl. apply Hh. simpl in Hw. apply leq_trans with (n := foldr maxn (size l) [seq ABwidth i | i <- l]). rewrite size_map. apply leq_fold_maxl. apply Hw.
Qed.

(** Huniq is defined as ABuniq on the converted tree (ie forgetting bounds) *)
Definition Huniq {A B : eqType} {w h : nat} (t : @Htree w A B h) : bool :=
  ABuniq (h_to_ab_tree t).

Lemma uniq_ab_htree {A B : eqType} {w h : nat} (tu : @Htree w A B h) (H : Huniq tu) : ABuniq (h_to_ab_tree tu).
Proof.
by induction tu.
Qed.

End ABtree_utils.

End ABtree.

(** * WUTree : Width and uniqueness constrained ABtrees. *)
Section WUtree.

(** WU constrains an ABtree t to have a bounded width and unique leaves on branch. The uniqueness constraint puts a bound on the height if A finite
and in that case makes ABtree similar to Htrees. *)
Definition wu_pred {A B : eqType} {w : nat} (t : @ABtree A B) := ((ABuniq t) && (ABwidth t <= w)).

(** If A tree fullfills [wu_pred] so do its children *)
Lemma wu_pred_descs {A B : eqType} {w : nat} (h : A) (l : seq (@ABtree A B)) :
  @wu_pred A B w (ABNode h l) -> all (@wu_pred A B w) l.
Proof.
induction l.
- auto.
- move => /andP [Hu Hw].
  apply/andP ; split.
  + apply/andP ; split ; [apply/uniq_desc_l/Hu | apply/width_desc_l/Hw].
  + apply/IHl/andP ; split ; [apply/uniq_desc_r/Hu | apply/width_desc_r/Hw ].
Qed.

(** A subtree of a tree fullfilling [wu_pred] is also a [wu_pred] tree *)
Lemma wu_pred_sub {A B : eqType} {w : nat} (t1 t2 : @ABtree A B) (Hsub : subtree t1 t2)
  (Hwupred : @wu_pred A B w t2) : @wu_pred A B w t1.
Proof.
induction t2 using abtree_ind_prop.
- by rewrite (eqP Hsub).
- destruct (orP Hsub) as [Heq | Hssub].
  + by rewrite (eqP Heq).
  + destruct (hasP Hssub) as [x Hxinl Hxsub].
    pose Hl := wu_pred_descs Hwupred.
    pose Hwux := allP Hl _ Hxinl.
    apply (all_prop_in H Hxinl Hxsub Hwux).
Qed.

(** map preserves the [wu_pred] property as long as the function on internal
 node labels is injective. *)
Lemma wu_pred_map {A B C D: eqType} {w : nat} (f : A -> C) (g : B -> D) 
                  (Hfi : injective f) (t : @ABtree A B) 
                  (H : @wu_pred A B w t) : @wu_pred C D w (ABmap f g t).
Proof.
destruct (andP H) as [Hu Hw].
apply/andP ; split.
- apply (@ABuniq_map A B C D f g t Hu Hfi).
- apply (@ABwidth_map A B C D w f g t Hw).
Qed.

Definition wu_merge {A B : eqType} {w : nat} {t : @ABtree A B} (Hu : ABuniq t) (Hw : ABwidth t <= w) :
  (@wu_pred A B w t).
Proof.
by apply/andP ; split.
Qed.

(** We define WUtree as a structure made of an ABtree respecting the [wu_pred]
   condition *)
Structure WUtree {A B : eqType} (w : nat) := Wht {wht :> @ABtree_eqType A B ; Hwht : @wu_pred A B w wht}.

(** WUtree is an eqType *)
Canonical WUtree_subType {A B : eqType} {w : nat} := Eval hnf in [subType for (@wht A B w)].
Canonical WUtree_eqType {A B : eqType} {w : nat} := Eval hnf in EqType (@WUtree A B w) [eqMixin of (@WUtree A B w) by <:].

(** ** WUtree is an finite Type *)
Section WUtree_finType.

(** If A is a finite type, any sequence of A is a subsequence of the enumeration of A*)
Lemma subset_enum {A : finType} : forall (l : seq A), {subset l <= enum A}.
Proof.
by move => l x Hxl ; rewrite mem_enum.
Qed.

(** Lifted to sequence of sequences *)
Lemma subsubset_enum {A : finType} : forall (l : seq (seq A)),
all_prop (fun x => {subset x <= enum A}) l.
Proof.
induction l.
- move => //.
- split.
  + apply subset_enum.
  + apply IHl.
Qed.

(** Core lemma: the height of a WUtree (in fact of an ABtree respecting uniqueness) is bound by the cardinal of A. *)
Lemma height_WUtree {A B : finType} {w : nat} (t : @WUtree A B w) : ABheight (wht t) < #|A|.+1.
Proof.
rewrite ltnS ; rewrite [card]unlock.
destruct t as [t Hwut].
apply uniq_ab_size.
- apply(bool_to_prop_l Hwut).
- apply subsubset_enum.
Qed.

(** Translation from an HTree respecting [Huniq] to a WUTree *)
Definition h_to_wu_tree {A B : eqType} {w h : nat} (t : @Htree w A B h) (Hu : Huniq t) : @WUtree A B w :=
  Wht (wu_merge (uniq_ab_htree Hu) (h_to_ab_w_bound t)).

(** Translation from a WUTree to an HTree *)
Definition WUtree_to_H {A B : eqType} {w h : nat} {def : B} (t : @WUtree A B w) : @Htree w A B h :=
  match t with
     | @Wht _ _ _ t _ => @ABtree_to_H A B w h def t end.

(** An htree translated to a WUtree and back gives back the initial htree *)
Lemma htree_wutreeK {A B : eqType} {w h : nat} (def : B) (t : Htree w A B h) (Hu : Huniq t) : (@WUtree_to_H A B w h def (h_to_wu_tree Hu)) = t.
Proof.
by apply htree_abtreeK.
Qed.

(** The translation of a WUtree respect Huniq *)
Lemma uniq_h_wutree {A B : eqType} {w h : nat} {def : B} (tu : @WUtree A B w) (Hh : ABheight (wht tu) <= h) : @Huniq A B w h (@WUtree_to_H A B w h def tu).
Proof.
destruct tu as [tu Hwut].
assert (Hut : ABuniq tu).
  - apply (bool_to_prop_l Hwut).
assert (Hw : ABwidth tu <= w).
  - apply (bool_to_prop_r Hwut).
simpl.
unfold Huniq. by rewrite abtree_htreeK.
Qed.

(** A WUtree translated to an HTree and back gives back the same WUtree as long
  as we consider the value. *)
Lemma wutree_htree_valK {A B : eqType} {w h : nat} (def : B) (t : @WUtree A B w) (Hh : ABheight (wht t) <= h) :
 val (h_to_wu_tree (@uniq_h_wutree A B w h def t Hh)) = val t.
Proof.
destruct t as [t Hwut].
assert (Hut : ABuniq t).
  - apply (bool_to_prop_l Hwut).
assert (Hw : ABwidth t <= w).
  - apply (bool_to_prop_r Hwut).
simpl. by apply abtree_htreeK.
Qed.

(** A WUtree translated to an HTree and back gives back the same WUtree *)
Lemma wutree_htreeK {A B : eqType} {w h : nat} (def : B) (t : @WUtree A B w) (Hh : ABheight (wht t) <= h) :
 (h_to_wu_tree (@uniq_h_wutree A B w h def t Hh)) = t.
Proof. 
apply/val_inj/wutree_htree_valK. 
Qed.

Lemma maxn_0_n : forall n, maxn 0 n = n.
Proof.
by case.
Defined.

(** If [t] verifies [Huniq], its translation as ABtree verifies [ABuniq] *)
Lemma Huniq_to_ABuniq {A B : eqType} {w h : nat} {t : @Htree w A B h} (H : Huniq t) : ABuniq (h_to_ab_tree t).
Proof.
dependent elimination t.
- auto.
- rewrite h_to_ab_tree_equation_2. unfold Huniq in H. rewrite h_to_ab_tree_equation_2 in H. apply H.
Defined.

(** The translation of an Htree of width w (read 'at most w') is at most w *)
Lemma Htree_to_ABwidth {A B : eqType} {w h : nat} (t : Htree w A B h) : ABwidth (h_to_ab_tree t) <= w.
Proof.
induction t using htree_uniq_ind_prop_seq.
  - auto.
  - rewrite h_to_ab_tree_equation_2. simpl. rewrite <- map_comp. apply fold_maxn_n_map_leq.
      + rewrite size_map. apply wlist_to_seq_size.
      + simpl. apply H.
Defined.

(** The full translation from WUtree to Htree with the conditions extracted.*)
Definition wu_tree_of_htree {A B : finType} {w h : nat} (t : @Htree w A B h) (H : Huniq t) : @WUtree A B w :=
  Wht (wu_merge (Huniq_to_ABuniq H) (h_to_ab_w_bound t)).

(** Cancellation with the full*)
Lemma hutree_abtreeK {A B : finType} {w : nat} {def : B} {x : Htree w A B #|A| } (Px : Huniq x) : ABtree_to_H w #|A| def (wht (h_to_wu_tree Px)) = x.
Proof.
by rewrite htree_abtreeK.
Qed.
(** A property verified by all Htree verifying uniq can be lifted in a property
   verified by all WUtree. *)
Lemma wu_htree_elim {A B : finType} {w : nat} {def : B} : forall K : WUtree w -> Type,
 (forall (x : Htree w A B #|A|) (Px : Huniq x), K (h_to_wu_tree Px)) -> forall u : WUtree w, K u.
Proof.
by move => K HK u ; rewrite <- (@wutree_htreeK A B w #|A| def u (height_WUtree u)).
Qed.

(** WUTree is a subtype, eqtype, choiceType, countable type, finite type *)
Definition wutree_subType {A B : finType} {w : nat} {def : B} :=
  Eval hnf in (SubType (@WUtree A B w) (@WUtree_to_H A B w #|A| def) (@h_to_wu_tree A B w #|A|) (@wu_htree_elim A B w def) (@htree_wutreeK A B w #|A| def)).

Definition wutree_eqMixin {A B : finType} {w : nat} {def : B} :=
  @SubEqMixin (@htreen_eqType w A B #|A|) (@Huniq A B w #|A|) (@wutree_subType A B w def).
Canonical wutree_eqType {A B : finType} {w : nat} {def : B} :=
  Eval hnf in EqType (@WUtree A B w) (@wutree_eqMixin A B w def).

Definition wutree_choiceMixin {A B : finType} {w : nat} {def : B} :=
  @sub_choiceMixin (@htreen_choiceType w A B #|A|) (@Huniq A B w #|A|) (@wutree_subType A B w def).
Canonical wutree_choiceType {A B : finType} {w : nat} {def : B} :=
  Eval hnf in ChoiceType (@WUtree A B w) (@wutree_choiceMixin A B w def).

Definition wutree_countMixin {A B : finType} {w : nat} {def : B} :=
  @sub_countMixin (@htreen_countType w A B #|A|) (@Huniq A B w #|A|) (@wutree_subType A B w def).
Canonical wutree_countType {A B : finType} {w : nat} {def : B} :=
  Eval hnf in CountType _ (@wutree_countMixin A B w def).

Definition wutree_subcountMixin {A B : finType} {w : nat} {def : B} :=
  @sub_countMixin (@htreen_finType w A B #|A|) (@Huniq A B w #|A|) (@wutree_subType A B w def).
Canonical wutree_subCountType {A B : finType} {w : nat} {def : B} :=
  Eval hnf in [subCountType of (@wutree_countType A B w def)].

Definition wutree_finMixin {A B : finType} {w : nat} {def : B} :=
  @SubFinMixin (@htreen_finType w A B #|A|) (@Huniq A B w #|A|) (@wutree_subCountType A B w def).
Canonical wutree_finType {A B : finType} {w : nat} {def : B} :=
  Eval hnf in FinType (@wutree_subCountType A B w def) (@wutree_finMixin A B w def).

Coercion wutree_fin {A B : finType} {w : nat} {def : B} (x : @WUtree A B w) : @wutree_finType A B w def := x.

(** [WUtree option] as a finite type *)
Definition wutree_option_finType {A B : finType} {w : nat} {def : B} :=
  Eval hnf in option_finType (@wutree_finType A B w def).

Coercion wutree_option_fin {A B : finType} {w : nat} {def : B} (x : option (@WUtree A B w)) :
  @wutree_option_finType A B w def := x.

End WUtree_finType.

(** ** WUTree as a subtype *)
Section WUtree_subFinType.

(** Transform an ABTree seen as a countable type to a WUtree (finite type)
  if [wu_pred] is valid *)
Definition WU_sf_sub {A B : finType} {w : nat} {def : B} : forall (x : @ABtree_countType A B), @wu_pred A B w x -> (@wutree_finType A B w def).
move => x Hx. apply ({| wht := x; Hwht := Hx |}).
Defined.

(** Replace a proof on [WUtree] by a proof on [ABTree] respecting [wu_pred] *)
Lemma WU_sf_elim {A B : finType} {w : nat} {def : B} : forall K : (@wutree_finType A B w def) -> Type,
        (forall (x : (@ABtree_countType A B)) (Px : @wu_pred A B w x), K (@WU_sf_sub A B w def x Px)) ->
          forall u : (@wutree_finType A B w def), K u.
Proof.
move => K HK u.
destruct u as [whu Hwhu].
apply HK.
Qed.

(** We can extract back the ABTree after transforming it to a WUtree *)
Lemma WU_sf_subK {A B : finType} {w : nat} {def : B} : forall (x : (@ABtree_countType A B)) (Px : @wu_pred A B w x),
        @wht A B w (@WU_sf_sub A B w def x Px) = x.
Proof.
by [].
Qed.

Canonical WUtree_sf {A B : finType} {w : nat} {def : B} := Eval hnf in
  @SubType (@ABtree A B) (@wu_pred A B w) (@wutree_finType A B w def) (@wht A B w)
      (@WU_sf_sub A B w def) (@WU_sf_elim A B w def) (@WU_sf_subK A B w def).

  (* It would be cleaner by using SubFinType in WUtree_sf, but I did not manage to ... *)
Definition WU_fsf {A B : finType} {w : nat} {def : B} := [finType of (@WUtree_sf A B w def)].

Definition wutree_option_fsfType {A B : finType} {w : nat} {def : B} :=
  Eval hnf in option_finType (@WU_fsf A B w def).

Coercion wutree_option_fst {A B : finType} {w : nat} {def : B} (x : option (@WUtree A B w)) :
  @wutree_option_fsfType A B w def := x.

End WUtree_subFinType.

(** ** Utilities for WUTree *)
Section WUtree_utils.

(** A leaf trivially verifies wu_pred which is a condition on nodes *)
Lemma wu_pred_leaf {A B : eqType} {w : nat} (x : B) : @wu_pred A B w (ABLeaf A x).
Proof. by []. Qed.

(** Leaf constructor for WUtrees *)
Definition wu_leaf {A B : eqType} {w : nat} (x : B) : @WUtree A B w :=
  @Wht A B w (ABLeaf A x) (@wu_pred_leaf A B w x).

(** NotIn for WUtree *)
  (* coercion does not seem to be working under wall, made explicit here *)
Definition WUnotin {A B : eqType} {w : nat} (x : A) (t : @WUtree A B w) := ABnotin x (wht t).


Lemma AB_to_WUnotin_seq {A B : eqType} {w : nat} (x : A) (ts : seq (@WUtree A B w)) : (all (WUnotin x) ts) -> all (ABnotin x) (map (@wht A B w) ts).
Proof.
induction ts.
- auto.
- move => /= /andP [Ha Hl]. apply/andP. split.
  + apply Ha.
  + apply/IHts/Hl.
Qed.
(** If x is not in a list of WUTree, the tree made of x and all those trees
  as children verifies the unicity condition *)
Lemma wu_cons_uniq {A B : eqType} {w : nat} (x : A) (tl : seq (@WUtree A B w)) (H : all (WUnotin x) tl) :
 (ABuniq (ABNode x (map (@wht A B w) tl))).
Proof.
apply/andP ; split.
- apply/AB_to_WUnotin_seq/H.
- induction tl.
  + auto.
  + apply/andP ; split.
    - destruct a as [ab Ha]. apply (bool_to_prop_l Ha).
    - apply IHtl. apply (bool_to_prop_r H).
Qed.

Lemma wu_list_width {A B : eqType} {w : nat} (tl : seq (@WUtree A B w))
: all_prop (fun x => ABwidth x <= w) (map (@wht A B w) tl).
by induction tl ; [ | split ; [destruct a as [a Ha] ; destruct (andP Ha) |]].
Qed.

(** Definition of a node constructor for WUtrees taking a node label [x] and
  a sequence of WUtrees [tl] and the condition that must be respected:
  - size of the list below [w]
  - label [x] does not appear in the children [tl].
 *)
Definition wu_cons {A B : finType} {w : nat} {def : B} (x : A) (tl : seq (@WUtree_sf A B w def)) (Htl : size tl <= w)
(H : all (WUnotin x) tl) : @WUtree_sf A B w def :=
  Wht (wu_merge (@wu_cons_uniq A B w x tl H) (@ABwidth_cons A B w x (map (@wht A B w) tl) (size_map_leq Htl) (wu_list_width tl))).

(** Constructor with a Wlist for the children (encoding the width constraint) *)
Definition wu_cons_wlist {A B : finType} {w : nat} {def : B} (x : A) (tl : Wlist (@WUtree_sf A B w def) w)
(H : wall (WUnotin x) tl) : @WUtree_sf A B w def :=
wu_cons (wlist_to_seq_size tl) (wall_to_all H).

Definition wu_pcons_wlist {A B : finType} {w : nat} {def : B} (x : A) (tl : Wlist (@WUtree_sf A B w def) w) : @wutree_option_fsfType A B w def :=
  match Sumbool.sumbool_of_bool(wall (WUnotin x) tl) with
    | left H => Some (wu_cons_wlist H)
    | in_right => None
  end.

Definition wu_pcons_seq {A B : finType} {w : nat} {def : B} (x : A) (s : seq (@WUtree_sf A B w def)) : @wutree_option_fsfType A B w def  :=
  wu_pcons_wlist x (seq_to_wlist w s).

Definition wu_pcons_tup {A B : finType} {w n : nat} {def : B} (x : A) (tl : n.-tuple(@WUtree_sf A B w def)) (Hn : n <= w) : @wutree_option_fsfType A B w def  :=
  wu_pcons_wlist x (seq_to_wlist w (val tl)).

(** A map function on WUtrees *)
Definition wu_map {A B C D : eqType} {w : nat} (f : A -> C) (g : B -> D) 
                  (Hfi : injective f) (t : @WUtree A B w) :
                  @WUtree C D w.
destruct t as [t Ht].
apply (Wht (@wu_pred_map A B C D w f g Hfi t Ht)).
Defined.

End WUtree_utils.

End WUtree.
