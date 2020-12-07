(**************************************************************************)
(*                                                                        *)
(*  This file is part of octant-proof.                                    *)
(*                                                                        *)
(*  Copyright (C) 2019-2020 Orange                                        *)
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

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset. 

From Equations Require Import Equations Signature.
Set Implicit Arguments.

Unset Strict Implicit.

(** * uniq_seq: finite sequences, bounded by unicity *)
Section uniq_seq.

(** ** Definition *)

Structure uniq_seq {A : eqType} := {useq :> seq A ; buniq : uniq useq}.

Lemma andP_to_uniq {A : eqType} {t : A} {b : uniq_seq} (H : t \notin (useq b) /\ uniq b) : uniq (t::b).
Proof.
by apply/andP.
Qed.

(** ** uniq_seq is a subtype of seq *)
Canonical uniq_seq_subType {A : eqType} := Eval hnf in [subType for @useq A].
(** ** as well as eqType, choiceType, countType and subCountType *)
Canonical uniq_seq_eqType {A : eqType} := Eval hnf in EqType _ [eqMixin of (@uniq_seq A) by <:].
Canonical uniq_seq_choiceType {A : choiceType} := Eval hnf in ChoiceType _ [choiceMixin of (@uniq_seq A) by <:].
Canonical uniq_seq_countType {A : countType} := Eval hnf in CountType _ [countMixin of (@uniq_seq A) by <:].
Canonical uniq_seq_subCountType {A : countType} := Eval hnf in [subCountType of (@uniq_seq A)].

Lemma notinnil {A : eqType} (x : A) : x \notin [::].
Proof.
auto.
Qed.

(** ** constructors for uniq_seq *)
Definition unil {A : eqType} : @uniq_seq A  := {| useq := [::]; buniq := is_true_true |}.
Definition ucons1 {A : eqType} (t : A) :=
  {| useq := [:: t]; buniq := notinnil t |}.
Definition ucons {A : eqType} (t : A) (b : uniq_seq) (H : t \notin (useq b)) : uniq_seq :=
{| useq := t :: b; buniq := (andP_to_uniq (conj H (buniq b))) |}.
(* tries to add t to b *)
Definition pucons {A : eqType} (t : A) (b : @uniq_seq A) : @uniq_seq A :=
 match Sumbool.sumbool_of_bool (t \notin (useq b)) with
    | left H => ucons H
    | in_right => b
  end.

Lemma uniq_behead {A : eqType} (s : seq A) : uniq s -> uniq (behead s).
Proof.
induction s as [|h l Hs];auto.
by move=>/andP [].
Qed.

Definition useq_behead {A : eqType} (us : @uniq_seq A) : @uniq_seq A :=
  match us with
    | {| useq := s; buniq := Hus |} => {| useq := behead s; buniq := uniq_behead Hus |}
end.

Definition useq_hd {A : eqType} (us : @uniq_seq A) : option A :=
  match us with
    | {| useq := [::] |} => None
    | {| useq := hd :: tl |} => Some hd end.

(** ** uniq_seq is a finType *)
(* thanks to Arthur Azevedo De Amorim *)
Lemma size_useq {A : finType} (d : @uniq_seq A) : size d < #|A|.+1.
Proof.
rewrite ltnS [card]unlock uniq_leq_size ?buniq // => ?. 
rewrite mem_enum. auto.
Qed.

Definition tag_of_uniq_seq {A : finType} (d : @uniq_seq A) : {k : 'I_#|A|.+1 & k.-tuple A} :=
  @Tagged _ (Sub (size d) (size_useq d))
            (fun k : 'I_#|A|.+1 => k.-tuple A)
            (in_tuple d).

Definition uniq_seq_of_tag {A : finType} (t : {k : 'I_#|A|.+1 & k.-tuple A}) : option (@uniq_seq_countType A) :=
  insub (val (tagged t)).

Lemma tag_of_dbranchK {A : finType} : pcancel (@tag_of_uniq_seq A) uniq_seq_of_tag.
Proof. by rewrite /tag_of_uniq_seq /uniq_seq_of_tag=> x; rewrite valK. Qed.

Definition uniq_seq_finMixin {A : finType} := PcanFinMixin (@tag_of_dbranchK A).
Canonical uniq_seq_finType {A : finType} := Eval hnf in FinType (@uniq_seq A) uniq_seq_finMixin.

End uniq_seq.

(** * Wlist: finite sequences, with a size bounded by a nat *)
Section Wlist.

(** ** Definition *)

Inductive Wlist (X: Type): nat -> Type :=
  Bnil : forall n, (Wlist X n)
| Bcons : forall n, X -> (Wlist X n) -> (Wlist X n.+1).

(** ** Canceling lemmas *)

Section Cancel.

Variable A: Type.

Definition g (_: unit) := (Bnil A 0).

Definition f (x: Wlist A 0) := tt.

Lemma nil_list0 : forall n (x: Wlist A n), (n = 0) -> (eq x (Bnil A n)).
intros n x.
elim x.
auto.
intros.
contradict H0.
auto.
Defined.

Lemma nil0 : forall (x: Wlist A 0), (eq x (Bnil A 0)).
intro; by [apply nil_list0].
Defined.

Lemma cancelfg : cancel f g.
intro x.
rewrite (nil0 x).
auto.
Defined.

Definition gg (n: nat) (x: unit + A * Wlist A n) : (Wlist A n.+1) :=
match x with
| inl _ => Bnil A n.+1
| inr (H1, H2) => Bcons H1 H2
end.

Derive Signature for Wlist.
Equations ff (n : nat) (x : Wlist A n.+1) : (unit + A * Wlist A n) :=
  ff (Bnil _) := inl tt ;
  ff (Bcons a l) := inr (a,l).

Lemma cancelffgg: forall n, cancel (@ff n) (@gg n).
intros n x.
dependent elimination x; compute; auto.
Defined.

End Cancel.

(** ** Wlist is a type with dedicable equality *)
Section WlistEqType.
Variable A: eqType.

Definition wlist0_eqMixin := CanEqMixin (@cancelfg A).
Definition wlist0_eqType := EqType (Wlist A 0) wlist0_eqMixin.

Fixpoint wlistn_eqMixin n : Equality.mixin_of (Wlist A n).
elim n.
exact wlist0_eqMixin.
intros n0 EM.
apply (@CanEqMixin _ (sum_eqType unit_eqType (prod_eqType A (Equality.Pack EM))) (@ff A n0) (@gg A n0) (@cancelffgg A n0)).
Defined.

Definition wlistn_eqType n := Eval hnf in EqType (Wlist A n) (wlistn_eqMixin n).
End WlistEqType.

(** ** Wlist is a subtype of seq *)
Section WlistSubType.

Fixpoint wlist_to_seq {X : Type} {m : nat} (s : Wlist X m) : seq X := match s with
  | Bnil _ => [::]
  | Bcons _ a b => a :: (wlist_to_seq b) end.

Fixpoint seq_to_wlist {X : Type} (m : nat) (s : seq X) := match m with 
  0 => Bnil X 0 
  | m'.+1 => match s with 
              [::] => Bnil X m'.+1 
              | a :: l => Bcons a (seq_to_wlist m' l) end end.

Lemma seq_to_bnil {X : Type} (m : nat) : @seq_to_wlist X m [::] = Bnil X m.
Proof.
by destruct m.
Qed.

Lemma wlist_seqK {X : Type} {m : nat} (l : Wlist X m) : (seq_to_wlist m (wlist_to_seq l)) = l.
Proof.
by induction l ; [destruct n | simpl ; apply/f_equal/IHl].
Qed.

Lemma seq_wlistK {X : Type} {m : nat} (l : seq X) (H : size l <= m) : (wlist_to_seq (seq_to_wlist m l)) = l.
Proof.
move:m H.
induction l.
- by destruct m.
- move => m H ; destruct m.
  + inversion H.
  + simpl ; apply/f_equal/IHl/H.
Qed.

Definition seq_to_wlist_uncut {X : Type} {m : nat} (s : seq X) (H : size s <= m) : Wlist X m :=
  seq_to_wlist m s.

Lemma wlist_to_seq_size {X : Type} {m : nat} (s : Wlist X m) : size (wlist_to_seq s) <= m.
Proof.
by induction s.
Defined.

Lemma wlist_elim {A : Type} {m : nat} : forall K : Wlist A m -> Type,
 (forall (s : seq A) (Ps : size s <= m), K (seq_to_wlist_uncut Ps)) -> forall u : Wlist A m, K u.
Proof. 
move => K Ps s. unfold seq_to_wlist_uncut in Ps. 
rewrite <- wlist_seqK. apply Ps. apply wlist_to_seq_size.
Qed.

Lemma wlist_ind {A : Type} {m : nat} : forall K : Wlist A m -> Prop,
 (forall (s : seq A) (Ps : size s <= m), K (seq_to_wlist_uncut Ps)) -> forall u : Wlist A m, K u.
Proof. 
move => K Ps s. unfold seq_to_wlist_uncut in Ps. 
rewrite <- wlist_seqK. apply Ps. apply wlist_to_seq_size.
Qed.

Lemma seq_wlist_uncut_K {A : Type} {m : nat} (s : seq A) (Ps : size s <= m) :
  wlist_to_seq (seq_to_wlist_uncut Ps) = s.
Proof.
apply (seq_wlistK Ps).
Qed.

Definition wlist_subType {A : Type} {w : nat} := 
  Eval hnf in (SubType (@Wlist A w) (@wlist_to_seq A w) seq_to_wlist_uncut wlist_elim seq_wlist_uncut_K).

Coercion wlist_to_seq_co {A : Type} {m : nat} x := @wlist_to_seq A m x.

End WlistSubType.

(** ** Wlist is a choice type *)
Section WlistChoiceType.
Variable A: choiceType.
Definition wlist0_choiceMixin := CanChoiceMixin (@cancelfg A).
Definition wlist0_choiceType := ChoiceType (wlist0_eqType A) wlist0_choiceMixin.

Fixpoint wlistn_choiceMixin (n:nat) :  Choice.mixin_of (Wlist A n).
elim n.
exact wlist0_choiceMixin.
intros n0 EC.

apply  (@CanChoiceMixin (sum_choiceType unit_choiceType (prod_choiceType A (ChoiceType (wlistn_eqType A n0) EC)  ))
                        (Wlist A n0.+1) (@ff A n0) (@gg A n0) (@cancelffgg A n0)).
Defined.

Definition wlistn_choiceType n := Eval hnf in (@ChoiceType (wlistn_eqType A n) (wlistn_choiceMixin n)).
End WlistChoiceType.

(** ** Wlist is a count type *)
Section WlistCountType.

Variable A: countType.
Definition wlist0_countMixin := CanCountMixin (@cancelfg A).
Definition wlist0_countType := CountType (wlist0_choiceType A) wlist0_countMixin.

Fixpoint wlistn_countMixin (n:nat): Countable.mixin_of (Wlist A n).
elim n.
exact wlist0_countMixin.
intros n0 EN.

apply (@CanCountMixin
           (sum_countType unit_countType (prod_countType A (CountType (wlistn_choiceType A n0) EN)  ))
           _ (@ff A n0) (@gg A n0) (@cancelffgg A n0)).
Defined.

Definition wlistn_countType n := Eval hnf in (@CountType (wlistn_choiceType A n) (wlistn_countMixin n)).

Lemma cteq: wlistn_countType 0 = wlist0_countType.
Proof.
compute. trivial.
Qed.

End WlistCountType.

(** ** Wlist is a finite type *)
Section WlistFinType.

Variable A: finType.

Definition wlist0_finMixin := @CanFinMixin (wlist0_countType A) unit_finType (@f A) (@g A) (@cancelfg A).
Definition wlist0_finType := FinType (wlist0_countType A) wlist0_finMixin.

Fixpoint wlistn_finMixin (n:nat): Finite.mixin_of (wlistn_countType A n).
elim n.
rewrite cteq.
exact wlist0_finMixin.
intros n0 EF.
apply (@CanFinMixin
           (wlistn_countType A n0.+1)
           (sum_finType unit_finType (prod_finType A (FinType (wlistn_countType A n0) EF)  ))
           (@ff A n0) (@gg A n0) (@cancelffgg A n0)).
Defined.

Definition wlistn_finType n := Eval hnf in (@FinType (wlistn_choiceType A n) (wlistn_finMixin n)).
End WlistFinType.

(** ** Utility lemmas and definitions for Wlist *)
Section WlistUtils.

Fixpoint wsize {X : Type} {m : nat} (t : Wlist X m) : nat := match t with
  | Bnil _ => 0
  | Bcons _ a b => (wsize b).+1 end.

Fixpoint wmap {X Y : Type} {m : nat} (f : X -> Y) (t : Wlist X m) : Wlist Y m := match t with
  | Bnil a => Bnil Y a
  | Bcons n a b => Bcons (f a) (@wmap X Y _ f b) end.

Lemma size_wmap {X Y : Type} {m : nat} : forall (f : X -> Y) (s : Wlist X m), 
  wsize (wmap f s) = wsize s.
Proof.
by induction s ; [ | simpl ; auto].
Defined.

Lemma wmapcoK {X Y : Type} {m : nat} (f : X -> Y) (t : Wlist X m) : wlist_to_seq_co (wmap f t) = map f (wlist_to_seq_co t).
Proof.
by induction t => /= ; [|apply/f_equal].
Qed.

Lemma wmapK {X Y : Type} {m : nat} (f : X -> Y) (t : Wlist X m) : wlist_to_seq (wmap f t) = map f (wlist_to_seq t).
Proof.
by induction t => /= ; [|apply/f_equal].
Qed.

Fixpoint w_subtype {X : Type} {n : nat} (m : nat) (l : Wlist X n) : Wlist X (n+m) := match l with
  | Bnil n => Bnil X (n+m)
  | Bcons _ a b => Bcons a (w_subtype m b) end.

Fixpoint wapp {X : Type} {n m : nat} (l : Wlist X n) (ll : Wlist X m) : Wlist X (n+m)
 := match l with
  | Bnil n => eq_rect_r (Wlist X) ((w_subtype n ll)) (addnC n m)
  | Bcons _ a b => Bcons a (wapp b ll) end.

Fixpoint wall {X : Type} {m : nat} (P : X -> bool) (s : Wlist X m) : bool := match s with  
  | Bnil _ => true
  | Bcons _ a b => (P a) && (wall P b) end.

Lemma wall_allK {A : Type} {w : nat} {l : Wlist A w} {P : pred A} : wall P l = all P (wlist_to_seq l).
Proof.
by induction l ; [ | apply andb_id2l].
Qed.

Lemma wall_to_all {A : Type} {w : nat} {l : Wlist A w} {P : pred A} : wall P l -> all P (wlist_to_seq l).
Proof.
by rewrite wall_allK.
Qed.

Definition w_all_prop (T : Type) (a : T -> Prop) :=
fix all {w : nat} (s : Wlist T w) : Prop := 
  match s with
  | Bnil _ => True
  | Bcons n x s' => a x /\ all n s'
  end.

(*Coercion wlist_to_seq : (Wlist X m) >-> seq X.*)

Fixpoint tuple_to_wlist {X : Type} {n : nat} (t : n.-tuple X) : Wlist X n.
destruct t.
move:n i.
induction tval.
  - move => n i ; simpl in i. assert(0 = n). apply/eqP/i. rewrite <- H. apply Bnil.
  - move => n i. simpl in i. assert((size tval).+1 = n). apply/eqP/i. destruct n.
    inversion H.
    inversion H.
    assert (size tval == n). apply/eqP/H1.
    rewrite H1.
    apply (Bcons a (IHtval n H0)).
Defined.

Lemma wmap_nil {X Y : Type} {n : nat} (f : X -> Y) (l : Wlist X n): 
  map f (wlist_to_seq_co l) = [::] -> l = Bnil X n.
Proof.
by destruct l.
Qed.

End WlistUtils.

End Wlist.