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

Require Import syntax.
Require Import subs.
Require Import pmatch.
Require Import bSemantics.
Require Import monotonicity.
Require Import soundness.

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset bigop finfun.

Require Import bigop_aux.
Require Import utils.
Require Import finseqs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Implicit Types (s r : sub) (d def : syntax.constant) (a : atom)
               (ga : gatom) (tl : list atom) (cl : clause) (i : interp).

Section Dtypes.

Variable p : program.

Section t_occ.

(** * Occurrences *)
(** [occ] is a pair representing a position in
   a program. (occ x y) is the yth atom in the
   body of the xth clause of the program *)
Definition occ := ('I_(size p) * 'I_bn)%type.

(** Getting atom at occurrence o *)
Definition pat (p : program) (o : occ) : option atom := match nth_error p (fst o) with
  | None => None
  | Some (Clause _ l) => nth_error l (snd o) end.

(** term occurrence is a triple made of a clause
 position in the program, atom position in the body of the clause and term position in the atom *)
Record t_occ := T_occ {r_ind : 'I_(size p) ; b_ind : 'I_bn ; t_ind : 'I_max_ar}.

(** Extract the atom occurence from the term occurence*)
Definition pred_occ (t : t_occ) := (r_ind t, b_ind t).

(** Type for the representation of [t_occ]*)
Definition tocc_countprod := prod_countType (prod_countType (ordinal_countType (size p)) (ordinal_countType bn)) (ordinal_countType max_ar).

(** Representation and cancellation lemma for [t_occ] *)
Definition t_occ_rep (a : t_occ) : tocc_countprod :=
  let: T_occ b c d := a in (b,c,d).
Definition t_occ_pre (a : tocc_countprod) :=
  let: (b,c,d) := a in T_occ b c d.

Lemma prod_of_t_occK : cancel t_occ_rep t_occ_pre.
Proof.
by case.
Qed.

(** [t_occ] is a finite type *)
Definition t_occ_eqMixin :=
  CanEqMixin prod_of_t_occK.
Canonical t_occ_eqType :=
  Eval hnf in EqType t_occ t_occ_eqMixin.
Definition t_occ_choiceMixin :=
  CanChoiceMixin prod_of_t_occK.
Canonical t_occ_choiceType :=
  Eval hnf in ChoiceType t_occ t_occ_choiceMixin.
Definition t_occ_countMixin :=
  (@CanCountMixin tocc_countprod _ t_occ_rep t_occ_pre prod_of_t_occK).
Canonical t_occ_countType :=
  Eval hnf in CountType t_occ t_occ_countMixin.
Definition t_occ_finMixin :=
  CanFinMixin prod_of_t_occK.
Canonical t_occ_finType :=
  Eval hnf in FinType t_occ t_occ_finMixin.

(** Access the atom from a t_occ and a program *)
Definition at_at (o : t_occ) : option atom :=
  match nth_error p (r_ind o) with
    | None => None
    | Some cl => nth_error (body_cl cl) (b_ind o) end.

(** Access the term from a t_occ and a program *)
Definition t_at (o : t_occ) : option term.
destruct (at_at o).
- destruct o as [x y z].
  apply (nth_error (arg_atom a) z).
- apply None.
Defined.

(** Access the predicate of the atom from a t_occ
  and a program *)
Definition p_at (t : t_occ) := match (at_at t) with
  | None => None
  | Some ato => Some (sym_atom ato) end.

(** If [t_at] givves back a variable, this is
   an actual var of a clause. *)
Lemma t_at_vars_in (tocc : t_occ) v cl :
    t_at tocc = Some (Var v)
  -> Some cl = nth_error p (r_ind tocc)
  -> v \in tail_vars (body_cl cl).
Proof.
unfold tail_vars.
move => Htat Heq. apply/bigcup_seqP.
unfold t_at in Htat.
unfold at_at in Htat. rewrite -Heq in Htat.
assert (Haex : exists a, nth_error (body_cl cl) (b_ind tocc) = Some a).
destruct (nth_error (body_cl cl) (b_ind tocc)) as [a|] ; [|inversion Htat].
by exists a.
destruct Haex as [a Ha].
rewrite Ha in Htat.
exists a.
apply (nth_error_in Ha).
apply/andP ; split ; [|trivial].
apply/bigcup_seqP ; exists (Var v) ; [|apply/andP ; split ; by [|apply/set1P|]].
destruct tocc. apply (nth_error_in Htat).
Qed.

End t_occ.

(** * Types *)
(** A branch is a sequence without repetition of [t_occ] *)
Definition dbranch := (@uniq_seq_finType t_occ_finType).

(** A conjunction is just a set of branches *)
Definition conj_dbranch := {set dbranch}.

(** And a disjunction is a set of conjunction *)
Definition disj_conj_dbranch := {set conj_dbranch}.

(** types used in the analysis. It is either a
 [disj_conj_dbranch] or an added top element *)
Inductive Dtype :=
 | Triv (* Top type: no information carried *)
 | Tr of disj_conj_dbranch (* Actual type, \/-/\-Tree (see paper) *).

Definition dt_get_dcb (t : Dtype) := match t with
  | Triv => set0
  | Tr s => s end.

(** Boolean equality on type *)
Definition Dtype_eq (x y : Dtype) := match x,y with
  | Triv,Tr t | Tr t,Triv => false
  | Triv,Triv => true
  | Tr t1, Tr t2 => t1 == t2 end.

(** it is reflexive *)
Lemma Dtype_eq_refl (x : Dtype) : Dtype_eq x x = true.
Proof.
case x=> // => d /= ; apply/eq_refl.
Qed.

(** It is indeed an equality *)
Lemma Dtype_eq_axiom : Equality.axiom Dtype_eq.
Proof.
case ; case.
 apply Bool.iff_reflect ; move=>//.
 move=>d /= ; apply/Bool.iff_reflect;move=> //.
 move => f y ; apply/Bool.iff_reflect; move=>// ; split.
  move => d. rewrite d. apply Dtype_eq_refl.
  move => // H. destruct y ; inversion H. apply/f_equal/eqP/H1.
Qed.

(** Dtype is an equality type *)
Definition Dtype_eqMixin := EqMixin Dtype_eq_axiom.

Canonical Dtype_eqType := Eval hnf in EqType Dtype Dtype_eqMixin.

(** Checks that a t_occ does not appear in a conjunction  *)
Definition dnotin_conj (al : t_occ) (t : conj_dbranch) :=
  [forall b in t, al \notin useq b].

(** Checks that a t_occ does not appear in a type *)
Definition dnotin (al : t_occ) (t : Dtype) := match t with
  | Triv => true
  | Tr dtree => [forall ct in dtree, dnotin_conj al ct] end.

 (* USELESS Checks if one of the branch is empty in the type 
Definition has_empty_branch (t : Dtype) := match t with
  | Triv => false
  | Tr dtree => [exists ct in dtree, exists br in (pred_of_set ct),
                      val br == [::]] end.
*)

(** ** Subtyping *)
(** Subtyping relation for Conj. Reflexiviy,
    and ability to remove paths in the Conj. *)
Inductive conj_subtype : conj_dbranch -> conj_dbranch -> Prop :=
  | csub_refl : forall (c : conj_dbranch) , conj_subtype c c
  | csub_rec  : forall (c1 c2 : conj_dbranch) (br : dbranch), 
                  conj_subtype c1 c2 ->
                  conj_subtype (br |: c1) c2.

(** Subtyping relation for Disj. Reflexivity,
    and pairwise subtyping on Conjs. *)
Inductive disj_subtype : disj_conj_dbranch -> disj_conj_dbranch -> Prop :=
  | dsub_refl : forall (d : disj_conj_dbranch) , disj_subtype d d
  | dsub_rec  : forall (d1 d2 : disj_conj_dbranch)
                       (c1 c2 : conj_dbranch), 
                          conj_subtype c1 c2 ->
                          disj_subtype d1 d2 ->
                          disj_subtype (c1 |: d1) (c2 |: d2).

(** General subtyping relation. Everything is
    smaller than Top, using [disj_subtype] otherwise *)
Inductive subtype : Dtype -> Dtype -> Prop :=
  | sub_disj : forall (d1 d2 : disj_conj_dbranch), 
                  disj_subtype d1 d2 -> subtype (Tr d1) (Tr d2)
  | sub_top  : forall t : Dtype, subtype t Triv.

(** Only a Disj can be smaller than a Disj *)
Lemma subtype_Tr (t : Dtype) (d : disj_conj_dbranch) :
  subtype t (Tr d) -> exists (d' : disj_conj_dbranch), 
                        t = Tr d' /\ disj_subtype d' d.
Proof.
move=>H. inversion H as [d1 d2 Hsub H0 H1|]. exists d1;split.
reflexivity. apply Hsub.
Qed.

(** Boolean view of [conj_subtype] *)
Lemma csub_subset (c1 c2 : conj_dbranch) :
  conj_subtype c1 c2 -> c2 \subset c1.
Proof.
move=>H. induction H as [|c1 c2 br Hsub]. auto.
apply (subset_trans IHHsub). apply subsetUr.
Qed.

(** [disj_subtype] is subset modulo [conj_subtype] *)
Lemma dsub_subset (d1 d2 : disj_conj_dbranch) : 
  disj_subtype d1 d2 -> forall c1, c1 \in d1
  -> exists c2, c2 \in d2 /\ conj_subtype c1 c2.
Proof.
move=>H. induction H as [|d1 d2 c1 c2 Hcsub Hdsub].
- move=>c1 Hc1.
  exists c1. split. apply Hc1. apply csub_refl.
- move=>c3 /setU1P [->|Hc3].
  + exists c2. split.
    by apply/setU1P;left. apply Hcsub.
  + destruct (IHHdsub c3 Hc3)
      as [c4 [H1 H2]].
    exists c4. split. 
    by apply/setU1P; right. apply H2.
Qed.
Lemma dsub_subset_rev (d1 d2 : disj_conj_dbranch) : 
  disj_subtype d1 d2 -> forall c2, c2 \in d2
  -> exists c1, c1 \in d1 /\ conj_subtype c1 c2.
Proof.
move=>H. induction H as [|d1 d2 c1 c2 Hcsub Hdsub].
- move=>c1 Hc1.
  exists c1. split. apply Hc1. apply csub_refl.
- move=>c3 /setU1P [->|Hc3].
  + exists c1. split.
    by apply/setU1P;left. apply Hcsub.
  + destruct (IHHdsub c3 Hc3)
      as [c4 [H1 H2]].
    exists c4. split. 
    by apply/setU1P; right. apply H2.
Qed.

(** Lifitng [dsub_subset] and [dsub_subset_rev]
   to subtype and dt_get_dcb *)
Lemma dt_get_dcb_subtype (t1 t2 : Dtype) c1 :
   subtype t1 t2 -> c1 \in dt_get_dcb t1 -> [exists t, t2 == Tr t]
-> exists c2, c2 \in dt_get_dcb t2 /\ conj_subtype c1 c2.
Proof.
move=>H H1 H2.
destruct t2 as [|t2].
inversion H. destruct (existsP H2) as [f Hf].
have Hff := eqP Hf. inversion Hff.
destruct (subtype_Tr H) as [d [Hd1 Hd2]].
apply (dsub_subset Hd2). by rewrite Hd1 in H1.
Qed.
Lemma dt_get_dcb_subtype_rev (t1 t2 : Dtype) c2 :
   subtype t1 t2 -> c2 \in dt_get_dcb t2 -> [exists t, t2 == Tr t]
-> exists c1, c1 \in dt_get_dcb t1 /\ conj_subtype c1 c2.
Proof.
move=>H H1 H2.
destruct t2 as [|t2].
inversion H. destruct (existsP H2) as [f Hf].
have Hff := eqP Hf. inversion Hff.
destruct (subtype_Tr H) as [d [Hd1 Hd2]].
rewrite Hd1.
apply (dsub_subset_rev Hd2 H1).
Qed.

(** * Actual constructors for types *)
(** ** Init type *)
Definition tInit := Tr([set [set unil ]]).

(** Adds a t_occ at the head of all branches of a 
  conjunction. This requires a proof that the
  t_occ did not already appear in some of the branch
  *)

(** ** Insertion of an occurrence in the branches *)
Definition tInsert_conj (al : t_occ) (t : conj_dbranch)
  (H : [forall b in t, al \notin (useq b)]) :=
  let dt := equip _ t in
  [set (ucons (implyP ((forallP H) (proj1_sig db)) (proj2_sig db))) | db in dt].

(** Adds a t_occ at the head of all branches of a 
  type. This requires a proof that the
  t_occ did not already appear in some of the branch
  *)
Definition tInsert_disj_conj (al : t_occ) (t : disj_conj_dbranch)
  (H : [forall ct in t, [forall b in pred_of_set ct, al \notin (useq b)]]) :=
  let dt := equip _ t in
  Tr [set (tInsert_conj (implyP ((forallP H) (proj1_sig ct)) (proj2_sig ct))) | ct in dt].

(** Checks that a conjunction is in a type *)
Definition Din (ct : conj_dbranch) (t : Dtype) := match t with
  | Triv => false
  | Tr dt => ct \in dt end.

(** Checks that a t_occ not in a type *)
Definition notInT al t := 
  [forall ct : conj_dbranch, 
    Din ct t ==> [forall b in ct, al \notin (useq b)]].

(** Insert a t_occ at the head of a type *)
Definition tInsert (al : t_occ) (t : Dtype) :=
  match t as d return (notInT al d -> Dtype) with
    | Triv => fun _ => Triv
    | Tr s => @tInsert_disj_conj al s end.

(** ** Computing disjunction and conjunction of types *)
(** Disjunction of types *)
Definition tDisj t t2 := match t,t2 with
  | Triv,_ | _,Triv => Triv
  | Tr t, Tr t2 => Tr (t :|: t2) end.

(** Conjunction of types. We forget Triv. We must
   build a cross product for regular types. *)
Definition tConj t t2 := match t,t2 with
  | Triv,_ => t2
  | _,Triv => t
  | Tr t, Tr t2 => Tr [set (a :|: b) | a in t, b in t2 ] end.

(** There is no t_occ in tInit *)
Lemma not_in_init (s : {set t_occ}) : [forall x in s, dnotin x (tInit)].
Proof.
apply/forallP=>x. apply/implyP=>Hx.
apply/forallP=>y. apply/implyP=>/set1P ->.
apply/forallP=>z. by apply/implyP=>/set1P ->.
Qed.

(** * Utility lemmas proving we have real branches in our types *)
Section Notinit.

(** An insertion that succeeds does not gives back [tInit] *)
Lemma tInsert_not_init (al : t_occ) (t : Dtype) (Hal : notInT al t) :
   tInsert Hal <> tInit.
move => Hfalse.
destruct t as [|t]. inversion Hfalse.
unfold tInit in Hfalse. unfold tInsert in Hfalse.
unfold tInsert_disj_conj in Hfalse. inversion Hfalse.
move:H0. move => /eqP. rewrite eqEsubset.
move => /andP [/subsetP Hsub1 /subsetP Hsub2].
assert (Hindt : [set (@unil (t_occ_finType))] \in [set [set unil]]). apply/set11.
destruct (imsetP (Hsub2 [set unil] Hindt)) as [x Hxint Hxeq].
unfold tInsert_conj in Hxeq.
move:Hxeq. move => /eqP. rewrite eqEsubset.
move => /andP [/subsetP Hssub1 /subsetP Hssub2].
destruct (imsetP (Hssub1 unil (set11 unil))) as [y Hyin Hyeq].
inversion Hyeq.
Qed.

(** If a non top type is not tInit, it is either
   the degenerate case Tr set0, or it contains
   a non empty branch. *)
Lemma tnotinit_notdisj t : Tr t <> tInit ->
  t = set0 \/ [exists x in t, x != [set unil]].
Proof.

destruct (set_0Vmem t) as [Hset0|[x Hx]];move=>H.
by left.
right.
destruct (bool_des_rew (x == [set unil])) as [Heq|Hneq].
destruct (bool_des_rew ([exists x0 in t, x0 != [set unil]]))
  as [Hseq|Hsneq].
apply Hseq.
exfalso. apply H. apply/f_equal/eqP.
rewrite eqEsubset. apply/andP;split;apply/subsetP;move=>y.
assert (Hneqb: ~~ [exists x0 in t, x0 != [set unil]]).
by rewrite Hsneq.
rewrite negb_exists in Hneqb.
pose Hb := (forallP Hneqb y). clearbody Hb.
rewrite negb_and in Hb. destruct (orP Hb) as [Hf|Hf].
move=>Hi. rewrite Hi in Hf. inversion Hf.
move=>Hi. apply/set1P. unfold negb in Hf. apply/eqP.
destruct (bool_des_rew (y == [set unil])) as [Hy|Hy].
apply Hy. by rewrite Hy in Hf.
move=>/set1P ->. by rewrite (eqP Heq) in Hx.
apply/existsP. exists x. apply/andP;split.
apply Hx. unfold negb. by rewrite Hneq.
Qed.

(** A disjunction of two types that where not tInit
  is not [tInit] *)
Lemma tDisj_not_init (t1 t2: Dtype) :
  t1 <> tInit-> t2 <> tInit -> tDisj t1 t2 <> tInit.
Proof.
unfold tInit.
unfold tDisj.
destruct t1 as [|t1];destruct t2 as [|t2];move=>//.
move=>/tnotinit_notdisj [H1s0|H1ns0] /tnotinit_notdisj [H2s0|H2ns0];
rewrite ?H1s0 ?H2s0 ?set0U ?setU0;move=>Hf;inversion Hf as [Hff];
move:Hff;move=>/eqP; rewrite eqEsubset;move=>/andP [Hs1 Hs2].
assert (Hff : [set @unil t_occ_finType] \in set0).
apply (subsetP Hs2 [set unil]). by apply/set1P.
by rewrite in_set0 in Hff.
destruct (existsP H2ns0) as [x Hx].
destruct (andP Hx) as [Hxin Hxneq].
by rewrite (set1P (subsetP Hs1 x Hxin)) (eq_refl _) in Hxneq.
destruct (existsP H1ns0) as [x Hx].
destruct (andP Hx) as [Hxin Hxneq].
by rewrite (set1P (subsetP Hs1 x Hxin)) (eq_refl _) in Hxneq.
destruct (existsP H1ns0) as [x Hx].
destruct (andP Hx) as [Hxin Hxneq].
assert (Hxinb : x \in (t1 :|: t2)). by apply/setUP;left.
by rewrite (set1P (subsetP Hs1 x Hxinb)) (eq_refl _) in Hxneq.
Qed.

(** Conjunction of two not init is not an init *)
Lemma tConj_not_init (t1 t2: Dtype) :
  t1 <> tInit-> t2 <> tInit -> tConj t1 t2 <> tInit.
Proof.
unfold tInit. unfold tConj.
destruct t1 as [|t1] ; destruct t2 as [|t2];
move => // Ht1g Ht2g Htrfalse;
inversion Htrfalse as [Hfalse] ; clear Htrfalse.
move:Hfalse. move => /eqP. rewrite eqEsubset.
move=>/andP [/subsetP Hf1 /subsetP Hf2].
destruct (imset2P (Hf2 [set unil] (set11 [set unil]))) as [cb1 cb2 Hcb1 Hcb2 Hcb12eq].
assert (Hx1unil : {subset (pred_sort_of_fin cb1) <= [set unil]}).
move => x Hx. assert (HxinUP : x \in cb1 :|: cb2). by apply/setUP ; left.
by rewrite Hcb12eq.
assert (Hx2unil : {subset (pred_sort_of_fin cb2) <= [set unil]}).
move => x Hx. assert (HxinUP : x \in cb1 :|: cb2). by apply/setUP ; right.
by rewrite Hcb12eq.

 (* 3 cases :
     - cb1 = cb2 = [set unil] (will appear twice)
     - cb1 = [set unil] ; cb2 = set0
     - cb1 = set0 ; cb2 = [set unil] *)

 (* TODO: factorize *)
assert (Hucb12 : unil \in (cb1 :|: cb2)). rewrite -Hcb12eq. apply/set11.
destruct (setUP Hucb12) as [Hucb1 | Hucb2].
 (* cb1 = [set unil] *)
assert (Hcb1unil : cb1 = [set unil]).
apply/eqP. rewrite eqEsubset. apply/andP ; split ;
apply/subsetP ; move => x Hx.
by apply Hx1unil.
by rewrite (set1P Hx).

- destruct (@Bool.bool_dec (unil \in (pred_sort_of_fin cb2)) true) as [Hucb2 | Hncb2].
  (* cb1 = cb2 = [set unil] *)
  + assert (Hcb2unil : cb2 = [set unil]).
    apply/eqP. rewrite eqEsubset. apply/andP ; split ;
    apply/subsetP ; move => x Hx.
    by apply Hx2unil.
    by rewrite (set1P Hx).
    assert (Hexcb1 : [exists cb1' in t1, (cb1' != cb1)]).
    rewrite -negb_forall_in. apply/negP. move => Hf.
    apply/Ht1g/f_equal/eqP. rewrite eqEsubset ; apply/andP ; split ;
    apply/subsetP ; move => y Hy.
    - rewrite (eqP (implyP (forallP Hf y) Hy)) Hcb1unil. apply/set11.
    - by rewrite (set1P Hy) -Hcb1unil.
    destruct (existsP Hexcb1) as [cb1' Hcb1']. clear Hexcb1.
    destruct (andP Hcb1') as [Hcb1bin Hcb1neq]. clear Hcb1'.
    rewrite Hcb1unil in Hcb1neq.
    move:Hcb1neq. move => /not_set1P/orP [Hcb1set0|Hcb1bnotnunil].
    (* cb1' = set0 *)
    - apply/Ht2g/f_equal/eqP. rewrite eqEsubset.
      apply/andP ; split ; apply/subsetP ; move => x Hx.
      apply/Hf1/imset2P. exists cb1' cb2 ; auto.
      rewrite (eqP Hcb1set0) set0U Hcb2unil.
      apply/set1P/Hf1/imset2P. exists cb1' x; auto.
      by rewrite (eqP Hcb1set0) set0U.
      by rewrite (set1P Hx) -Hcb2unil.
    (* (x != unil) \in cb1' *)
    - destruct (existsP Hcb1bnotnunil) as [y Hy]. clear Hcb1bnotnunil.
      destruct (andP Hy) as [Hyincb1b Hynotunil]. clear Hy.
      assert (Hff : cb1' :|: [set unil] \in [set [set unil]]). apply Hf1.
      apply/imset2P. exists cb1' [set unil] ; rewrite Hcb2unil in Hcb2 ; auto.
      pose Hfff := (set1P Hff). move:Hfff. move=>/eqP. rewrite eqEsubset.
      move=> /andP [/subsetP Hcb1bunilin Hunilsub].
      assert (HyinUP : y \in cb1' :|: [set unil]). by apply/setUP ; left.
      rewrite (set1P (Hcb1bunilin _ HyinUP)) in Hynotunil.
      by apply (negP Hynotunil).
  (* cb1 = [set unil] ; cb2 = set0 *)
  + assert (Hcb20 : cb2 = set0).
    apply/eqP. rewrite eqEsubset. apply/andP ; split ;
    apply/subsetP ; move => y Hy.
    by rewrite -(set1P (Hx2unil y Hy)) Hy in Hncb2.
    by rewrite in_set0 in Hy.
    apply/Ht1g/f_equal/eqP. rewrite eqEsubset.
    apply/andP ; split ; apply/subsetP ; move => x Hx.
    apply/Hf1/imset2P. exists x cb2 ; auto.
    by rewrite Hcb20 setU0.
    rewrite (set1P Hx). by rewrite Hcb1unil in Hcb1.

(* cb2 = [set unil] *)
assert (Hcb2unil : cb2 = [set unil]).
apply/eqP. rewrite eqEsubset. apply/andP ; split ;
apply/subsetP ; move => x Hx.
by apply Hx2unil.
by rewrite (set1P Hx).

- destruct (@Bool.bool_dec (unil \in (pred_sort_of_fin cb1)) true) as [Hucb1 | Hncb1].
  (* cb1 = cb2 = [set unil] *)
  + assert (Hcb1unil : cb1 = [set unil]).
    apply/eqP. rewrite eqEsubset. apply/andP ; split ;
    apply/subsetP ; move => x Hx.
    by apply Hx1unil.
    by rewrite (set1P Hx).
    assert (Hexcb2 : [exists cb2' in t2, (cb2' != cb2)]).
    rewrite -negb_forall_in. apply/negP. move => Hf.
    apply/Ht2g/f_equal/eqP. rewrite eqEsubset ; apply/andP ; split ;
    apply/subsetP ; move => y Hy.
    - rewrite (eqP (implyP (forallP Hf y) Hy)) Hcb2unil. apply/set11.
    - by rewrite (set1P Hy) -Hcb2unil.
    destruct (existsP Hexcb2) as [cb2' Hcb2']. clear Hexcb2.
    destruct (andP Hcb2') as [Hcb2bin Hcb2neq]. clear Hcb2'.
    rewrite Hcb2unil in Hcb2neq.
    move:Hcb2neq. move => /not_set1P/orP [Hcb2set0|Hcb2bnotnunil].
    (* cb2' = set0 *)
    - apply/Ht1g/f_equal/eqP. rewrite eqEsubset.
      apply/andP ; split ; apply/subsetP ; move => x Hx.
      apply/Hf1/imset2P. exists cb1 cb2' ; auto.
      rewrite (eqP Hcb2set0) setU0 Hcb1unil.
      apply/set1P/Hf1/imset2P. exists x cb2'; auto.
      by rewrite (eqP Hcb2set0) setU0.
      by rewrite (set1P Hx) -Hcb1unil.
    (* (x != unil) \in cb2' *)
    - destruct (existsP Hcb2bnotnunil) as [y Hy]. clear Hcb2bnotnunil.
      destruct (andP Hy) as [Hyincb2b Hynotunil]. clear Hy.
      assert (Hff : [set unil] :|: cb2' \in [set [set unil]]). apply Hf1.
      apply/imset2P. exists [set unil] cb2' ; rewrite Hcb1unil in Hcb1 ; auto.
      pose Hfff := (set1P Hff). move:Hfff. move=>/eqP. rewrite eqEsubset.
      move=> /andP [/subsetP Hcb2bunilin Hunilsub].
      assert (HyinUP : y \in  [set unil] :|: cb2'). by apply/setUP ; right.
      rewrite (set1P (Hcb2bunilin _ HyinUP)) in Hynotunil.
      by apply (negP Hynotunil).
  (* cb1 = set0 ; cb2 = [set unil] *)
  + assert (Hcb10 : cb1 = set0).
    apply/eqP. rewrite eqEsubset. apply/andP ; split ;
    apply/subsetP ; move => y Hy.
    by rewrite -(set1P (Hx1unil y Hy)) Hy in Hncb1.
    by rewrite in_set0 in Hy.
    apply/Ht2g/f_equal/eqP. rewrite eqEsubset.
    apply/andP ; split ; apply/subsetP ; move => x Hx.
    apply/Hf1/imset2P. exists cb1 x ; auto.
    by rewrite Hcb10 set0U.
    rewrite (set1P Hx). by rewrite Hcb2unil in Hcb2.
Qed.

End Notinit.

End Dtypes.
