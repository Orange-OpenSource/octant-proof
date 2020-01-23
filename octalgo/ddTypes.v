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
Require Import dTypes.

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset bigop finfun.

Require Import bigop_aux.
Require Import utils.
Require Import finseqs.

Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (s r : sub) (d def : syntax.constant) (a : atom)
               (ga : gatom) (tl : list atom) (cl : clause) (i : interp).

(** Set of term occurrences for p *)
Definition tocs p := {set (t_occ p)}.

Section DDtype.

(** * DDType *)
(** ** Definition *)
(** A DDType is a DType where some term occurences cannot appear *)
Structure DDtype p (ctxt : (tocs p)) := 
  {dt :> (Dtype p) ; Hdd : [forall x in ctxt, (dnotin x dt)]}.

Canonical DDtype_subType p (ctxt : (tocs p)) := Eval hnf in [subType for (@dt p ctxt)].

(** [Triv] is a DDtype as it contains no term occurence *)
Lemma TrivDDtype : forall p (ctxt : (tocs p)), 
  [forall x in ctxt, dnotin x (Triv p)].
Proof.
by move => p ctxt ; apply/forallP ; move => x ; apply/implyP.
Qed.

(** So is the empty type *)
Lemma EmptyDDtype : forall p (ctxt : (tocs p)), 
  [forall x in ctxt, dnotin x (Tr set0)].
Proof.
move => p ctxt ; apply/forallP=>x ; apply/implyP=>Hx;
apply/forallP=>y ; apply/implyP. by rewrite in_set0.
Qed.

(** So is the init type *)
Lemma tInitDDtype : forall p (ctxt : (tocs p)), 
  [forall x in ctxt, dnotin x (tInit p)].
Proof.
move => p ctxt ; apply/forallP ; move => x ; apply/implyP ; move => H //.
apply/forallP ; move => x0.
apply/implyP ; move => H0.
rewrite (set1P H0).
apply/forallP.
move => x1 //.
apply/implyP.
move => Hx1.
by rewrite (set1P Hx1).
Qed.

(** A disjunction of DDTypes  verifies the DDType constraint *)
Lemma tDisjDDtype {p} {ctxt : (tocs p)} (t1 : (DDtype ctxt)) (t2 : (DDtype ctxt)) : 
  [forall x in ctxt, (dnotin x (tDisj (dt t1) (dt t2)))].
Proof.
destruct t1 as [t1 Ht1] ; destruct t2 as [t2 Ht2].
apply/forallP ; move => x ; apply/implyP ; move => Hx /=.
destruct t1 as [ | s].
- by destruct t2.
- destruct t2 as [ | s0].
  + auto.
  + simpl.
    apply/forallP ; move => ct ; apply/implyP ; move => Hdisj.
    simpl in Ht1 ; simpl in Ht2.
    destruct (setUP Hdisj) as [Hcts | Hcts0].
    - apply/forallP ; move => x0 ; apply/implyP ; move => Hx0.
      apply ((implyP ((forallP ((implyP ((forallP ((implyP (forallP Ht1 x)) Hx)) ct)) Hcts)) x0)) Hx0).
    - apply/forallP ; move => x0 ; apply/implyP ; move => Hx0.
      apply ((implyP ((forallP ((implyP ((forallP ((implyP (forallP Ht2 x)) Hx)) ct)) Hcts0)) x0)) Hx0).
Qed.

(** A conjunction of DDTypes verifies the DDType constraint *)
Lemma tConjDDtype {p} {ctxt : (tocs p)} (t1 : (DDtype ctxt)) (t2 : (DDtype ctxt)) : 
  [forall x in ctxt, dnotin x (tConj (dt t1) (dt t2))].
Proof.
destruct t1 as [t1 Ht1] ; destruct t2 as [t2 Ht2].
apply/forallP ; move => x ; apply/implyP ; move => Hx /=.
pose Hxt1 := implyP (forallP Ht1 x) Hx.
pose Hxt2 := implyP (forallP Ht2 x) Hx.
destruct t1 as [ | s].
- by destruct t2.
- destruct t2 as [ | s0].
  + auto.
  + simpl.
    apply/forallP=>ct;apply/implyP=>Hdisj;apply/forallP=>x0;apply/implyP=>Hxct.
    destruct (imset2P Hdisj) as [x1 x2 Hx1s Hx2s0 Hctx].
    rewrite Hctx in Hxct.
    destruct (setUP Hxct) as [Hx0x1 | Hx0x2].
    - apply (implyP (forallP (implyP ((forallP Hxt1) x1) Hx1s) x0) Hx0x1).
    - apply (implyP (forallP (implyP ((forallP Hxt2) x2) Hx2s0) x0) Hx0x2).
Qed.

(** If we instert an occurrence not in the context
  to a DDType, then the result verifies the DDType
  constraint *)
Lemma tInsertDDtype {p} {ctxt : (tocs p)} (al : (t_occ p)) (Halctxt : al \notin ctxt)
(t : (DDtype (ctxt :|: [set al])))
(H : notInT al t) :
 [forall x in ctxt, (dnotin x (@tInsert p al (dt t) H))].
Proof.
apply/forallP ; move => x ; apply/implyP ; move => Hx.
destruct t as [t Ht].
destruct t as [ |s].
- auto.
- apply/forallP=>ct;apply/implyP=> Hctin;apply/forallP=>b;apply/implyP=>Hbin.
  destruct (imsetP Hctin) as [ctb Hcts Hctconj].
  destruct ctb as [ctb Hmemctb].
  rewrite Hctconj in Hbin.
  destruct (imsetP Hbin) as [fb Hfbctb Hbconsfb].
  destruct b as [b Huniqb] ; destruct fb as [fb Hfb].
  inversion Hbconsfb as [Hbalfb].
  apply/memPnC/eqfun_inP.
  apply/forallP=>xal;apply/implyP=>/= Hxalin;apply/eqP/negP=>Habseq.
  rewrite -(eqP Habseq) Hbalfb in_cons in Hxalin.
  destruct (orP Hxalin) as [Hxal | Hxfb].
  + rewrite (eqP Hxal) in Hx. by rewrite Hx in Halctxt.
  + pose ximp := implyP (forallP Ht x).
    assert (xctxtal : x \in ctxt :|: [set al]).
    - by apply/setUP ; left.
    have Hf := (implyP (forallP (implyP (forallP (ximp xctxtal) ctb) Hmemctb) fb) Hfb).
    by rewrite Hxfb in Hf.
Qed.

(** ** Constructors for DDTypes *)
(** A DDtype from a DType and a proof it respects
  the condition *)
Definition mk_DDtype {p} {ctxt : (tocs p)} {dt : (Dtype p)} (H : [forall x in ctxt, dnotin x dt]) : (DDtype ctxt) :=
  {| dt := dt ; Hdd := H |}.

(** Construct the disjunction of DDTypes *)
Definition DtDisj {p} {ctxt : (tocs p)} (t1 : (DDtype ctxt)) (t2 : (DDtype ctxt)) : DDtype ctxt :=
  {| dt := tDisj (dt t1) (dt t2) ; Hdd := tDisjDDtype t1 t2 |}.

(** Construct the conjunction of DDTypes *)
Definition DtConj {p} {ctxt : (tocs p)} (t1 : (DDtype ctxt)) (t2 : (DDtype ctxt)) : DDtype ctxt :=
  {| dt := tConj (dt t1) (dt t2) ; Hdd := tConjDDtype t1 t2 |}.

(** Construct a DDType by insertion of a t_occ *)
Definition DtInsert {p} {ctxt : (tocs p)} {al : (t_occ p)} {t : (DDtype (ctxt :|: [set al]))} (Hal : al \notin ctxt)
(H : notInT al t) : DDtype ctxt :=
  {| dt := tInsert H ; Hdd := tInsertDDtype Hal H |}.

(** Empty DDType *)
Definition DEmpty {p} {ctxt : (tocs p)} : DDtype ctxt :=
  {| dt := Tr set0 ; Hdd := EmptyDDtype ctxt |}.

Definition fold_type_alg {p} {ctxt : (tocs p)} (op : (DDtype ctxt) -> (DDtype ctxt) -> (DDtype ctxt))
  (l: seq (DDtype ctxt)) (b : DDtype ctxt) :=
  foldr op b l.

(** Builds a conjunction of a list of DDTypes. It is
   not tInit.*)
Lemma notInitSeq {p} {ctxt : tocs p} (typs: seq (DDtype ctxt)) :
  all_prop (fun t : Dtype p => t <> tInit p)
  [seq val i | i <- typs] -> val (fold_type_alg DtConj typs (mk_DDtype (@TrivDDtype p ctxt))) <> tInit p.
Proof.
induction typs as [|a typs]=>//= [[Ha Hall]].
destruct a as [[|a] Hanotin].
apply (IHtyps Hall).
apply (tConj_not_init Ha (IHtyps Hall)).
Qed.

(** If [x] appears in [t1], it appears in [t1 \/ t2] *)
Lemma DinDisj_l p x t1 t2 : Din x (Tr t1)
                           -> Din x (@tDisj p (Tr t1) (Tr t2)).
Proof. move => /= H. apply/setUP. by left.
Qed.

(** If [x] appears in [t2], it appears in [t1 \/ t2] *)
Lemma DinDisj_r p x t1 t2 : Din x (Tr t2)
                           -> Din x (@tDisj p (Tr t1) (Tr t2)).
Proof. move => /= H. apply/setUP. by right.
Qed.

(** If [x] does not appears in [t1 \/ t2], it 
  does not appear in [t1] *)
Lemma notInTDisj_l p al t1 t2 : notInT al (@tDisj p (Tr t1) (Tr t2))
                        -> notInT al (Tr t1).
Proof.
move => /forallP Hprev.
apply/forallP. move => x. apply/implyP. move => HDin1.
apply/forallP. move => br. apply/implyP. move => HDin2.
apply ((implyP ((forallP ((implyP (Hprev x)) (@DinDisj_l p x t1 t2 HDin1))) br)) HDin2).
Qed.

(** If [x] does not appears in [t1 \/ t2], it 
  does not appear in [t2] *)
Lemma notInTDisj_r p al t1 t2 : notInT al (@tDisj p (Tr t1) (Tr t2))
                        -> notInT al (Tr t2).
Proof.
move => /forallP Hprev.
apply/forallP. move => x. apply/implyP. move => HDin1.
apply/forallP. move => br. apply/implyP. move => HDin2.
apply ((implyP ((forallP ((implyP (Hprev x)) (@DinDisj_r p x t1 t2 HDin1))) br)) HDin2).
Qed.

(** If [al] does not appear in folding disjunction 
  over a list of DDTypes, then it does not appear
  in any DDType *)
Lemma notInTDisj_fold p (ct : tocs p) al t (tl : seq (DDtype ct)) :
                       val (fold_type_alg DtDisj tl DEmpty) <> Triv p ->
                      notInT al (fold_type_alg DtDisj tl DEmpty)
                      -> t \in map val tl -> notInT al t.
Proof.
induction tl as [|h tl Hl].
by rewrite in_nil.
rewrite in_cons. move=>Ht H /orP [/eqP Hh|Hrec].
rewrite Hh. simpl in H.
destruct h as [[|h]]. simpl in *. apply/forallP=>x. by apply/implyP.
move:Ht H. simpl.
destruct (fold_type_alg DtDisj tl DEmpty) as [[|]]; move=>/=Hf.
exfalso. by apply Hf.
move=>Hn. apply/forallP=>x. apply/implyP=>Hx.
apply (implyP (forallP Hn x)).
apply/setUP;left. apply Hx.
assert (Htb : val (fold_type_alg DtDisj tl DEmpty) <> Triv p).
simpl in Ht. move:Ht.
unfold tDisj. destruct h as [[|h]]; move=>//=.
destruct (fold_type_alg DtDisj tl DEmpty) as [[|]].
move=>//. move=>/=Hv Hf. inversion Hf.
assert (val h <> Triv p).
move:Ht. simpl. destruct h as [[|]]; move=>//.
apply Hl. apply Htb.
move:H Htb. simpl.
destruct h as [[|]];destruct (fold_type_alg DtDisj tl DEmpty) as [[|]];
move=>//= Hn Hf.
apply (notInTDisj_r Hn).
apply Hrec.
Qed.

(** Insert commutes with tDisj *)
Lemma tInsert_Disj_comm p al t1 t2 (H : notInT al (tDisj (Tr t1) (Tr t2))) :
          tInsert H = @tDisj p (tInsert (notInTDisj_l H)) (tInsert (notInTDisj_r H)).
Proof.
simpl. unfold tInsert_disj_conj. apply/f_equal.
apply/eqP. rewrite eqEsubset. apply/andP. split ; apply/subsetP ; move => /= x Hx.
- destruct (imsetP Hx) as [y Hyeq Hyins].
  rewrite in_set mem_pmap in Hyeq.
  destruct (mapP Hyeq) as [z Hzin Hzins].
  rewrite mem_enum in Hzin.
  destruct (setUP Hzin) as [Hzt|Hzt] ; apply/setUP ; [left|right] ; apply/imsetP ; exists (exist _ z Hzt).
  + rewrite in_set mem_pmap. apply/mapP. exists z.
    - by rewrite mem_enum.
    - unfold insub.
      destruct idP as [|Hf].
      + apply/f_equal/f_equal/Eqdep_dec_bool.
      + exfalso. apply/Hf/Hzt.
  + rewrite Hyins. simpl.
    unfold insub in Hzins. destruct idP as [|Hf] in Hzins.
    - inversion Hzins.
      + by rewrite (@Eqdep_dec_bool _ (implyP (forallP H z) i) (implyP (forallP (notInTDisj_l H) z) Hzt)).
      + exfalso. apply/Hf/setUP. by left.

  + rewrite in_set mem_pmap. apply/mapP. exists z.
    - by rewrite mem_enum.
    - unfold insub.
      destruct idP as [|Hf].
      + apply/f_equal/f_equal/Eqdep_dec_bool.
      + exfalso. apply/Hf/Hzt.
  + rewrite Hyins. simpl.
    unfold insub in Hzins. destruct idP as [|Hf] in Hzins.
    - inversion Hzins.                                                          (* diff is here (_r) *)
      + by rewrite (@Eqdep_dec_bool _ (implyP (forallP H z) i) (implyP (forallP (notInTDisj_r H) z) Hzt)).
      + exfalso. apply/Hf/setUP. by left.

- destruct (setUP Hx) as [Hxb|Hxb] ; destruct (imsetP Hxb) as [[y Ht] Hyeq Hyins] ;
  apply/imsetP ; assert (Hyint1t2 : y \in (t1 :|: t2)) ;
  [apply/setUP ; by left | exists (@exist _ _ y Hyint1t2) | apply/setUP ; by right | exists (@exist _ _ y Hyint1t2)].
  + rewrite in_set mem_pmap. apply/mapP. exists y.
    - by rewrite mem_enum.
    - simpl. unfold insub. destruct idP as [|Hf].
      + apply/f_equal/f_equal/Eqdep_dec_bool.
      + exfalso. by apply Hf.
  + by rewrite Hyins (@Eqdep_dec_bool _ (implyP (forallP (notInTDisj_l H) y) Ht) (implyP (forallP H y) Hyint1t2)).
  + rewrite in_set mem_pmap. apply/mapP. exists y.
    - by rewrite mem_enum.
    - simpl. unfold insub. destruct idP as [|Hf].
      + apply/f_equal/f_equal/Eqdep_dec_bool.
      + exfalso. by apply Hf.
  + by rewrite Hyins (@Eqdep_dec_bool _ (implyP (forallP (notInTDisj_r H) y) Ht) (implyP (forallP H y) Hyint1t2)).
Qed.

(** An induction principle to prove properties on
   conjunctions of DDtypes. *)
Lemma fold_type_alg_conj {p ctxt} (P : Dtype p -> Prop) (Htriv : P (Triv p))
  (Hconj : forall t1 t2 : Dtype p, P t1 -> P t2 -> P (tConj t1 t2))
  (s : seq (DDtype ctxt)) (Hall : all_prop P (map val s)) : P (fold_type_alg DtConj s (mk_DDtype (@TrivDDtype p ctxt))).
Proof.
induction s ; [apply Htriv|].
unfold fold_type_alg. simpl. destruct Hall as [Ha Hall]. apply/Hconj. apply Ha. apply/IHs/Hall.
Qed.

(** ** enotin - Occurence not in a context *)
(** A structure to keep the fact that an element is 
   not in a given context *)
Structure enotin {p} (ctxt : (tocs p)) := {elnotin :> (t_occ_finType p) ; Helnotin : elnotin \notin ctxt}.

Canonical enotin_subType {p} (ctxt : (tocs p)) := Eval hnf in [subType for (@elnotin p ctxt)].
Canonical enotin_eqType {p} (ctxt : (tocs p)) := Eval hnf in EqType (@enotin p ctxt) [eqMixin of (@enotin p ctxt) by <:].
Canonical enotin_choiceType {p} (ctxt : (tocs p)) := Eval hnf in ChoiceType (@enotin p ctxt) [choiceMixin of (@enotin p ctxt) by <:].
Canonical enotin_countType {p} (ctxt : (tocs p)) := Eval hnf in CountType (@enotin p ctxt) [countMixin of (@enotin p ctxt) by <:].
Canonical enotin_subCountType {p} (ctxt : (tocs p)) := Eval hnf in [subCountType of (@enotin p ctxt)].
Canonical enotin_finType {p} (ctxt : (tocs p)) := Eval hnf in FinType (@enotin p ctxt) [finMixin of (@enotin p ctxt) by <:].
Canonical enotin_subFinType {p} (ctxt : (tocs p)) := Eval hnf in [subFinType of (@enotin p ctxt)].

Canonical enotin_option_fsfType {p} (ctxt : (tocs p)) :=
  Eval hnf in option_finType (@enotin_subFinType p ctxt).

Coercion enotin_option_fin {p} (ctxt : (tocs p)) (x : option (@enotin p ctxt))
  : @enotin_option_fsfType p ctxt := x.

(** Given [l] and [s] sets of t_occs, gives back as
   (enotin ns) the t_occs of [l] not in [ns] *)
Definition seq_to_enotin {p} (l : tocs p) (ns : (tocs p)) : {set (enotin ns)} :=
pset [set enotin_option_fin (insub x) | x in l].

(** If [l] is empty, so is the result *)
Lemma seqenotin0 {p'} (ct : tocs p') : (seq_to_enotin set0 ct) = set0.
Proof.
apply/eqP. rewrite -subset0.
apply/subsetP. move=>x /imsetP [y].
rewrite mem_pmap. move=> /mapP [z] /mapP [a].
rewrite mem_enum. move=>/imsetP [b]. by rewrite in_set0.
Qed.

Lemma ddtextract {p} {ct : (tocs p) } {tocc : (t_occ p)} (dt : DDtype (ct :|: [set tocc])) :
  [forall ct0 : {set (dbranch p)}, Din ct0 dt ==> [forall b : (dbranch p), (b \in ct0) ==> (tocc \notin (useq b))]].
Proof.
apply/forallP. move => ct0. apply/implyP. move => Hct0.
apply/forallP. move => b0. apply/implyP. move => Hb0ct0.
destruct dt as [dt Hdt].
destruct dt as [|s].
- by [].
- assert (Hin : tocc \in ct :|: [set tocc]).
  + by apply/setUP ; right ; apply/set1P.
  apply (implyP (forallP (implyP (forallP ((implyP ((forallP Hdt) tocc)) Hin) ct0) Hct0) b0) Hb0ct0).
Qed.

(** A conjunction with an element not Top is not Top *)
Lemma tr_conj {p} {ct : (tocs p)} (typl : seq (DDtype ct)) :
  has (fun x => x != Triv p) (map val typl) -> val (fold_type_alg DtConj typl (mk_DDtype (@TrivDDtype p ct))) != Triv p.
Proof.
induction typl as [|h tl Htl]. move=>//.
move=>/orP [Hl|Hr]. destruct h as [[|h] Hh]. move=>//. simpl.
by destruct (dt (fold_type_alg DtConj tl (mk_DDtype (@TrivDDtype p ct)))).
destruct h as [[|h] Hh]. simpl. apply/Htl/Hr.
simpl. by destruct (dt (fold_type_alg DtConj tl (mk_DDtype (@TrivDDtype p ct)))).
Qed.

(** A conjunction of Top is Top *)
Lemma triv_conj {p} (ct : (tocs p)) (typl : seq (DDtype ct)) :
  all (fun x => x == Triv p) (map val typl) -> val (fold_type_alg DtConj typl (mk_DDtype (@TrivDDtype p ct))) = Triv p.
Proof.
induction typl as [|h tl Htl]. move=>//.
move=>/andP [Hl Hr]. simpl. unfold tConj.
destruct h. simpl in *. rewrite (eqP Hl).
apply/Htl/Hr.
Qed.

End DDtype.
