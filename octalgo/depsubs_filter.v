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
Require Import tSemantics.
Require Import soundness.
Require Import dTypes.
Require Import ddTypes.
Require Import rules.
Require Import ctransfo.
Require Import depsubs.
Require Import depsubs_completeness.


From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset bigop finfun.

Require Import bigop_aux.
Require Import utils.
Require Import finseqs.
Require Import fintrees.

Set Implicit Arguments.
Unset Strict Implicit.

Section cadequacy.

Variable p : program.
Variable i : interp.
Variable def : syntax.constant.
Variable dv  : 'I_n.

(** * [dep_subs] captures all substitutions for the semantics of [p] in [i] *)
Hypothesis psafe : prog_safe p.
Hypothesis phsafe : prog_safe_hds p.
Hypothesis pvars : vars_not_shared p.
Hypothesis ext_edb : safe_edb i.

(** assuming a typing to study *)
Variable typing : forall v, var_type p v.

Variable dga : gatom.

(** The substitutions matching [cl] in the semantics of [p] verify [dep_subs_cl]
  for the the typing [typing] *)
Lemma subs_comp_cl : forall (s : sub) (cl : clause) (m : nat),
           cl \in p
        -> s \in match_body (sem p def m i) (body_cl cl)
        -> s \in (dep_subs_cl i typing cl).
Proof.
move=> s cl m Hclin Hsmatch.
(* extracting trace sem tree *)
destruct (existsP (implyP (forallP (implyP (forallP 
      (trace_sem_completeness_b dga def m i psafe) cl) Hclin) s) Hsmatch))
  as [tst Htst].
destruct (andP Htst) as [Htstded Htsthead]. clear Htst.
(* getting rid of the leaf case *)
destruct tst as [[l|[hcl hs] l] Htrace];
have H := eqP Htsthead; inversion H as [[Hcleq Y]]. clear H.
move:Htrace Htstded Htsthead. 
rewrite !Hcleq !Y. clear Hcleq. clear Y. clear hcl. clear hs.
move=>Htrace Htraceded Htracehead.
(* preparing tuple *)
assert (Hroot : ABroot (val {| wht := ABNode (RS cl s) l; Hwht := Htrace |}) = inl (RS cl s)).
auto.
destruct (existsP (all_exist_tuple (semt_exists_ad_type ext_edb psafe phsafe pvars typing Htraceded Hroot)))
         as [tup Htup]. 
destruct (andP Htup) as [Htup1 Htup2]. 
clear Htup. unfold dep_subs_cl.
apply/bigcup_seqP. unfold stv.
move:tup Htup1 Htup2.
(*rewrite !ad_typed.*)
move=>tup Htup1 Htup2.
exists tup. apply mem_index_enum.
rewrite in_set. apply/andP;split.
- apply/forallP=>part. apply/implyP=>Hpart.
  (* showing that the equivalence partition is actually one *) 
  assert (Hparteq : partition (equivalence_partition (vdep (p:=p)) (\big[setU
                     (T:=prod_finType 
                           (ordinal_finType n) 
                           (dbranch p))/set0]_(vt <- tup)
                     [set (vt.1, x) | x in pred_of_set vt.2])) 
                     (\big[setU
                        (T:=prod_finType 
                              (ordinal_finType n) 
                              (dbranch p))/set0]_(vt <- tup)
                    [set (vt.1, x) | x in pred_of_set vt.2])).
  + apply/equivalence_partitionP.
    move=>a b c Ha Hb Hc. split. 
    apply vdep_refl. apply vdep_congr.
    destruct (andP Hparteq) as [Hcover Hb]. clear Hparteq.
    destruct (andP Hb) as [Htrivpart Hs0part]. clear Hb. clear Htrivpart.
    (* we need to extract a branch from part, which can now be done *)
    destruct (set_0Vmem part) as [Hf|[vbr Hvbr]].
    (* absurd case *)
    rewrite Hf in Hpart. by rewrite Hpart in Hs0part. clear Hs0part.
    (* vbr is the "witness" of part
       We need to find which ct in tup it comes from
       ie., the ct that built part *)
    move:Hpart. move=>/imsetP [partrep Hrepin Hparteq].
    (* part is the set of (v,br) which are vdep to partrep,
       the representative of the partition *)
    rewrite Hparteq in_set in Hvbr.
    (* vbr, the witness, comes from vct *)
    move:Hvbr. move=>/andP [/bigcup_seqP [vct Hvctin Hvct] Hvdepvbr].
    destruct (andP (allP Htup2 vct Hvctin)) as [Hvct2in Hvcttr]. clear Hvctin.
    (* vct (which contains vbr) is in the type of v *)
    move:Hvct.
    move=>/andP [/imsetP [brb Hbrbin Hvbreq] _].
    (* splitting vbr into v and br *)
    destruct vbr as [v br]. inversion Hvbreq as [[Hveq Hbreq]].
    clear Hvbreq. rewrite -Hbreq in Hbrbin. clear Hbreq. clear brb.
    destruct vct as [vct1 vct2].
    simpl in Hvct2in. destruct (typing vct1) as [vtyp mtyp Hsub Htyping]. simpl in Hvct2in. 
    have Hbrpred := (all_brpred_incr (typing_brpred Htyping psafe phsafe pvars) Hsub) vct2 Hvct2in br Hbrbin.
    have Hallbr := (all_tat_incr (typing_tat Htyping) Hsub Hvct2in Hbrbin).
    destruct (andP Hvcttr) as [Hvcttr1 Hvcttr2]. 
    destruct br as [[|hbr tlbr] Hbr]. 
    have Hf := (implyP (forallP Hvcttr1 _) Hbrbin). inversion Hf.
    assert (Htocc : nth_error (val {| useq := hbr :: tlbr; buniq := Hbr |}) 0 = Some hbr). auto.
    destruct (andP Hallbr) as [Hallbrh Hallbrl]. 
    destruct (existsP Hallbrh) as [vb Hvb]. 
    destruct (existsP (sem_t_vtr_exists_ga Htraceded Hvcttr Hbrbin Hbrpred Hallbr Htocc (eqP Hvb)))
      as [ga Hga].
    destruct (andP Hga) as [Hgain Hgab]. clear Hga.
    apply/existsP. exists ga. apply/andP;split. apply Hgain. 
    apply/forallP=>svb. rewrite Hparteq in_set.
    apply/implyP=>/andP [/bigcup_seqP [nvct Hnvctin /andP [/imsetP [nvbb Hnvbbin -> Htriv]]]]. clear Htriv.
    destruct partrep as [vrep brrep]. 
    unfold vdep. move=>/= Hdep. simpl in Hvdepvbr.
    have Hdepc := (dep_trans (dep_comm Hdep) Hvdepvbr). 
    destruct (andP (allP Htup2 _ Hnvctin)) as [Hnvct2typed Hnvctvtr].

    destruct nvct as [nvct1 nvct2]. simpl in Hnvct2typed.
    destruct (typing nvct1) as [vtypb mtypb Hsubb Htypingb]. simpl in Hnvct2typed.
    have Hnbrpred := (all_brpred_incr (typing_brpred Htypingb psafe phsafe pvars) Hsubb) nvct2 Hnvct2typed nvbb Hnvbbin.
    have Hnallv := (all_tat_incr (typing_tat Htypingb) Hsubb Hnvct2typed Hnvbbin).
    destruct (existsP (implyP (implyP (implyP (forallP Hgab nvbb) Hdepc) Hnbrpred) Hnallv))
      as [toccd Htoccd]. destruct (andP Htoccd) as [Htoccd1 Htoccd2]. clear Htoccd.
    destruct nvbb as [[|hnvbb tlnvbb] Hnvbb]. inversion Htoccd1. 
    destruct (existsP Htoccd2) as [nv Hnv]. clear Htoccd2. destruct (andP Hnv) as [Hnv1 Hnv2].
    clear Hnv. destruct vtypb as [|vtypb]. by rewrite in_set0 in Hnvct2typed.
    assert (Hvatyped : [exists t, Tr (p:=p) vtypb == Tr (p:=p) t]).
    by apply/existsP; exists vtypb. 
    destruct (dt_get_dcb_subtype_rev Hsubb Hnvct2typed Hvatyped)
      as [c1 [Hc1 Hc2]].
    have Hveqb := (implyP (forallP (implyP (forallP (implyP (forallP (typing_v_head Htypingb) _) 
                    Hc1) _) (subset_to_in Hnvbbin (csub_subset Hc2))) _) Htoccd1).
    rewrite (eqP Hveqb) in Hnv1. move:Hnv1. move=>/eqP [Hveqbb]. rewrite -Hveqbb in Hnv2.
    simpl. simpl in Hnv2. apply Hnv2.  
- rewrite in_set. apply/forallP=>j. apply/implyP=>Hj. rewrite tcastE.
  rewrite (@tnth_nth _ _ set0 (in_tuple (seq_of_conj_trees typing cl))) in_tupleE nth_image. 
  apply/imsetP. simpl.
  assert (H : tnth tup j = (enum_val j, (tnth tup j).2)).
  apply/prod_eq. simpl. rewrite (@enum_val_nth _ _ dv). 
  rewrite (@tnth_nth _ _ (dv,set0)). simpl.
  destruct tup as [tup Htup]. apply (pair_seq_nth_proj_l). apply (eqP Htup1). auto.
  exists (snd (tnth tup j)).
  + destruct (andP (allP Htup2 (tnth tup j) (mem_tnth j tup))) as [H1 H2].
    assert (Hb : (tnth tup j).1 = enum_val j). by rewrite H.
    by rewrite -Hb.
  + apply H.
Qed.

(** Any substitution in the semantics of [p] for [i] is in [dep_subs i typing].
 This will imply that using [dep_subs] as basis for program specialization
 will not loose any deduced fact. *)
Lemma subs_comp : forall (s : sub) (cl : clause) (m : nat),
           cl \in p
        -> s \in match_body (sem p def m i) (body_cl cl)
        -> s \in dep_subs i typing.
Proof.
move=>s cl m Hclin Hsmatch.
apply/bigcup_seqP.
exists cl.
apply/mem_index_enum.
apply/andP;split.
apply/subs_comp_cl/Hsmatch/Hclin.
apply Hclin.
Qed.

(*Lemma subs_comp_sub :
  \bigcup_(cl <- p) nomega p i def cl \subset dep_subs i typing.
Proof.
apply/subsetP=>s /bigcup_seqP [cl Hclin /andP [Hsin Htriv]].
apply (subs_comp Hclin Hsin).
Qed.*)

End cadequacy.
