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

Require Import syntax.
Require Import occurrences.
Require Import subs.
Require Import pmatch.
Require Import soundness.
Require Import bSemantics.
Require Import tSemantics.
Require Import static.
Require Import norec_sem.
Require Import rinstance.
Require Import completeness.

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset bigop finfun. 

Require Import bigop_aux.
Require Import utils.
Require Import finseqs.
Require Import fintrees.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Combining the static analysis and the rule instantiation *)
Section Transformation.

(** * Definition of dependent substitutions of clauses for a typing *)
(** [p] a program and [i] an interpretation *)
Variable p : program.
Variable i : interp.

(** The variables are not shared across rules *)
Hypothesis Hvns : vars_not_shared p.
(** The variables appearing in the head of a clause are a subset of those
    in the body of the same rule. *)
Hypothesis Hpsafe : prog_safe p.
(** Only intensional predicataes are used as head of clauses *)
Hypothesis Hpsafehds : prog_safe_hds p.
(** No constant in the head of clauses *)
Hypothesis Hvarinhead : only_variables_in_heads p.
(** Only extensional predicates in the interpretation *)
Hypothesis Hsafe_edb : safe_edb i.

(* default constant, predicate, variable, gatom and t_occ for the 
   nth function and the trace semantics *)
Variable def : syntax.constant.
Variable df : symtype.
Variable dv : 'I_n.
Variable dga : gatom.
Variable docc : t_occ p.

(* analyzed variable *)
Variable v : 'I_n.

Definition analysis := analyze_var p (Val def) dv v #|rul_gr_finType|.

(** ** Extraction of the substitutions via the static analysis *)
Definition extract_subs_spec : {set sub} := 
    [set s : sub | (dom s == [set v]) && 
      [exists ct in analysis,
        [forall br in pred_of_set ct, @br_adequate p df def br s v i]]].

Definition extract_vals_br (br: dbranch p) : {set syntax.constant} :=
  [set (nth def (arg_gatom f) (branch_t_ind br)) | f : gatom in i & sym_gatom f == branch_pred df br].

Definition extract_vals_conj (cj : {set dbranch p}) : {set syntax.constant} :=
  \bigcap_(br in cj) extract_vals_br br.

Definition extract_vals_disj (disj : {set {set dbranch p}}) : {set syntax.constant} :=
  \bigcup_(cj in disj) extract_vals_conj cj.

Definition extract_vals : {set syntax.constant} :=
  extract_vals_disj analysis.

Definition extract_vals_sub : {set sub} :=
  [set (add emptysub v c) | c in extract_vals].

Lemma extract_vals_sub_adequate :
  extract_vals_sub = extract_subs_spec.
Proof.
apply/eqP. rewrite eqEsubset. apply/andP;split;apply/subsetP=>x; rewrite in_set.
- move=>/imsetP [c /bigcupP [ct Hctanal /bigcapP Hcap ->]]. clear x.
  apply/andP;split.
  + apply/eqP/dom_singlesub.
  + apply/existsP.
    exists ct. apply/andP;split.
    - apply Hctanal.
    - apply/forallP=>br. apply/implyP=>Hbr.
      apply/existsP. exists c. apply/andP;split.
      + by rewrite ffunE eq_refl.
      + apply/existsP.
        have Hbrb := (Hcap br Hbr).
        move:Hbrb. move=>/imsetP [ga]. 
        rewrite in_set. move=> /andP [Hgai Hgasym] Hceq.
        exists ga. apply/and3P;split;auto.
        by rewrite Hceq.
- move=>/andP [Hdom /existsP [ct /andP [Hctanal Hctconj]]].
  apply/imsetP.
  destruct (sub_elim x v) as [[c Hc]|Hnone].
  + exists c.
    - apply/bigcupP.
      exists ct.
      + apply Hctanal.
      + apply/bigcapP.
        move=>br Hbrct.
        destruct (existsP (implyP (forallP Hctconj br) Hbrct)) as [c' Hc']. move:Hc'.
        move=>/andP [/eqP Hc']. rewrite Hc in Hc'. inversion Hc' as [Hceq].
        move=>/existsP [ga /and3P [Hgain Hgasym Hnth]].
        apply/imsetP. exists ga.
        rewrite in_set. apply/andP;split;auto.
        by rewrite (eqP Hnth).
    - apply (eq_singlesub (eqP Hdom) Hc).
  + move:Hdom. rewrite eqEsubset.
    move=>/andP [H1 /subsetP  H2].
    have H3 := (H2 v (set11 v)).
    rewrite in_set Hnone in H3. inversion H3.
Qed.

Lemma static_extract_spec :
  [forall cl in p,
   (0 < #|tail_vars (body_cl cl) :&: [set v]|) ==>
   [forall s, bmatch def (ffp p i def) cl s ==> (sub_filter s [set v] \in extract_subs_spec)]].
Proof.
apply/forallP=>cl. apply/implyP=>Hcl.
apply/implyP=>Hrv.
apply/forallP=>s.  apply/implyP=>Hsmatch.
rewrite card_gt0 in Hrv. move:Hrv.
move=>/set0Pn [vb /setIP [Hvb1 /set1P Hveq]]. rewrite Hveq in Hvb1.
destruct (bmatch_match_body Hsmatch) as [r Hr1 Hr2]. 
destruct (existsP (implyP (forallP (implyP (forallP (trace_sem_completeness_b dga _ _ _ Hpsafe) _) Hcl) _) Hr1))
    as [tr Htr].
destruct (andP Htr) as [Htr1 Htr2]. clear Htr.
destruct tr as [[ga|[clb sb] descs] Htrwu].
- unfold tst_node_head in Htr2. simpl in Htr2.
  have Hf := eqP Htr2. inversion Hf.
- unfold tst_node_head in Htr2. simpl in Htr2.
  have Htr3 := eqP Htr2. inversion Htr3 as [[Hcleq Hseq]].
  assert (Hrooteq : ABroot (val {| wht := ABNode (RS clb sb) descs; Hwht := Htrwu |}) = inl (RS clb sb)).
  auto. rewrite -Hcleq in Hvb1.
  rewrite in_set. 
  assert (Hv : v \in dom r). 
  apply (subsetP (pmatch_vars_subset Hr1)). rewrite -Hcleq. apply Hvb1.
  apply/andP;split.
  + rewrite eqEsubset. apply/andP;split;apply/subsetP=>x.
    - rewrite in_set ffunE.
      destruct (bool_des_rew (x \in [set v])) as [Hxv|Hxv];rewrite Hxv;auto.
      move=>/set1P->. rewrite in_set ffunE in_set1 eq_refl.
    - have H := forallP Hr2 v. destruct (sub_elim r v) as [[c Hc]|Hnone].
      + rewrite Hc inE_bis in H. by rewrite (eqP H).
      + rewrite in_set Hnone in Hv. inversion Hv.
  + apply/existsP. eexists. apply/andP;split.
    - apply (no_rec_capt_nf (Val def) dv docc Hvns Hpsafe Hpsafehds Hsafe_edb Hvarinhead Htr1
                      Hrooteq Hvb1).
    - apply/forallP=>br. apply/implyP=>Hbr.
      destruct (existsP (implyP (forallP (no_rec_needed (Val def) dv df set0 Hvns Hpsafe Hvarinhead Htr1 Hrooteq Hvb1) _) Hbr))
        as [c Hc]. destruct (andP Hc) as [Hc1 Hc2]. clear Hc.
      apply/existsP. exists c. apply/andP;split;auto.
      rewrite -(eqP Hc1) Hseq.
      rewrite !ffunE in_set1 eq_refl .
      destruct (sub_elim r v) as [[d Hd]|Hnone].
      + rewrite Hd.
        have H := forallP Hr2 v. rewrite Hd inE_bis in H. apply H.
      + by rewrite in_set Hnone in Hv.
Qed.

(** ** Adequacy of the transformation *)
Theorem static_extraction_adequacy (m : nat)
  : (sem (@tprog p [set v] extract_vals_sub) def m i) = (sem p def m i).
Proof.
rewrite extract_vals_sub_adequate (cadequacy static_extract_spec).
reflexivity.
Qed.

End Transformation.
