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
Require Import fixpoint.
Require Import completeness.

From mathcomp
Require Import ssreflect ssrbool eqtype seq ssrnat ssrfun choice fintype tuple finset bigop finfun. 

Require Import bigop_aux.
Require Import utils.
Require Import finseqs.

Set Implicit Arguments.
Unset Strict Implicit.


(** * Transformation of a Datalog program *)
Section Transformation.

(** ** Actual transformation *)

(** Hypotheses: a safe program [p], an interpretation [i]
  and [def] a default constant *)
Variable p : program.
Hypothesis psafe : prog_safe p.
Variable i : interp.
Variable def : syntax.constant.

(** [Rv] is the set of variables to replace *)
Variable Rv : {set 'I_n}.

(** assuming a set of substitutions *)
Variable subs : {set sub}.

(** facts fixedpoint *)
Definition ffp := iter #|bp| (fwd_chain def p) i.

(** Any substitution that match a clause [cl] in the model of [p] has
  its restriction to [Rv] in [subs]. This is the condition that will
  ensure that the transformation does not loose any deductible fact. *)
Hypothesis subs_comp : 
  [forall cl in p, forall s : sub, (bmatch def ffp cl s) ==> (sub_filter s Rv \in subs)].

(** [stv] returns the to-be-replaced variables of a clause *)
Definition stv cl := Rv :&: tail_vars (body_cl cl). 

(** Instantiation of a clause by [subs]. It creates
  a sequence of rules by applying on the clause only 
  the substitution whose
  domain is exactly the domain of the clause *)
Definition inst_rule (cl : clause): seq clause :=
  (* s is only about interesting variables *)
  [seq scl s cl | s <- enum subs & dom s == stv cl].   

(** [tprog] is obtained by instantiating all the rules of [p] *)
Definition tprog : program := 
  flatten [seq (inst_rule cl) | cl <- p].

(** ** Adequacy of the transformation *)

(** Any iteration of the semantic of [p] from [i] is in [ffp] *)
Lemma ffp_comp (k : nat) : sem p def k i \subset ffp.
Proof.
have h_inc : increasing (fwd_chain def p).
  by move=> i'; apply: fwd_chain_inc.
have h_incr := fwd_chain_incr p def.
have h_fp  := fwd_chain_stable def (bpM p).
have h_ub  :  ubound bp (fwd_chain def p).
  by move=> ss H; rewrite subsetT.
have h_lb  : i \subset bp by rewrite /bp.
have [m [m_fix [m_def m_min]]] := has_lfp h_lb h_incr h_inc h_ub.
unfold ffp. unfold sem.
apply/iterf_incr_bound.
apply/iter_fwd_chain_subset.
move=> ib H.
rewrite -m_def m_fix.
apply fwd_chain_incr. rewrite m_def. apply H.
Qed.

(** For any clause, the set of substitutions that match [cl] with the
mth iteration of the semantic is a subset of those that match [cl] with
the model of [p] *)
Lemma nomega_fp : forall (cl : clause) (m : nat), cl \in p -> 
        match_body (sem p def m i) (body_cl cl) \subset match_body ffp (body_cl cl).
Proof.
move=> cl m Hclin.
apply/match_body_incr/ffp_comp.
Qed.

(** Completeness: the m iterate of [p] semantics is contained in the
   m iterate of the semantics of [tprog] *)
Lemma ccompleteness (m : nat)  
  : (sem p def m i) \subset (sem tprog def m i).
Proof.
apply/subsetP.
induction m as [|m Hm];move=> x Hxinit.
- apply Hxinit.
- have Hsemb := Hxinit. 
  destruct (setUP Hxinit) as [Hxindeduced | Hxrec] ; clear Hxinit ; apply/setUP ; [left | right].
  (* x previously deduced *)
  + apply (Hm x Hxindeduced).
  (* x was just deduced via clause ccl *)
  + move:Hxrec. 
    move=> /bigcup_seqP [ccl Hclp /andP [/imsetP [s Hsmatch Hhead] _]].
    rewrite Hhead. rewrite Hhead in Hsemb. clear Hhead.
    apply/bigcup_seqP.
    (*destruct (match_tl_sound Hsmatch) as [sgtl Hseq Hallded]. *)
    (* we need to expose a clause in the transformed program         *)
    (* let's use s(ccl), where x was deduced on clause ccl via sub s *)
    exists (scl (sub_filter s Rv) ccl).
      (* showing that s(ccl) is in the transformed program *)
    - apply/flattenP. exists (inst_rule ccl).
      + apply/map_f/Hclp.
      + apply/mapP. exists (sub_filter s Rv).
        rewrite mem_filter. apply/andP;split.
        rewrite eqEsubset;apply/andP ;split; apply/subsetP=>y.
        - move=>Hy. apply/setIP;split;apply/(subset_to_in Hy).
          apply sub_filter_subset_t.
          apply/subset_trans. apply sub_filter_subset_s.
          apply (match_subset_vars Hsmatch).
        - move=>/setIP [Hy1 Hy2].
          rewrite in_set ffunE Hy1.
          have H := (subset_to_in Hy2 (match_vars_subset Hsmatch)).
          rewrite in_set in H. apply H.
        rewrite mem_enum.
        apply (implyP (forallP (implyP (forallP subs_comp ccl) Hclp) s)).
        unfold bmatch. simpl. apply (match_body_bmatch def). 
        apply (subset_to_in Hsmatch (nomega_fp m Hclp)).
          (* need to show that s is a good way to instantiate ccl *)
        - reflexivity. 
    - apply/andP ; split ; trivial.
      assert (Hdedsub : (sem p def m i) \subset (sem tprog def m i)).
      apply/subsetP ; move => y Hy.
      apply (Hm y Hy).
      pose Hsub := (subsetP (match_body_incr ccl Hdedsub) s) Hsmatch.
      unfold cons_clause. apply/imsetP.
      exists (sub_filter s (~: Rv)).
      + apply untyped_in_scl_match_body. apply Hsub.
        apply disjointC.
        apply/forallP=>y. apply/orP. 
        destruct (bool_des_rew (y \in Rv)) as [H|H].
        left;apply H. right. apply/setCP. unfold not. by rewrite H.
      + destruct ccl. apply/val_inj/gr_raw_atom_scl_eq.
        move=>v. rewrite !ffunE.  
        by destruct (bool_des_rew (v \in Rv)) 
          as [Htyp|Htyp];rewrite !Htyp;[right|left];split;
        (reflexivity || rewrite in_set Htyp).
Qed.

(** Soundness: the m iterate of [tprog] semantics is contained in the
   m iterate of the semantics of [p] *)
Lemma csoundness (m : nat) 
  : (sem tprog def m i) \subset (sem p def m i). 
Proof.
apply/subsetP.
induction m as [|m Hm];move=> x Hxinit.
- apply Hxinit.
- have Hsemb := Hxinit.
  destruct (setUP Hxinit) as [Hxindeduced | Hxrec] ; clear Hxinit ; apply/setUP ; [left | right].
  (* x previously deduced *)
  + apply (Hm x Hxindeduced).
  (* x was just deduced via clause ccl *)
  + move:Hxrec. 
    (* we need to expose a clause in the original program *)
    (* let's "untransform" ccl *)
    move=> /bigcup_seqP [ccl /flattenP [pinst /mapP [ocl Hoclinp Hpinsteq] Hcclinpinst] 
                         /andP [/imsetP [s Hsmatch Hhead] _]].
    rewrite Hhead. rewrite Hhead in Hsemb.
    apply/bigcup_seqP.
    (* let's ocl (original clause) *)
    (*assert (Hsdom : dom (only_typed p s) == tail_vars (body_cl ccl) :&: typed_vars p).*)
    exists ocl;auto. apply/andP;split;auto.
    apply/imsetP.
    (* we need the substitution that was used in the original program,
       ie. the union of the sub that transformed the original program 
       and the one that was used in the transformed version (s)            *)
    rewrite Hpinsteq in Hcclinpinst. clear Hpinsteq.
    (* transub is the substitution that transformed the program *)
    destruct (mapP Hcclinpinst) as [transub Htransubprop Hccleq]. clear Hcclinpinst.
    rewrite mem_filter in Htransubprop. 
    destruct (andP Htransubprop) as [H Htransubissub]. clear Htransubprop.
    simpl in H. 
    destruct ocl as [hocl tlocl].
    rewrite Hccleq. 
    (*assert (Htmp : dom s \subset tail_vars tlocl).
    apply/subset_trans. apply sub_filter_subset_s.
    rewrite (eqP H). apply/subsetIr.*)
    exists (subU transub s).
    - assert (Hdedsub : (sem tprog def m i) \subset (sem p def m i)).
      apply/subsetP ; move => y Hy.
      apply (Hm y Hy).
      have Hsub := (subsetP (match_body_incr _ Hdedsub) s) Hsmatch. 
      apply subU_match;auto.
      (*assert (Heq : (scl (sub_filter transub Rv) (Clause hocl tlocl)) = scl transub (Clause hocl tlocl)).
      rewrite sub_sub_filter. reflexivity.
      rewrite (eqP H). apply/subsetIl.*)
      rewrite (eqP H). 
      apply subsetIr.
      rewrite -Hccleq. apply Hsub.
    - apply/val_inj/(Logic.eq_sym)/gr_raw_atom_scl_eq. 
      move=>v. rewrite !ffunE.  
      destruct (sub_elim s v) as [[c Hc]|Hc];rewrite Hc;
      destruct (sub_elim transub v) as [[d Hd]|Hd];rewrite !Hd;
      try by left. 
      rewrite Hccleq in Hsmatch.
      assert (Hsub : dom transub \subset tail_vars (body_cl (Clause hocl tlocl))).
      rewrite (eqP H). apply subsetIr.
      have Hdom0 := (match_domsI Hsmatch (subsetP Hsub)).
      assert (Hf : v \in set0). rewrite -Hdom0. 
      apply/setIP. split. by rewrite in_set Hc.
      by rewrite in_set Hd.
      by rewrite in_set0 in Hf.
      by right.
Qed.

(** [p] and [tprog] semantic coincide àt each iteration *)
Theorem cadequacy (m : nat)  
  : (sem tprog def m i) = (sem p def m i).
Proof.
apply/eqP ; rewrite eqEsubset;apply/andP ;split ; 
[apply csoundness|apply ccompleteness].
Qed.

End Transformation.
