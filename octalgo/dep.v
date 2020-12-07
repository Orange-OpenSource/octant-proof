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

(*
(** ** Modification of the dbranch type, dropping the t_ind info
       but allowing multiple t_occ at the leaf level *)
Section ddbranch.

Variable p : program.

(** ** ddbranch is a series of atom occurrences with, at the end, 
       a sequence of term occurrences *)
Definition ddbranch := 
  ((@uniq_seq_finType (a_occ_finType p)) * option (seq (t_occ p)))%type.

Definition make_ddleaf (l : seq (t_occ p)) : ddbranch :=
  (unil,Some l).

End ddbranch.*)

(** * Merging analyses results *)
Section merging.

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

(** ** Clause containing the variables to analyze *)
Variable cl : clause.
Hypothesis cl_in_p : cl \in p.

(* default constant, predicate, variable, gatom and t_occ for the 
   nth function and the trace semantics *)
Variable def : syntax.constant.
Variable df : symtype.
Variable dv : 'I_n.
Variable dga : gatom.
Variable docc : t_occ p.

(** ** Variables to analyze in parallel *)
Variable vs : {set 'I_n}.
(** ** Calling the analysis (on elements of [vs] in practice) *)
Definition vs_analysis := fun v => analyze_var p (Val def) dv v #|rul_gr_finType|.

(** ** Watermaking the branches with the corresponding variables *)
Definition watermark_br (v : 'I_n) (br : dbranch p) := (v,br). 
Definition watermark_conj v (ct : {set dbranch p}) := 
  [set watermark_br v br | br in ct]. 
Definition watermark_disj v (disj : {set {set dbranch p}}) := 
  [set watermark_conj v ct | ct in disj].
Definition marked_vs_analyses := 
  map (fun v => watermark_disj v (vs_analysis v)) (enum vs).

(** ** The variables of [vs] all appear in the same clause *)
Hypothesis vars_in_clause : [forall v in vs, v \in cl_vars cl].

(** ** p.i *)
Definition predi := prod_finType symtype (ordinal_finType max_ar).
Definition dsources := {set {set {ffun 'I_n -> predi}}}.

Definition compatible_toccs (t1 t2 : t_occ p) : bool :=
  (r_ind t1 == r_ind t2) && (b_ind t1 == b_ind t2).

(** If two branches start (top-down view) from the same atom occurrence,
    then they have to be consistent all the way *)
Fixpoint br_agree (b1 b2 : seq (t_occ p)) :=
  match b1,b2 with
    | x1::l1, x2::l2 => 
        if (b_ind x1 == b_ind x2) then
          match l1,l2 with 
          | y1::l1', y2::l2' => 
            (r_ind y1 == r_ind y2) && br_agree l1 l2 
          | _,_ => true end else true
    | _,_ => true end.

(* br_agree lifted to conj_dbranch *)
Definition vct_agree (c1 c2 : {set prod_finType (ordinal_finType n) (dbranch p)}) :=
  [forall b1 in c1, [forall b2 in c2, br_agree (snd b1) (snd b2)]].

(** returns the cartesian product (ie. all combinations) of 
   /\ trees of the different (non-trivial) types           *)
(** i.e., \/ was unfolded *)
(** eliminates inconsistent conj_trees *)
Definition conj_branches_comb := 
  [set x in gen_cart_prod marked_vs_analyses 
    | [forall c1 in x, [forall c2 in x, vct_agree c1 c2]]].

(** ** disjunction over sets of mixed branches *)
Definition all_branches_comp :=
  [set \bigcup_(ct <- tval cts_tup) ct | cts_tup in conj_branches_comb].

Definition dep (b1 b2 : dbranch p) := 
   (size b1 == size b2) 
&& all (fun x => b_ind x.1 == b_ind x.2) (zip b1 b2).

(** This is a reflexive relation *)
Lemma dep_refl (b : dbranch p): dep b b.
Proof.
apply/andP;split. auto.
destruct b as [b Hb]. simpl. clear Hb. 
induction b as [|hb tlb Hr].
auto.
apply/andP;split. auto. apply Hr.
Qed.  

(** This is symmetric *)
Lemma dep_comm (b1 b2 : dbranch p) : dep b1 b2 -> dep b2 b1.
Proof.
unfold dep. move=>/andP [H1 H2]. apply/andP;split.
by rewrite (eqP H1). clear H1. 
destruct b1 as [b1 Hb1]; destruct b2 as [b2 Hb2]. 
simpl in *. clear Hb1. clear Hb2. 
move:b2 H2. induction b1 as [|hb1 tlb1 Hb];move=>[|hb2 tlb2] // /andP [H1 H2].
apply/andP;split. by rewrite (eqP H1). apply/Hb/H2.
Qed.

(** It is also transitive (it is an equivalence relation) *)
Lemma dep_trans (b1 b2 b3 : dbranch p) : dep b1 b2 -> dep b2 b3 -> dep b1 b3.
Proof.
unfold dep. 
move=>/andP [H1 H2] /andP [H3 H4]. apply/andP;split.
by rewrite (eqP H1) (eqP H3).  
destruct b1 as [b1 Hb1]; destruct b2 as [b2 Hb2]; destruct b3 as [b3 Hb3].
simpl in *. clear Hb1. clear Hb2. clear Hb3.
move:b2 H1 H2 b3 H3 H4. induction b1 as [|h1 tl1 Hr];move=> [|h2 tl2] H1 H2 [|h3 tl3] H3 H4 //;
move:H2 H4. move=>/andP [Hb1 Hb2] /andP[Hb3 Hb4].
apply/andP;split. by rewrite (eqP Hb1) (eqP Hb3). 
apply Hr with (b2 := tl2). apply H1. apply Hb2. apply H3. apply Hb4.
Qed. 

(** Extension of dep to a pair variable and branch. We are looking
   for groups of variables having branches verifying [dep] *)
Definition vdep (x1 x2 : ('I_n * dbranch p)%type) : bool :=
  dep (snd x1) (snd x2).

(** checking whether s v matches the branch br and ga that were picked *)
(** [ga_match_br ga br v s] iff the last element of [br] is [tocc]
  that refers to an atom [a] such that the symbol of [a] is the
  symbol of [ga] and the term referered by [tocc] in [ga] is [s v] *)
Definition ga_match_br (ga : gatom) (br : seq (t_occ_finType p)) (v : 'I_n) (s : sub) : bool :=
match br with
  (* pathological case *)
| [::] => false
| a :: l =>
    match s v with
    | Some c =>
        match p_at (last a l) with
        | Some pred => (sym_gatom ga == pred) && (nth_error (arg_gatom ga) (t_ind (last a l)) == Some c)
        | None => false
        end
    | None => false end end.

Definition extract_conj_spec (ct : {set (prod_finType (ordinal_finType n) (dbranch p))}) : {set sub} :=
  let vars := [set x.1 | x in ct] in
  let parts := equivalence_partition vdep ct in
  [set s | dom s == vars
         & [forall part : {set (prod_finType (ordinal_finType n) (dbranch p))} in parts,
             [exists ga in i, [forall vbr in part, ga_match_br ga vbr.2 vbr.1 s]]]].

Definition extract_disj_spec (disj : {set {set (prod_finType (ordinal_finType n) (dbranch p))}}) :=
  \bigcup_(ct in disj) extract_conj_spec ct.

Definition extraction := extract_disj_spec all_branches_comp.

Lemma extract_comp :
 [forall s, bmatch def (ffp p i def) cl s ==> (sub_filter s vs \in extraction)].
Proof.
apply/forallP=>s.  apply/implyP=>Hsmatch.
destruct (bmatch_match_body Hsmatch) as [r Hr1 Hr2].
destruct (existsP (implyP (forallP (implyP (forallP (trace_sem_completeness_b dga _ _ _ Hpsafe) _) cl_in_p) _) Hr1))
    as [tr Htr].
destruct (andP Htr) as [Htr1 Htr2]. clear Htr.
destruct tr as [[ga|[clb sb] descs] Htrwu].
- unfold tst_node_head in Htr2. simpl in Htr2.
  have Hf := eqP Htr2. inversion Hf.
- unfold tst_node_head in Htr2. simpl in Htr2.
  have Htr3 := eqP Htr2. inversion Htr3 as [[Hcleq Hseq]].
  (* assert (Hrooteq : ABroot (val {| wht := ABNode (RS clb sb) descs; Hwht := Htrwu |}) = inl (RS clb sb)).
  auto. rewrite -Hcleq in Hvb1. *)
  apply/bigcupP.
  eexists. exists (\bigcup_(ct <- tval ???) ct).
  + apply/imsetP.
    (* choix des conjonctions *)
    (*exists (\big[setU (T:=prod_finType (ordinal_finType n) (dbranch p))/set0]_(ct <- ?x) ct).*)
    eexists.
    - rewrite in_set. apply/andP;split.
      + rewrite in_set.
        apply/forallP=>j.
        unfold marked_vs_analyses.
        
        admit.
      + (* compatibilité des conjs *) admit.
    - reflexivity.
  + (* filtré dans l'extraction *) admit. 
   

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

Theorem static_extraction_adequacy (m : nat)
  : (sem (@tprog p vs extraction) def m i) = (sem p def m i).
Proof.
rewrite cadequacy;[reflexivity|].

TODO.
Qed.

End merging.