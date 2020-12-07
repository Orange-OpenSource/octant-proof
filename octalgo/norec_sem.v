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
Require Import bSemantics.
Require Import monotonicity.
Require Import soundness.
Require Import tSemantics.

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset bigop finfun.

Require Import bigop_aux.
Require Import utils.
Require Import finseqs.
Require Import fintrees.

Require Import Sumbool.

Set Implicit Arguments.
Unset Strict Implicit.


Implicit Types (s r : sub) (d def : syntax.constant) (t : term) (a : atom)
               (ga : gatom) (tl : list atom) (cl : clause) (i : interp).

(** * No recursion traces: extracting bounded sequences from deduction traces *)
Section no_rec_traces.

(** Program to analyze *)
Variable p : program.
(** default ground atom for the trace semantics *)
Variable gat_def : gatom.

(** Default term, variable and predicate, actually unsused but required by the nth 
    or nth_error functions *)
Variable dt : term.
Variable dv : 'I_n.
Variable df : symtype.

(** A branch is a sequence without repetition of [t_occ] *)
Definition dbranch := (@uniq_seq_finType (t_occ_finType p)).

(** the predicate corresponding to the last occurrence of the branch *)
Definition branch_pred (br : seq (t_occ p)) :=
  match br with
    | [::] => df (* case not used in practice *)
    | a :: l => match p_at (last a l) with
        | None => df (* same *)
        | Some f => f end end.

(** branch_pred stable wrt. cons *)
Lemma branch_pred_eq h (s : seq (t_occ p)) : 
  size s > 0 -> branch_pred s = branch_pred (h::s).
Proof.
by destruct s.
Qed.

(** [t_ind] (term index) of the last occurrence of the branch *)
Definition branch_t_ind (br : seq (t_occ p)) :=
  match br with
    | [::] => 0 (* unused case *)
    | a :: l => t_ind (last a l) end. 

(** branch_t_ind stable wrt. cons *)
Lemma branch_t_ind_eq h (s : seq (t_occ p)) : 
  size s > 0 -> branch_t_ind s = branch_t_ind (h::s).
Proof.
by destruct s.
Qed.

(** ** The actual extraction *)
(**    [prev] is the set of previously visited [t_occ]s
       [tr] is the trace to "unrec"
       [v] is the variable we focus on
       [count] is the fuel used for termination 
       The function computes the sequences of [t_occ]s the values of [v] go
       through, and eliminates the repetition of [t_occ]s *)
Fixpoint unrec_trace_gen (prev : (tocs p)) (tr : (ABtree rul_gr_finType gatom_finType)) (v : 'I_n) (count : nat) : {set dbranch} :=
  match count with | 0 => set0 | count.+1 =>
  match tr with
    | ABLeaf _ => [set unil]
    | ABNode (RS cl s) descs => 
          let unrec_b (o : t_occ p) : {set dbranch} :=
            match (nth_error descs (b_ind o)) with
              | None => set0 (* None case not used in practice *)
              | Some (ABLeaf _) => [set unil]
              | Some (ABNode (RS clb sb) descsb) => 
                  unrec_trace_gen (o |: prev) 
                                  (ABNode (RS clb sb) descsb) 
                                  (get_cl_var dt dv clb (t_ind o)) 
                                  count end
        in
        let occs := (occsInProgram p v) :\: prev in
        \bigcup_(occ in occs) [set pucons occ l | l in unrec_b occ]
         end end.

(** Version used in practice, where [prev] is empty *)
Definition unrec_trace (tr : (ABtree rul_gr_finType gatom_finType)) (v : 'I_n) (count : nat) : {set dbranch} :=
  unrec_trace_gen set0 tr v count.

(** ** The sequences in the no recursion trace are disjoint from [prev] *)
Lemma unrec_trace_gen_notin (prev : (tocs p)) (tr : (ABtree rul_gr_finType gatom_finType)) (v : 'I_n) (count : nat) :
  [forall br in unrec_trace_gen prev tr v count, [disjoint [set x | x \in (useq br)] & prev]].
Proof.
move:prev tr v. induction count as [|count Hrec].
- intros. apply/forallP=>x. apply/implyP=>//=. by rewrite in_set0.
- move=>prev tr v. apply/forallP=>br. apply/implyP=>/=.
  destruct tr as [|[cl s] descs].
  + move=>/set1P ->. simpl. rewrite disjoints_subset. apply/subsetP=>x. rewrite in_set. by rewrite in_nil.
  + move=>/bigcup_seqP [i Hin] /andP [/imsetP [x Hx ->] Hinb].
    unfold pucons.
    destruct (nth_error_case descs (b_ind i)) as [Hnone|[[|] [Hd1 Hd2]]].
    - by rewrite Hnone in_set0 in Hx.
    - rewrite Hd2 in Hx. rewrite (set1P Hx).
      simpl. rewrite disjoints_subset. 
      apply/subsetP=>y. rewrite in_set mem_seq1.
      move=>/eqP ->. rewrite in_setC. 
      have H := setDP Hinb. by destruct H.
    - rewrite Hd2 in Hx. destruct s0. 
      have H := implyP (forallP (Hrec _ _ _) _) Hx.
      rewrite disjoints_subset subsetC in H.
      rewrite disjoints_subset.
      have Hb := (subsetP H i (setU11 i _)).
      rewrite in_setC in_set in Hb.
      destruct sumbool_of_bool as [Hf|Hf].
      + apply/subsetP=>y. rewrite in_set in_cons in_setC.
        move=>/orP [/eqP ->|Hyin].
        - have Ht := setDP Hinb. by destruct Ht.
        - destruct (bool_des_rew (y \in prev)) as [Hyr|Hy].
          + have Ht := subsetP H y (setU1r i Hyr). 
            rewrite in_setC in_set Hyin in Ht. inversion Ht.
          + by rewrite Hy.
      + by rewrite Hb in Hf.
Qed.

(** ** The no recursion trace is monotonuous wrt. its fuel *)
Lemma unrec_trace_gen_count_incr (prev : (tocs p)) (tr : (ABtree rul_gr_finType gatom_finType)) (v : 'I_n) (c1 c2 : nat) br :
 c1 <= c2 -> br \in unrec_trace_gen prev tr v c1 -> br \in unrec_trace_gen prev tr v c2.
Proof.
move:prev v c1 c2 br.
induction tr using abtree_ind_prop;
move=>prev v [|c1] [|c2] br //=.
- by rewrite in_set0.
- by rewrite in_set0.
- destruct h as [cl s]. 
  move=>Hlt /bigcup_seqP [i Hienum /andP [/imsetP [x Hxin ->] Hin]].
  destruct (nth_error_case l (b_ind i)) as [Hnone|[[|] [Hd1 Hd2]]].
  + by rewrite Hnone in_set0 in Hxin.
  + rewrite Hd2 in Hxin. rewrite (set1P Hxin).
    unfold pucons. simpl.
    apply/bigcup_seqP. exists i. auto.
    apply/andP;split. rewrite Hd2. 
    apply/imsetP. exists unil. by apply/set1P.
    auto. auto.
  + unfold pucons.
    rewrite Hd2 in Hxin. destruct s0 as [clb sb].
    have Hif := disjoint_setI0 (implyP (forallP (unrec_trace_gen_notin _ _ _ _) _) Hxin).
    destruct sumbool_of_bool as [Hnotin|Hinin].
    - apply/bigcup_seqP. exists i. auto.
      apply/andP;split. apply/imsetP. exists x.
      rewrite Hd2. 
      apply/(all_prop_in H Hd1). apply Hlt.
      apply Hxin. destruct sumbool_of_bool as [Hit|Hit].
      by apply/val_inj. rewrite Hnotin in Hit. inversion Hit.
      auto.
    - move:Hinin. move=>/negPf /Bool.not_false_is_true Hinin.
      assert (Hf : i \in (@set0 (t_occ_finType p))). 
      rewrite -Hif. apply/setIP. split. rewrite in_set. apply Hinin.
      by apply/setU1P;auto. by rewrite in_set0 in Hf.
Qed.

(** ** [unrec_trace_gen] has a normal form wrt. its fuel *)
Lemma unrec_trace_gen_normal_form (prev : (tocs p)) (tr : (ABtree rul_gr_finType gatom_finType)) (v : 'I_n) (count : nat) :
  forall br, br \in unrec_trace_gen prev tr v count -> br \in unrec_trace_gen prev tr v (ABheight tr).+1.
Proof.
move:prev v count.
induction tr using abtree_ind_prop;
move=>prev v [|count] br //.
- by rewrite in_set0.
- by rewrite in_set0.
- destruct h as [cl s].
  move=>/bigcup_seqP [i Hinenum /andP [/imsetP [x Hxin ->] Hinb]].
  destruct (nth_error_case l (b_ind i)) as [Hnone|[[|] [Hd1 Hd2]]].
  + by rewrite Hnone in_set0 in Hxin. 
  + rewrite Hd2 in Hxin.
    rewrite (set1P Hxin).
    apply/bigcup_seqP. exists i. auto.
    apply/andP;split;auto.
    apply/imsetP.
    exists x.
    by rewrite Hd2 Hxin. rewrite (set1P Hxin). by apply/val_inj. 
  + rewrite Hd2 in Hxin. destruct s0 as [clb sb].
    have Hif := disjoint_setI0 (implyP (forallP (unrec_trace_gen_notin _ _ _ _) _) Hxin).
    have Hrec := (all_prop_in H Hd1 _ _ _ _ Hxin).
    assert (Hh : (ABheight (ABNode (RS clb sb) l0)).+1 <= (ABheight (ABNode (RS cl s) l))).
    apply/sstree_height. apply/hasP. exists (ABNode (RS clb sb) l0 ). apply Hd1.
    simpl. by apply/orP;left. 
    unfold pucons.
    destruct sumbool_of_bool as [Hnotin|Hinin].
    - apply/bigcup_seqP. exists i. auto.
      apply/andP;split. apply/imsetP. exists x.
      rewrite Hd2.
      apply/(unrec_trace_gen_count_incr Hh Hrec).
      apply/val_inj. simpl. unfold pucons.
      destruct sumbool_of_bool as [Hf|Hf]. auto.
      by rewrite Hnotin in Hf. auto. 
    - move:Hinin. move=>/negPf /Bool.not_false_is_true Hinin.
      assert (Hf : i \in (@set0 (t_occ_finType p))). 
      rewrite -Hif. apply/setIP. split. rewrite in_set. apply Hinin.
      by apply/setU1P;auto. by rewrite in_set0 in Hf.
Qed.

(** A substitution [s] is adequate wrt. a branch [br], ending with an occurrence [o] referring to
    an occurrence of predicate [f], and an interpretation [i] iff. [s] [v] = [c], st. [i] contains
    a [f]-fact that has c at the position matching [o] *)
Definition br_adequate def (br : dbranch) (s : sub) (v : 'I_n) (i : interp) : bool :=
  [exists c : syntax.constant, (s v == Some c) && 
         [exists ga in i, (sym_gatom ga == branch_pred br) 
                       && (nth def (arg_gatom ga) (branch_t_ind br) == c)]].

(** ** Core result: any value [v] can take in practice during an execution of [p]
       is captured by the no-recursion trace *)
Theorem no_rec_needed def prev (tr : trace_sem_trees gat_def) (i : interp) (m : nat) cl s v :
   vars_not_shared p
-> prog_safe p
-> only_variables_in_heads p
-> tr \in sem_t p gat_def def m i
-> ABroot (val tr) = inl (RS cl s)
-> v \in tail_vars (body_cl cl)
-> [forall br in unrec_trace_gen prev (val tr) v (ABheight (val tr)).+1, 
      br_adequate def br s v i].
Proof.
move:cl s v tr prev.
induction m as [|m Hrec].
- move=>/= cl s v tr prev Hvns Hpsafe Hvarshead /imsetP [x Hx ->] //.
- move=> cl s v tr prev Hvns Hpsafe Hvarshead Hded. have Hded_copy := Hded. move:Hded. 
  move=>/setUP [Hded|/bigcup_seqP [clb Hclbinp /andP [H _]]].
  + by apply/Hrec.
  + destruct (imset2P (mem_pset_set H))
      as [descs sb Hdescsded Hsmatch Htreq]. clear H.
    destruct tr as [[|[clt st] descst] Htr];
    move=>// [Hcleq Hseq] Hvin.
    unfold wu_pcons_seq in Htreq.
    unfold wu_pcons_wlist in Htreq. move:Htreq.
    destruct sumbool_of_bool;move=> //[Hcleqb Hseqb Hdescseq].
    assert (Hdescssize : size descs <= bn).
    destruct descs as [descs Hdescs]. rewrite (eqP Hdescs).
    destruct clb. apply wlist_to_seq_size.
    rewrite (seq_wlistK Hdescssize) in Hdescseq.
    (* cl = clb = clt, s = sb = st and descs = descst *)
    rewrite in_set in Hsmatch. 
    destruct (and3P Hsmatch) as [Hsbmatch Hdedsub Hprevded]. clear Hsmatch.
    apply/forallP=>br. apply/implyP=>Hbrb. have Hbrb_copy := Hbrb. move:Hbrb. simpl.
    move=>/bigcup_seqP [occ Hoccinrule].
    move=>/andP [/imsetP [brb Hbrb Hbreq]] /setDP [Hocc1 Hocc2].
    assert (Hdomvs : v \in dom s).
    rewrite -Hseq Hseqb.
    apply (subsetP (match_vars_subset Hsbmatch)).
    rewrite -Hcleqb Hcleq. apply Hvin.
    rewrite in_set in Hdomvs.
    destruct (sub_elim s v) as [[c Hc]|Hnone];
      try by rewrite Hnone in Hdomvs.
    apply/existsP. exists c. apply/andP;split. apply/eqP/Hc.
    destruct (nth_error_case descst (b_ind occ))
      as [Hnone|[[ga| [cld sd] descsd] [Hdin Hdnth]]]. by rewrite Hnone in_set0 in Hbrb.
    - rewrite Hdnth in Hbrb.
      rewrite (set1P Hbrb) in Hbreq.
      simpl in Hbreq. 
      assert (Hwub : @wu_pred _ _ bn (ABLeaf rul_gr_finType ga)). auto. 
      assert (Hsubtree : subtree (val {| wht := (ABLeaf rul_gr_finType ga); Hwht := Hwub |}) (val {| wht := ABNode (RS clt st) descst; Hwht := Htr |})).
      simpl. apply/hasP. exists (ABLeaf rul_gr_finType ga). apply Hdin. by apply/eqP.
      have Hgain  := sem_t_leaf (trace_sem_prev_trees Hded_copy Hsubtree).
      apply/existsP. exists ga. apply/andP;split. apply Hgain.
      unfold ded_sub_equal in Hdedsub.
      rewrite Hdescseq in Hdnth. destruct (nth_error_preim Hdnth) as [trb [Htrb1 Htrb2]].
      have Heqb := (nth_error_map (ded def) Htrb1).
      assert (Heqt : trb = {| wht := (ABLeaf rul_gr_finType ga); Hwht := Hwub |}).
      apply/val_inj. apply Htrb2.
      rewrite Heqt in Heqb. unfold ded at 2 in Heqb. simpl in Heqb.
      rewrite Hbreq. simpl. unfold p_at.
      have Hoccsrule := occsInProgramV Hocc1.
      unfold t_at in Hoccsrule.
      simpl. unfold at_at. unfold at_at in Hoccsrule.
      destruct (nth_error_case p (r_ind occ)) as [Hnone|[d [Hd1 Hd2]]]. by rewrite Hnone in Hoccsrule.
      rewrite Hd2 in Hoccsrule. rewrite Hd2. 
      destruct (nth_error_case (body_cl d) (b_ind occ)) as [Hnone|[db [Hdb1 Hdb2]]]. 
      by rewrite Hnone in Hoccsrule.
      rewrite Hdb2 in Hoccsrule. rewrite Hdb2.
      have Heqtb := (nth_error_map (gr_atom_def def sb) Hdb2).
      assert (Hdeq : d = clb). apply/(@vns_cl_eq _ _ _ v).
      apply/bigcup_seqP. exists db. apply Hdb1. apply/andP;split;auto. 
      apply/bigcup_seqP. exists (Var v). destruct occ. apply (nth_error_in Hoccsrule). 
      apply/andP;split;auto. by apply/set1P. rewrite -Hcleqb Hcleq. apply Hvin. apply Hd1. 
      apply Hclbinp. apply Hvns. 
      simpl in Heqb.
      rewrite Hdeq -(eqP Hdedsub) Heqb in Heqtb.
      inversion Heqtb as [Hgasbeq].
      apply/andP;split.
      + by destruct ga as [[]]; destruct db as [[]].
      + simpl. destruct occ.
        rewrite (nth_map (Var v) def _ (nth_error_in_size Hoccsrule)) (nth_error_nth (Var v) Hoccsrule).
        simpl. rewrite -Hseqb Hseq. unfold odflt. unfold oapp. by rewrite Hc.
    - assert (Hsubd : subtree (ABNode (RS cld sd) descsd) (ABNode (RS clt st) descst)).
      apply/orP;right. apply/hasP. exists (ABNode (RS cld sd) descsd). auto. by apply/orP;left.
      have Hwupred := (wu_pred_sub Hsubd Htr).
      assert (Hssubd : strict_subtree (val {| wht := (ABNode (RS cld sd) descsd); Hwht := Hwupred |}) (val {| wht := ABNode (RS clt st) descst; Hwht := Htr |})).
      apply/hasP. exists (ABNode (RS cld sd) descsd). auto. by apply/orP;left.
      have Hdedm1 := trace_sem_prev_trees_m1 Hded_copy Hssubd. simpl in Hdedm1.
      assert (Hrootd : ABroot (val {| wht := ABNode (RS cld sd) descsd; Hwht := Hwupred |}) =
       inl (RS cld sd)). auto.
      unfold ded_sub_equal in Hdedsub.
      rewrite Hdescseq in Hdnth. destruct (nth_error_preim Hdnth) as [trb [Htrb1 Htrb2]].
      have Heqb := (nth_error_map (ded def) Htrb1).
      assert (Heqt : trb = {| wht := ABNode (RS cld sd) descsd; Hwht := Hwupred |}).
      apply/val_inj. apply Htrb2.
      rewrite Heqt in Heqb. unfold ded at 2 in Heqb. simpl in Heqb.
      destruct cld as [hcld tlcld].
      (* rewrite Hbreq. simpl. unfold p_at.*)
      have Hoccsrule := occsInProgramV Hocc1. have Htat_copy := Hoccsrule.
      unfold t_at in Hoccsrule.
      (*rewrite Hocceq. simpl. unfold at_at.*) unfold at_at in Hoccsrule.
      destruct (nth_error_case p (r_ind occ)) as [Hnone|[d [Hd1 Hd2]]]. by rewrite Hnone in Hoccsrule.
      rewrite Hd2 in Hoccsrule. (*rewrite Hd2.*) 
      destruct (nth_error_case (body_cl d) (b_ind occ)) as [Hnone|[db [Hdb1 Hdb2]]]. 
      by rewrite Hnone in Hoccsrule.
      rewrite Hdb2 in Hoccsrule. (*rewrite Hdb2.*)
      have Heqtb := (nth_error_map (gr_atom_def def sb) Hdb2).
      assert (Hdeq : d = clb). apply/(@vns_cl_eq _ _ _ v).
      apply/bigcup_seqP. exists db. apply Hdb1. apply/andP;split;auto. 
      apply/bigcup_seqP. exists (Var v). destruct occ. apply (nth_error_in Hoccsrule). 
      apply/andP;split;auto. by apply/set1P. rewrite -Hcleqb Hcleq. apply Hvin. apply Hd1. 
      apply Hclbinp. apply Hvns.
      destruct occ as [occ Hocc]. simpl in Heqb.
      rewrite Hdeq -(eqP Hdedsub) Heqb in Heqtb.
      inversion Heqtb as [[Hgasymbeq Hgaargbeq]].
      have Hcldin := (tr_cl_in Hdedm1 Hrootd).
      assert (Hsveq : s v = sd (get_cl_var dt dv (Clause hcld tlcld) t_ind)
                   /\ nth_error (arg_atom hcld) t_ind = Some (Var (get_cl_var dt dv (Clause hcld tlcld) t_ind))).
      have H := (nth_error_map (gr_term_def def sb) Hoccsrule).
      rewrite -Hgaargbeq in H. unfold get_cl_var. simpl. 
      destruct (nth_error_preim H) as [[v'|c'] [H1' H2']]. split.
      rewrite (nth_error_nth _ H1') (gr_term_def_eq_in_dom H2'). by rewrite -Hseq Hseqb.
      destruct (existsP (trace_sem_head_match Hpsafe Hdedm1)) as [x Hx].
      apply (subsetP (match_vars_subset Hx)).
      apply/(subsetP (allP Hpsafe _ Hcldin)).
      apply/bigcup_seqP. exists (Var v'). apply (nth_error_in H1'). apply/andP;split;auto.
      by apply/set1P. 
      apply (subsetP (match_vars_subset Hsbmatch)). rewrite -Hcleqb Hcleq. apply Hvin.
      rewrite (nth_error_nth _ H1'). apply H1'. 
      have Hf := (allP (allP Hvarshead _ Hcldin) _ (nth_error_in H1')). inversion Hf.
      destruct Hsveq as [Hv1' Hv2'].
      assert (Hnewintail : (get_cl_var dt dv (Clause hcld tlcld) t_ind) \in tail_vars tlcld).
      apply (subsetP (allP Hpsafe _ Hcldin)).
      apply/bigcup_seqP. exists (Var (get_cl_var dt dv (Clause hcld tlcld) t_ind)). 
      apply (nth_error_in Hv2'). apply/andP;split;auto.
      by apply/set1P.
      rewrite Hdescseq (nth_error_map val Htrb1) Heqt in Hbrb. simpl in Hbrb. 
     (* helping unification *)
      assert (Hbrbin : brb
           \in unrec_trace_gen ({| r_ind := occ; b_ind := Hocc; t_ind := t_ind |} |: prev)
                 (val  {|  wht := ABNode (RS (Clause hcld tlcld) sd) descsd; Hwht := Hwupred |})
                 (get_cl_var dt dv (Clause hcld tlcld) t_ind) (@foldr nat nat maxn O
                 (@map (ABtree rul_gr gatom) nat (@ABheight rul_gr gatom) (@map
                 (@WUtree (Finite.eqType rul_gr_finType) (Finite.eqType gatom_finType) bn)
                 (ABtree rul_gr gatom) (@wht (Finite.eqType rul_gr_finType)
                 (Finite.eqType gatom_finType) bn) (@tval (@size atom  (@wlist_to_seq_co atom bn (body_cl clb)))
                 (@WUtree (Finite.eqType rul_gr_finType) (Finite.eqType gatom_finType) bn) descs)))).+1).
      apply Hbrb.
      have Hbrbprev := (unrec_trace_gen_normal_form Hbrbin). clear Hbrb. clear Hbrbin.
      have Hdisj := implyP (forallP (unrec_trace_gen_notin _ _ _ _) _) Hbrbprev.
      move:Hbreq. unfold pucons. destruct sumbool_of_bool as [Hin|Hin].
      + move=>/= ->. 
        have Hreced := implyP (forallP ((@Hrec _ sd _ _ _ Hvns) Hpsafe Hvarshead Hdedm1 Hrootd Hnewintail) brb) Hbrbprev.
        apply/existsP.
        simpl in Hreced.
        destruct (existsP Hreced) as [c' Hc']. destruct (andP Hc') as [Hc1' Hc2']. clear Hc'. clear Hreced.
        destruct (existsP Hc2') as [ga Hga]. destruct (andP Hga) as [Hga1 Hga2]. destruct (andP Hga2) as [Hga3 Hga4].
        clear Hga2. clear Hc2'. clear Hga. exists ga. 
        destruct (bool_des_rew ({| r_ind := occ; b_ind := Hocc; t_ind := t_ind |} \in 
                (@mem (Equality.sort (Choice.eqType (Finite.choiceType (t_occ_finType p))))
                 (seq_predType (Choice.eqType (Finite.choiceType (t_occ_finType p))))
                 (@useq (Choice.eqType (Finite.choiceType (t_occ_finType p))) brb)))) as [Hf|Hf].
        - assert (Hff : ({| r_ind := occ; b_ind := Hocc; t_ind := t_ind |} \in (@set0 (t_occ_finType p)))).
          rewrite -(disjoint_setI0 Hdisj). apply/setIP;split.
          rewrite in_set. apply Hf.
          apply setU11. by rewrite in_set0 in Hff.
          assert (Hsize : 0 < size brb).
          destruct brb as [[|]];auto.
          move:Hbrbprev. move=>/= /bigcup_seqP [i1 Hi1inenum /andP [/imsetP [x]]].
          destruct (nth_error_case descsd (b_ind i1)) as [Hnone|[[|] [Hdd1 Hdd2]]].
          + by rewrite Hnone in_set0.
          + rewrite Hdd2. move=>/set1P -> //.
          + rewrite Hdd2. destruct s0. move=>Hxunrec.
            unfold pucons. 
            (* helping unification *)
            assert (Hxunrecb : 
                x \in unrec_trace_gen (@setU (t_occ_finType p) (@set1 (t_occ_finType p)  i1)
               (@setU (t_occ_finType p) (@set1 (t_occ_finType p) {| r_ind := occ; b_ind := Hocc; t_ind := t_ind |})
               prev)) (ABNode (RS c0 s0) l) (get_cl_var dt dv c0 (occurrences.t_ind i1)) (@foldr nat nat maxn O
               (@map (ABtree rul_gr gatom) nat (@ABheight rul_gr gatom) descsd)).+1).
            apply Hxunrec.
            have Hdisjb := implyP (forallP (unrec_trace_gen_notin _ _ _ _) _) Hxunrecb.
            clear Hxunrecb. clear Hxunrec. destruct sumbool_of_bool as [Hfff|Hfff];move=>//.
            assert (Hff : (i1 \in (@set0 (t_occ_finType p)))).
            rewrite -(disjoint_setI0 Hdisjb). apply/setIP;split.
            rewrite in_set. destruct (bool_des_rew ((@in_mem (Equality.sort (Choice.eqType (Finite.choiceType (t_occ_finType p))))
               i1
               (@mem (Equality.sort (Choice.eqType (Finite.choiceType (t_occ_finType p))))
                  (seq_predType (Choice.eqType (Finite.choiceType (t_occ_finType p))))
                  (@useq (Choice.eqType (Finite.choiceType (t_occ_finType p))) x))))) as [Hf5|Hf5].
            by rewrite Hf5 in Hfff. by rewrite Hf5 in Hfff. apply setU11. by rewrite in_set0 in Hff.
          apply/and3P;split. apply Hga1.
          rewrite (eqP Hga3).
          apply/eqP/branch_pred_eq/Hsize. 
          rewrite -(branch_t_ind_eq {| r_ind := occ; b_ind := Hocc; t_ind := t_ind |} Hsize) (eqP Hga4).
          assert (Hsome : Some c' = Some c).
          rewrite -Hc -(eqP Hc1'). auto. by inversion Hsome.
        - assert (Hff : ({| r_ind := occ; b_ind := Hocc; t_ind := t_ind |} \in (@set0 (t_occ_finType p)))).
          rewrite -(disjoint_setI0 Hdisj). apply/setIP;split.
          rewrite in_set.  
          destruct (bool_des_rew (@in_mem (Equality.sort (Choice.eqType (Finite.choiceType (t_occ_finType p))))
              {| r_ind := occ; b_ind := Hocc; t_ind := t_ind |}
              (@mem (Equality.sort (Choice.eqType (Finite.choiceType (t_occ_finType p))))
                 (seq_predType (Choice.eqType (Finite.choiceType (t_occ_finType p))))
                 (@useq (Choice.eqType (Finite.choiceType (t_occ_finType p))) brb)))) as [Hf|Hf].
          apply Hf. by rewrite Hf in Hin.
          apply setU11. by rewrite in_set0 in Hff.
Qed.

End no_rec_traces.