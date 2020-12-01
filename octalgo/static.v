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

Require Import fintrees.
Require Import syntax.
Require Import occurrences.
Require Import subs.
Require Import pmatch.
Require Import bSemantics.
Require Import tSemantics.
Require Import monotonicity.
Require Import soundness.
Require Import norec_sem.

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset bigop finfun.

Require Import bigop_aux.
Require Import utils.
Require Import finseqs.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Static analysis of a Datalog program *)
Section analysis.

(** program to analyze *)
Variable p : program.

(** default term and variable for the nth function *)
Variable dt : term.
Variable dv : 'I_n.

(** ** The actual analysis *)
Section rules.

Definition bigcup_tup {m} {A : finType} (t : m.-tuple {set A}) : {set A} :=
  \bigcup_(x <- tval t) x.

Definition bigcup_cart {m} {A : finType} (s : {set m.-tuple {set A}}) : {set {set A}} :=
  [set bigcup_tup y | y : m.-tuple {set A} in s].

(** [prev]  is the set of tocs already visited
    [v]     is the analyzed variable 
    [count] is the fuel, used for termination
    The analysis is returned as a DNF, encoded as a set of set of uniq_seqs of toccs.
    The "outer set" represents the disjunction, whereas the "inner sets" are the conjunctions  *)
Fixpoint analyze_var_prev (prev : (tocs p)) (v : 'I_n) (count : nat) : {set {set (dbranch p)}} :=
  match count with | 0 => set0 | count.+1 =>
    (* computing the occurrences of v that have not been previously visited *)
    let occs := occsInProgram p v :\: prev in
    let analyze_pi (prev : tocs p) (o : t_occ p) :=
        (* predicate of the atom at the occurrence*)
        match p_at o with
           (* the None case does not occur in practice
              (guaranteed by occsInProgramV in occurrences.v *)
         | None => set0
         | Some f => 
            match predtype f with
              | Edb => [set [set unil]]
              | Idb =>  let arec := [set (analyze_var_prev prev (get_cl_var dt dv cl (t_ind o))) count | cl in p & hsym_cl cl == f] 
                        in \bigcup_(x in arec) x
          end
        end
    in
      let all_add_o (dt : {set {set (dbranch p)}}) (o : t_occ p) : {set {set (dbranch p)}}:=
        [set [set pucons o br | br in pred_of_set ct] | ct in dt]
      in
      let arec := [seq all_add_o (analyze_pi (occ |: prev) occ) occ | occ <- enum occs]
    in bigcup_cart (gen_cart_prod arec) end.

Definition analyze_var (v : 'I_n) (count : nat) :=
  analyze_var_prev set0 v count.

End rules.

(** ** Completeness results on the analysis *)
Section completeness.

(** default t_occ for the nth function 
    (should not be necessary with tnth_map) *)
Variable docc : t_occ p.

(** ** the content of any sequence in the result of an analysis is disjoint
    from the given set of previously visited toccs *)
Lemma analyze_disj (prev : (tocs p)) (v : 'I_n) (count : nat) :
  [forall ct in analyze_var_prev (prev : (tocs p)) (v : 'I_n) (count : nat),
    [forall br in pred_of_set ct, 
      [disjoint [set x | x \in (useq br)] & prev]]].
Proof.
move:v prev. induction count as [|count Hrec].
- intros. apply/forallP=>x. apply/implyP. by rewrite in_set0.
- move=>v prev.
  apply/forallP=>ct.
  apply/implyP=>/imsetP [[x Hxsize]].
  rewrite in_set. move=>H ->.
  apply/forallP=>br. 
  apply/implyP=>/bigcup_seqP [ctb] /= Hctbx /andP [Hbrctb _].
  have Hb := (seq_in_ind ctb Hctbx).
  rewrite (eqP Hxsize) in Hb. destruct Hb as [ctbi Hctbi].
  have Htmp := (forallP H ctbi). clear H. rewrite !(tnth_nth ctb) in Htmp.
  simpl in Htmp. rewrite Hctbi in Htmp. simpl in Htmp.
  rewrite (tnth_nth set0) in Htmp. simpl in Htmp.
  assert (Hctbisizeenum : ctbi < size (enum (occsInProgram p v :\: prev))).
  simpl;destruct ctbi as [ctbi Hctbize]; simpl; clear Hctbi; clear Htmp;
  rewrite size_map in Hctbize; apply Hctbize.
  rewrite (@nth_map _ docc _ set0 _ ctbi _) in Htmp;
  [|apply Hctbisizeenum]. 
  move:Htmp. move=>/imsetP [cti].
  unfold p_at. unfold at_at.
  destruct (nth_error_case p (r_ind (nth docc (enum (occsInProgram p v :\: prev)) ctbi)))
    as [Hnone|[d [Hd1 Hd2]]];try by rewrite Hnone in_set0.
  rewrite Hd2.
  destruct (nth_error_case (body_cl d) (b_ind (nth docc (enum (occsInProgram p v :\: prev)) ctbi)))
  as [Hnone|[a [Ha1 Ha2]]]; try by rewrite Hnone in_set0.
  rewrite Ha2.
  destruct (predtype (sym_atom a)).
  + move=>/set1P -> Hctb. move:Hbrctb.
    rewrite Hctb.
    move=>/imsetP [z /set1P -> ->].
    simpl. rewrite disjoints_subset.
    apply/subsetP=>zb. rewrite in_set mem_seq1.
    move=>/eqP ->. apply in_nth_P.
    apply/allP=>t. rewrite mem_enum in_set.
    move=>/andP[H1 H2]. rewrite -in_setC in H1. apply H1.
    apply Hctbisizeenum.
  + move=>/bigcup_seqP [k Hkenum /andP [Hctik /imsetP [ncl]]].
    rewrite in_set.
    move=>/andP [Hnclp Hnclsym] Hkeq Hctbeq.
    rewrite Hkeq in Hctik.
    rewrite Hctbeq in Hbrctb.
    move:Hbrctb.
    move=>/imsetP [xb Hxbin ->].
    rewrite disjoints_subset.
    apply/subsetP=>xt. rewrite in_set.
    unfold pucons.
    have Hrecdisj := implyP (forallP (implyP (forallP (Hrec _ _) _) Hctik) _) Hxbin.
    rewrite disjoints_subset in Hrecdisj.
    destruct Sumbool.sumbool_of_bool as [Hsum|Hsum].
    - simpl. rewrite in_cons. move=>/orP [/eqP ->|Hxt].
      + apply in_nth_P.
        apply/allP=>zt. rewrite mem_enum in_set.
        move=>/andP[Ht1 Ht2]. 
        rewrite -in_setC in Ht1. apply Ht1.
        apply Hctbisizeenum.
      + apply/(subsetP (subset_trans Hrecdisj _)).
        apply/subsetP=>m. rewrite !in_setC.
        destruct (bool_des_rew (m \notin prev)) as [Hm|Hm].
        - auto.
        - rewrite in_setU1.
          by rewrite (set_notin_f_in Hm) Bool.orb_true_r.
          rewrite in_set. apply Hxt.
    - move=>Hxt.
      have Htmp := (subsetP Hrecdisj (nth docc (enum (occsInProgram p v :\: prev))
          ctbi)).
      rewrite in_set in Htmp. have Htmp2 := Htmp (seq_notin_f_in Hsum).
      clear Htmp. rewrite in_setC in Htmp2. unfold negb in Htmp2.
      rewrite in_setU1 eq_refl Bool.orb_true_l in Htmp2. inversion Htmp2.
Qed.

(** ** The analysis is monotonous wrt. its fuel *)
Lemma analyze_incr prev v (m1 m2 : nat) :
  m1 <= m2 -> analyze_var_prev prev v m1 \subset analyze_var_prev prev v m2.
Proof.
move:m2 v prev.
induction m1 as [|m1 Hrec];
move=>[|m2] v prev // Hm12 /= ;[apply sub0set|].
apply/subsetP=>x /imsetP [[t Htsize]]. rewrite in_set.
move=>Ht ->. clear x.
apply/imsetP.
assert (Htsizeb : size t == (@size {set {set @uniq_seq (Finite.eqType (t_occ_finType p))}}
 [seq [set [set @pucons (t_occ_eqType p) occ br | br in pred_of_set ct] | ct in pred_of_set
  match @p_at p occ with | Some f => match  @fun_of_fin symtype (fun _ : Finite.sort symtype => pred_type)
  (Phant (Finite.sort symtype -> pred_type)) predtype f with| Edb => [set [set @unil (Finite.eqType (t_occ_finType p))]]
  | Idb => \big[@setU (set_of_finType (dbranch p))/@set0 (set_of_finType (dbranch p))]_(x in 
   pred_of_set [set analyze_var_prev (occ |: prev) (get_cl_var dt dv cl (@nat_of_ord
   (\max_(s in @sort_of_simpl_pred (Finite.sort symtype) (pred_of_argType (Finite.sort symtype)))
   @fun_of_fin symtype (fun _ : Finite.sort symtype => nat) (Phant (Finite.sort symtype -> nat)) arity s)
   (@t_ind p occ))) m2 | cl in pred_of_set [set cl in p | hsym_cl cl == f]]) x  end
   | None => @set0 (set_of_finType (@uniq_seq_finType (t_occ_finType p))) end] | occ <- enum
   (pred_of_set ((occsInProgram p v) :\: prev))])).
by rewrite (eqP Htsize) !size_map.
exists (Tuple Htsizeb);auto.
rewrite in_set. apply/forallP=>j.
assert (Hjsize : j < size (enum ((occsInProgram p v) :\: prev))).
destruct j as [j Hj]. simpl. by rewrite size_map in Hj.
rewrite (tnth_nth set0) (nth_map docc). simpl.
rewrite (tnth_nth set0). simpl.
assert (Hjb : j < (@size {set Finite.sort (set_of_finType (dbranch p))}
       [seq [set [set @pucons (t_occ_eqType p) occ br | br in pred_of_set ct]
        | ct in pred_of_set match @p_at p occ with | Some f => match
        @fun_of_fin symtype (fun _ : Finite.sort symtype => pred_type) (Phant (Finite.sort symtype -> pred_type)) predtype f
        with | Edb => [set [set @unil (Finite.eqType (t_occ_finType p))]] | Idb =>  \big[@setU (set_of_finType (dbranch p))/@set0
        (set_of_finType (dbranch p))]_(x in pred_of_set [set analyze_var_prev (occ |: prev) (get_cl_var dt dv cl
        (@nat_of_ord (\max_(s in @sort_of_simpl_pred (Finite.sort symtype) (pred_of_argType (Finite.sort symtype)))
        @fun_of_fin symtype (fun _ : Finite.sort symtype => nat) (Phant (Finite.sort symtype -> nat)) arity s)
        (@t_ind p occ))) m1 | cl in pred_of_set [set cl in p | hsym_cl cl == f]]) x end
         | None => @set0 (set_of_finType (@uniq_seq_finType (t_occ_finType p))) end] | occ <- enum
         (pred_of_set ((occsInProgram p v) :\: prev))])).
destruct j. simpl. rewrite size_map. apply Hjsize.
have H := forallP Ht (Ordinal Hjb). 
rewrite (tnth_nth set0) (nth_map docc) in H. simpl in H.
rewrite (tnth_nth set0) in H. simpl in H.
move:H. move=>/imsetP [x Hx Hxeq].
apply/imsetP. exists x;auto.
move:Hx.
destruct p_at;[|by rewrite in_set0].
destruct (predtype s). 
move=>/set1P ->. by apply/set1P.
move=>/bigcupP [y /imsetP [cl Hclin Hyeq] Hxanalyze].
apply/bigcupP. exists (analyze_var_prev (nth docc (enum ((occsInProgram p v) :\: prev)) j |: prev)
       (get_cl_var dt dv cl (t_ind (nth docc (enum ((occsInProgram p v) :\: prev)) j))) m2);auto.
apply/imsetP. 
exists cl. apply Hclin. reflexivity.
rewrite Hyeq in Hxanalyze. 
apply (subsetP (Hrec m2 _ _ Hm12) x Hxanalyze).
apply Hjsize. apply Hjsize.
Qed.

(** default ground atom and predicate for the nth function *)
Variable gat_def : gatom.
Variable df : symtype.

(** *** Core result: any no recursion trace is captured by the analysis *)
Lemma no_rec_capt def prev (tr : trace_sem_trees gat_def) (i : interp) (m : nat) cl s v :
   vars_not_shared p
-> prog_safe p
-> prog_safe_hds p
-> safe_edb i
-> only_variables_in_heads p
-> tr \in sem_t p gat_def def m i
-> ABroot (val tr) = inl (RS cl s)
-> v \in tail_vars (body_cl cl)
-> unrec_trace_gen dt dv prev (val tr) v (ABheight (val tr)).+1 \in analyze_var_prev prev v (ABheight (val tr)).
Proof.
move:cl s v tr prev.
induction m as [|m Hrec].
- move=>/= cl s v tr prev Hvns Hpsafe Hpsafehds Hsafeedb Hvarshead /imsetP [x Hx ->] //.
- move=> cl s v tr prev Hvns Hpsafe Hpsafehds Hsafeedb  Hvarshead Hded. have Hded_copy := Hded. move:Hded. 
  move=>/setUP [Hded|/bigcup_seqP [clb Hclbinp /andP [H _]]].
  + by apply/Hrec.
  + destruct (imset2P (mem_pset_set H))
      as [descs sb Hdescsded Hsmatch Htreq]. clear H.
    destruct tr as [[|[clt st] descst] Htr];
    move=>// [Hcleq Hseq] Hvin.
    unfold wu_pcons_seq in Htreq.
    unfold wu_pcons_wlist in Htreq. move:Htreq.
    destruct Sumbool.sumbool_of_bool;move=> //[Hcleqb Hseqb Hdescseq].
    assert (Hdescssize : size descs <= bn).
    destruct descs as [descs Hdescs]. rewrite (eqP Hdescs).
    destruct clb. apply wlist_to_seq_size. 
    rewrite (seq_wlistK Hdescssize) in Hdescseq.
    (* cl = clb = clt, s = sb = st and descs = descst *)
    rewrite in_set in Hsmatch.
    destruct (and3P Hsmatch) as [Hsbmatch Hdedsub Hprevded]. clear Hsmatch.
    simpl.
    assert (Hsizedescs : size descs = size (body_cl cl)).
    unfold ded_sub_equal in Hdedsub.
    by rewrite -(size_map (ded (gat_def:=gat_def) def)) -Hcleq Hcleqb (eqP Hdedsub) size_map.
    apply/imsetP.
    pose dct : seq ({set dbranch p}) := 
      [seq [set pucons occ l | l in pred_of_set match nth_error descst (b_ind occ) with
        | Some (@ABLeaf _ _ _) => [set unil]
        | Some (ABNode (RS clb0 _) descsb) =>  \big[setU (T:=uniq_seq_finType)/set0]_(occ0 in occsInProgram p
          (get_cl_var dt dv clb0 (t_ind occ)) :\: (occ |: prev)) [set pucons occ0 l
            | l in pred_of_set match nth_error descsb (b_ind occ0) with  | Some (@ABLeaf _ _ _) => [set unil]
              | Some (ABNode (RS clb1 sb1) descsb0) => unrec_trace_gen (p:=p) dt dv (occ0 |: (occ |: prev))
               (ABNode (RS clb1 sb1) descsb0) (get_cl_var dt dv clb1 (t_ind occ0))  (foldr maxn 0 [seq ABheight i | i <- descst])
                | None => set0 end]  | None => set0 end] | occ <- enum ((occsInProgram p v) :\: prev)].
    assert (Htsize : size dct == (@size {set {set @uniq_seq (Finite.eqType (t_occ_finType p))}}
              [seq [set [set @pucons (t_occ_eqType p) occ br | br in pred_of_set ct]
                      | ct in pred_of_set match @p_at p occ with | Some f =>
                    match @fun_of_fin symtype (fun _ : Finite.sort symtype => pred_type)
                    (Phant (Finite.sort symtype -> pred_type)) predtype f with
                      | Edb => [set [set @unil (Finite.eqType (t_occ_finType p))]]
                      | Idb => \big[@setU (set_of_finType (dbranch p))/@set0 (set_of_finType (dbranch p))]_(x in 
                               pred_of_set [set analyze_var_prev (occ |: prev) (get_cl_var dt dv cl0 (@nat_of_ord
                              (\max_(s0 in @sort_of_simpl_pred (Finite.sort symtype) (pred_of_argType (Finite.sort symtype)))
                              @fun_of_fin symtype (fun _ : Finite.sort symtype => nat) (Phant (Finite.sort symtype -> nat)) arity s0) 
                              (@t_ind p occ))) (@foldr nat nat maxn 0 [seq @ABheight rul_gr gatom i | i <- descst])
                              | cl0 in pred_of_set [set cl0 in p | hsym_cl cl0 == f]]) x  end
                                | None => @set0 (set_of_finType (@uniq_seq_finType (t_occ_finType p)))  end]
                 | occ <- enum (pred_of_set ((occsInProgram p v) :\: prev))])).
    by rewrite !size_map -cardE.
    exists (Tuple Htsize).
    - rewrite in_set. apply/forallP=>j.
      assert (Hjsize : j < size (enum ((occsInProgram p v) :\: prev))).
      destruct j as [j Hj]. simpl. by rewrite size_map in Hj.
      rewrite (tnth_nth set0) (nth_map docc);[|apply Hjsize]. unfold dct. 
      rewrite (tnth_nth set0). simpl.
      apply/imsetP.
      assert (Hnthv : t_at (nth docc (enum ((occsInProgram p v) :\: prev)) j) == Some (Var v)).
      apply (@in_nth_P _ docc (enum ((occsInProgram p v) :\: prev)) (fun x => t_at x == Some (Var v)) j).
      apply/allP=>x. rewrite mem_enum in_set. move=>/andP [H1 H2]. apply/eqP/occsInProgramV/H2. apply Hjsize.
      unfold t_at in Hnthv. unfold at_at in Hnthv.
      unfold p_at. unfold at_at.
      destruct (nth_error_case p (r_ind (nth docc (enum ((occsInProgram p v) :\: prev)) j)))
              as [Hnone|[ncl [Hncl1 Hncl2]]];[by rewrite Hnone in Hnthv|].
      rewrite Hncl2. rewrite Hncl2 in Hnthv.
      destruct (nth_error_case (body_cl ncl) (b_ind (nth docc (enum ((occsInProgram p v) :\: prev)) j)))
              as [Hnone|[na [Hna1 Hna2]]];[by rewrite Hnone in Hnthv|].
      rewrite Hna2 in Hnthv. rewrite Hna2.
      assert (Hclneq : ncl = clb).
      apply/vns_cl_eq. 
      apply/bigcup_seqP. exists na. apply Hna1. apply/andP;split;auto.
      apply/bigcup_seqP. exists (Var v). destruct (nth docc (enum ((occsInProgram p v) :\: prev)) j).
      apply (nth_error_in (eqP Hnthv)). apply/andP;split;auto.
      rewrite in_set. apply eq_refl.
      rewrite -Hcleqb Hcleq. apply Hvin. apply Hncl1. auto. auto.
      unfold ded_sub_equal in Hdedsub. 
      have H := nth_error_map (gr_atom_def def sb) Hna2.
      rewrite Hclneq -(eqP Hdedsub) in H. 
      destruct (nth_error_preim H) as [trd [Htrd1 Htrd2]]. 
      assert (Hnewtrded : trd \in sem_t p gat_def def m.+1.-1 i).
      apply/(trace_sem_prev_trees_m1 Hded_copy). simpl. apply/hasP. exists (wht trd).
      rewrite Hdescseq. apply/mapP. exists trd. apply (nth_error_in Htrd1). reflexivity.
      apply subtree_refl.
      destruct trd as [[ga|[cld sd] descsd] Htrd].
      + assert (Hpt : predtype (sym_atom na) = Edb).
        rewrite -(eqP (implyP (forallP Hsafeedb _) (sem_t_leaf Hnewtrded))).
        unfold ded in Htrd2.
        simpl in Htrd2. rewrite Htrd2. by destruct na as [[]]. 
        rewrite Hpt. exists [set unil].
        by apply/set1P.
        rewrite (nth_map docc).
        apply/eqP;rewrite eqEsubset;apply/andP;split;apply/subsetP=>tu.
        - move=>/imsetP [x]. rewrite {1}Hdescseq (nth_error_map _ Htrd1). simpl.
          move=>/set1P -> ->. apply/imsetP. exists unil. by apply/set1P.
          reflexivity.
        - move=>/imsetP [x /set1P ->] ->.
          apply/imsetP. 
          rewrite {1}Hdescseq (nth_error_map _ Htrd1). simpl.
          exists unil. by apply/set1P. reflexivity. auto.
      + assert (Hrootd : ABroot (val {| wht := ABNode (RS cld sd) descsd; Hwht := Htrd |}) = inl (RS cld sd)). auto.
        have Hcldin := tr_cl_in Hnewtrded Hrootd.
        assert (Hpt : predtype (sym_atom na) = Idb). 
        unfold ded in Htrd2. simpl in Htrd2.
        destruct cld as [hcld tlcld].
        inversion Htrd2 as [[Hfeq Haeq]].
        apply/eqP/(allP Hpsafehds (Clause hcld tlcld)). auto.
        rewrite Hpt.
        assert (Hnvin : get_cl_var dt dv cld (t_ind (nth docc (enum ((occsInProgram p v) :\: prev)) j))
         \in tail_vars (body_cl cld)).
        apply (subsetP (allP Hpsafe cld Hcldin)). 
        apply/bigcup_seqP. 
        exists (Var (get_cl_var dt dv cld (t_ind (nth docc (enum ((occsInProgram p v) :\: prev)) j)))).
        apply/get_cl_var_leq. apply (allP Hvarshead _ Hcldin).
        unfold get_cl_var. destruct cld as [hcld tlcld]. simpl. 
        unfold ded in Htrd2. simpl in Htrd2. 
        assert (Hsize : size (arg_atom hcld) = size (arg_atom na)).
        destruct hcld as [[]];destruct na as [[]];inversion Htrd2. simpl.
        rewrite -(size_map (gr_term_def def sd)) -(size_map (gr_term_def def sb)). by rewrite H2.
        rewrite Hsize. apply/nth_error_in_size. move: (eqP Hnthv). destruct nth. simpl. move=>Ht. apply Ht.
        apply/andP;split;auto.
        by apply/set1P.
        exists (unrec_trace_gen (p:=p) dt dv
         (nth docc (enum ((occsInProgram p v) :\: prev)) j |: prev)
         (val {| wht := ABNode (RS cld sd) descsd; Hwht := Htrd |})
         (get_cl_var dt dv cld (t_ind (nth docc (enum ((occsInProgram p v) :\: prev)) j)))
         (ABheight (val {| wht := ABNode (RS cld sd) descsd; Hwht := Htrd |})).+1).
        - apply/bigcupP. eexists. apply/imsetP. exists cld.
          rewrite in_set. apply/andP;split. apply Hcldin.
          unfold ded in Htrd2. simpl in Htrd2. destruct cld.  
          destruct a as [[]]; destruct na as [[]]; inversion Htrd2. simpl.
          unfold hsym_cl. simpl. by rewrite H1.
          reflexivity. 

          have Hrecd := (Hrec cld sd (get_cl_var dt dv cld (t_ind (nth docc (enum ((occsInProgram p v) :\: prev)) j)))
                   {| wht := ABNode (RS cld sd) descsd; Hwht := Htrd |} 
                   (nth docc (enum ((occsInProgram p v) :\: prev)) j |: prev)
                   Hvns Hpsafe Hpsafehds Hsafeedb Hvarshead Hnewtrded Hrootd Hnvin).
          apply/(subsetP (analyze_incr _ _ _) _ Hrecd). 
          assert (Hsizeb : ABheight (ABNode (RS cld sd) descsd) < ABheight ( (ABNode (RS clt st) descst))).
          apply sstree_height. apply/hasP. exists (ABNode (RS cld sd) descsd). rewrite Hdescseq. apply/mapP.
          exists {| wht := ABNode (RS cld sd) descsd; Hwht := Htrd |}. apply (nth_error_in Htrd1). auto. apply subtree_refl.
          apply Hsizeb.
        - rewrite (nth_map docc);auto. simpl.
          apply/eqP.
          rewrite eqEsubset. apply/andP;split;apply/subsetP=>x.
          + move=>/imsetP [y]. rewrite {1}Hdescseq (nth_error_map _ Htrd1). simpl.
            move=>Hy ->. apply/imsetP. exists y.
             assert (Hyb : y \in unrec_trace_gen dt dv (nth docc (enum ((occsInProgram p v) :\: prev)) j |: prev)
                                              (ABNode (RS cld sd) descsd) 
                                              (get_cl_var dt dv cld (t_ind (nth docc (enum ((occsInProgram p v) :\: prev)) j))) 
                                              (ABheight (ABNode (RS clt st) descst))). apply Hy.
            clear Hy.
            apply (unrec_trace_gen_normal_form Hyb). reflexivity.
          + move=>/imsetP [y Hy ->].
            apply/imsetP. exists y. rewrite {1}Hdescseq (nth_error_map _ Htrd1). simpl.
            apply (@unrec_trace_gen_count_incr p dt dv (nth docc (enum ((occsInProgram p v) :\: prev)) j |: prev)
                                              (ABNode (RS cld sd) descsd)
                                              (get_cl_var dt dv cld (t_ind (nth docc (enum ((occsInProgram p v) :\: prev)) j)))
                                              (ABheight (ABNode (RS cld sd) descsd)).+1 (ABheight (ABNode (RS clt st) descst))).
            apply sstree_height. apply/hasP. exists (ABNode (RS cld sd) descsd). rewrite Hdescseq. apply/mapP.
            exists {| wht := ABNode (RS cld sd) descsd; Hwht := Htrd |}. apply (nth_error_in Htrd1). auto. apply subtree_refl.
            apply Hy. reflexivity.
    - apply/eqP.
      rewrite eqEsubset. apply/andP;split;apply/subsetP=>x.
      + move=>/bigcupP [y /setDP [Hyin Hynotin] Hx]. apply/bigcup_seqP.
        eexists. simpl. unfold dct. apply/mapP. exists y.
        rewrite mem_enum in_set. by apply/andP;split.
        reflexivity. apply/andP;split;auto.
      + move=>/bigcup_seqP [y /=]. unfold dct.
        move=>/mapP [z Hzin ->] /andP[Hxy _].
        apply/bigcupP. exists z. rewrite mem_enum in_set in Hzin.
        destruct (andP Hzin); by apply/setDP;split.
        apply Hxy.
Qed.

(** *** Any no recursion trace is captured in by the analysis with bounded fuel
        and empty [prev] *)
Theorem no_rec_capt_nf def (tr : trace_sem_trees gat_def) (i : interp) (m : nat) cl s v :
   vars_not_shared p
-> prog_safe p
-> prog_safe_hds p
-> safe_edb i
-> only_variables_in_heads p
-> tr \in sem_t p gat_def def m i
-> ABroot (val tr) = inl (RS cl s)
-> v \in tail_vars (body_cl cl)
-> unrec_trace p dt dv (val tr) v (ABheight (val tr)).+1 \in analyze_var v #|rul_gr_finType|.
Proof.
move=>H1 H2 H3 H4 H5 H6 H7 H8.
have H := no_rec_capt set0 H1 H2 H3 H4 H5 H6 H7 H8.
apply/(subsetP (analyze_incr _ _ _) _ H).
assert (H9 : val tr = wht tr). by destruct tr.
rewrite H9.
apply (height_WUtree tr).
Qed.

End completeness.

End analysis.
