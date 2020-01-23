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
Require Import tSemantics .
Require Import monotonicity.
Require Import soundness.
Require Import dTypes.
Require Import ddTypes.
Require Import rules.
Require Import depsubs.

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset bigop finfun.

Require Import bigop_aux.
Require Import utils.
Require Import finseqs.
Require Import fintrees.

Require Import Coq.Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Technical lemmas for the completeness of depsubs *)
Section dep_completeness.

(** [i] is a safe interpretation (only on the EDB) *)
Variable i : interp.
Hypothesis isafe : safe_edb i.

(** [p] is a safe program, with safe heads (only IDB) that
  does not share variables between clauses. *)
Variable p : program.
Hypothesis psafe : prog_safe p.
Hypothesis phsafe : prog_safe_hds p.
Hypothesis pvars : vars_not_shared p.

(** assuming a typing to study *)
Variable c_var_typing : forall v, var_type p v.

(** default ground atom and variable *)
Variable dga : gatom_finType.
Variable dv  : 'I_n.

(** ** Monotonocity lemmas *)
Section monotonicity.

(** Augmenting [s1] with new bindings (giving [s2]) preserves
  [ga_match_br] *)
Lemma ga_match_br_mon (ga : gatom) (br : seq (t_occ_finType p)) (v : 'I_n)
                      (s1 s2 : sub) :
   s1 \sub s2
-> ga_match_br ga br v s1
-> ga_match_br ga br v s2.
Proof.
unfold ga_match_br.
destruct br as [|];auto.
move=>Hsub.
destruct (sub_elim s1 v) as [[c Hc]|Hc];
rewrite Hc;auto.
have Hsubb := forallP Hsub v.
rewrite Hc in Hsubb.
rewrite mem_bindE in Hsubb.
by rewrite (eqP Hsubb).
Qed.

(** If [s1] in [dep_subs_cl i c_var_typing cl] so is
  any [s2] with new bindings. *)
Lemma dep_subs_cl_mon (cl : clause) (s1 s2 : sub) :
    s1 \sub s2 ->
    s1 \in dep_subs_cl i c_var_typing cl
 -> s2 \in dep_subs_cl i c_var_typing cl.
Proof.
move=>Hsub /bigcupP [tup H1 H2].
apply/bigcupP. exists tup. apply H1.
rewrite in_set in H2. rewrite in_set.
apply/forallP=>par. apply/implyP=>H3.
destruct (existsP (implyP (forallP H2 par) H3))
  as [ga H4]. destruct (andP H4) as [H5 H6].
apply/existsP. exists ga. apply/andP;split.
apply H5. apply/forallP=>vbb. apply/implyP=>H7.
apply (ga_match_br_mon Hsub (implyP (forallP H6 vbb) H7)).
Qed.

(** This can be generalized to the full program *)
Lemma dep_subs_mon (s1 s2 : sub) :
  s1 \sub s2 ->
  s1 \in dep_subs i c_var_typing -> s2 \in dep_subs i c_var_typing.
Proof.
move=>Hsub /bigcupP [cl H1 H2].
apply/bigcupP. exists cl.
apply H1. apply (dep_subs_cl_mon Hsub H2).
Qed.

End monotonicity.

(** ** Properties between branches *)
Section bbranches.

(** Given a branch, access the clause at the head of it if any.*)
Definition br_rind (br : dbranch p) : option clause :=
  match br with
    | {| useq := useq; buniq := x |} =>
      match useq as l return (uniq l -> option clause) with
        | [::] => fun _ : uniq [::] => None
        | h :: tl => fun _ : uniq (h :: tl) => nth_error p (r_ind h)
        end x
  end.

(** Given a set of branches, returns the clause each is associated with *)
Definition all_br_rinds (brs : {set dbranch p}) :=
  pmap br_rind (enum brs).

(** Returns the tail of a branch if it exists *)
Definition br_desc (br : dbranch p) : option (dbranch p) :=
match br with
| {| useq := useq; buniq := x |} =>
    match useq as l return (uniq l -> option (dbranch p)) with
    | [::] => fun _ : uniq [::] => None
    | h :: tl =>
        fun Hbr : uniq (h :: tl) =>
        let a : h \notin tl /\ uniq tl := andP Hbr in
        match a with
        | conj _ Htl => Some {| useq := tl; buniq := Htl |}
        end
    end x
end.

Coercion option_fin {A : finType} (x : option A) : option_finType A
 := x.

(** Returns the tails when they exist. *)
 Definition brs_descs (brs : {set dbranch p}) :=
  pset [set option_fin (br_desc x) | x in brs].

(** both branches are non_empty and the 2nd index of their heads match.
 It will be used to classify branches in groups that are on the same
 atom. *)
Definition br_h_b_eq {p'} (br1 br2 : dbranch p') : bool.
destruct br1 as [[|[a1 b1 c1] tl1] Hbr1];
destruct br2 as [[|[a2 b2 c2] tl2] Hbr2].
- apply false.
- apply false.
- apply false.
- apply (b1 == b2).
Defined.

(** [br_h_b_eq] is transitive *)
Lemma br_h_b_eq_trans {p'} (br1 br2 br3 : dbranch p') :
  br_h_b_eq br1 br2 -> br_h_b_eq br2 br3 -> br_h_b_eq br1 br3.
Proof.
destruct br1 as [[|[a1 b1 c1] tl1] Hbr1];
destruct br2 as [[|[a2 b2 c2] tl2] Hbr2];
destruct br3 as [[|[a3 b3 c3] tl3] Hbr3];auto.
move=> /= /eqP -> /eqP ->. by apply/eqP.
Qed.

(** vdep is reflexive *)
Lemma vdep_refl vbr : @vdep p vbr vbr.
Proof.
destruct vbr as [v [br Hbr]];simpl;unfold dep;simpl;clear Hbr.
induction br as [|h tl Hbr].
by apply/andP;split.
apply/andP;split;auto. apply/andP;split;auto. by destruct (andP Hbr).
Qed.

(** vdep is transitive and symmetric *)
Lemma vdep_congr vb1 vb2 vb3 :
  @vdep p vb1 vb2 -> @vdep p vb1 vb3 = @vdep p vb2 vb3.
Proof.
destruct vb1 as [v1 [br1 Hbr1]];
destruct vb2 as [v2 [br2 Hbr2]];
destruct vb3 as [v3 [br3 Hbr3]];
simpl;unfold dep;simpl.
clear Hbr1. clear Hbr2. clear Hbr3.
move:br2 br3.
induction br1 as [|h1 tl1 Hbr1];
destruct br2 as [|h2 tl2];
destruct br3 as [|h3 tl3];
 move=> /andP //=.
move=>[/eqP [H1] /andP [/eqP H2 H3]].
rewrite H1 H2.
assert (H:(size tl1 == size tl3) && all
         (fun x : t_occ p * t_occ p =>
          pred_occ x.1 == pred_occ x.2) (zip tl1 tl3) =
       (size tl2 == size tl3) && all
         (fun x : t_occ p * t_occ p =>
          pred_occ x.1 == pred_occ x.2) (zip tl2 tl3)).
apply/(@Hbr1 tl2 tl3)/andP;split;auto. by rewrite H1.
unfold andb in H.
destruct (bool_des_rew (size tl2 == size tl3)) as [Heq|Hneq].
rewrite H1 !Heq in H. by rewrite H.
assert (Hneqb : (size tl2).+1 == (size tl3).+1 = false).
by rewrite -Hneq.
by rewrite !Hneqb.
Qed.

(** Check that the head of the branch has the
  given atom index [k]. *)
Definition br_h_b_seq {p'} (br : seq (t_occ p')) (k : 'I_bn) : bool :=
match br with
| [::] => false
| {| b_ind := b |} :: _ => b == k end.

End bbranches.

(** ** Traces are captured by typing *)
Section trace_cap.

(** [vtr_brs_eq] the correspondance between a trace and a set of
   branches, checking at each level that the branches match the trace.
   The main idea is to decompose the branches in parts linked to a
   given atom and then call recursively [vtr_brs_eq] on the part
   of the trace corresponding to this atom and on the tail of the
   branches in the part.

   [count] should be equal to the height
   of the type tree which is also the maximal length of the branches.
   When anything wrong is found, the result will be [false]  *)
Fixpoint vtr_brs_eq {p'} (tr : (@ABtree rul_gr_finType gatom_finType)) (brs : {set dbranch p'})
                    (count : nat) {struct count} : bool:=
 (* called with height of tr *)
match count with 0 => false
| S count =>
  match tr with
  | ABLeaf ga =>
      [forall br in brs,
       (val br) == [::]]
  | ABNode (RS cl s) descs => [forall x in brs, size x > 0] &&
      [forall part in equivalence_partition br_h_b_eq brs,
        (* heads match the current clause cl *)
        [forall br in pred_of_set part,
             [exists brhd, (useq_hd br == Some brhd) && (nth_error p' (r_ind brhd) == Some cl)]]
     && [exists k : 'I_bn,
           (* naming the partition value *)
           [forall br in pred_of_set part, br_h_b_seq br k]
        && match nth_error descs k with
            | None => false
            | Some tr' => vtr_brs_eq tr' [set useq_behead x | x in pred_of_set part] count end]] end end.

(** [vtr_brs_eq] is decreasing when its given
    set of branches is increasing *)
Lemma vtr_brs_eq_decr_brs {p'} (tr : (@ABtree rul_gr_finType gatom_finType)) 
                            (brs1 brs2 : {set dbranch p'}) (h : nat)
  : vtr_brs_eq tr brs1 h -> brs2 \subset brs1 -> vtr_brs_eq tr brs2 h.
Proof.
move:brs1 brs2 h. 
apply (@abtree_ind_prop _ _ (fun tr => forall (brs1 brs2 : {set dbranch p'}) h,
  vtr_brs_eq tr brs1 h -> brs2 \subset brs1 -> vtr_brs_eq tr brs2 h)).
- move=> ga brs1 brs2 h.
  destruct h. auto. simpl.
  move=>/forallP H1 Hsub. apply/forallP=>br.
  apply/implyP=>H2. apply (implyP (H1 br)).
  apply (subset_to_in H2 Hsub).
- move=>[cl s] l Hrec brs1 brs2 h.
  unfold vtr_brs_eq.
  destruct h as [|h];auto.
  move=>/andP [H1 H2] Hsub.
  apply/andP;split.
  + apply/forallP=>x. apply/implyP=>Hx.
    apply (implyP (forallP H1 _)).
    apply (subset_to_in Hx Hsub).
  + apply/forallP=>x.
    apply/implyP=>Hx.
    destruct (existsP (implyP (forallP (equiv_part_set_mon br_h_b_eq Hsub) x) Hx))
      as [y Hy]. destruct (andP Hy) as [Hy1 Hy2]. clear Hy.
    destruct (andP (implyP (forallP H2 _) Hy1)) as [H3 H4]. clear H2.
    apply/andP;split.
    - apply/forallP=>br. apply/implyP=>Hbrin. apply/existsP. 
      destruct (existsP (implyP (forallP H3 _) (subset_to_in Hbrin Hy2)))
        as [brb Hbrb]. exists brb. apply Hbrb.
    - destruct (existsP H4) as [k Hk]. clear H4.
      apply/existsP. exists k. destruct (andP Hk) as [H5 H6].
      apply/andP;split.
      apply/forallP=>br. apply/implyP=>Hbr.
      apply (implyP (forallP H5 br) (subset_to_in Hbr Hy2)).
      move:H6. destruct (nth_error_case l k) as [Hnone|[c [Hc1 Hc2]]].
      by rewrite Hnone.
      rewrite Hc2. move=>H.
      apply (all_prop_in Hrec) with (brs3 := [set useq_behead x0 | x0 in pred_of_set y]).
      apply Hc1. apply H. 
      apply/subsetP=>z /imsetP [a Ha ->].
      apply/imsetP. exists a. apply (subset_to_in Ha Hy2). reflexivity.
Qed.

(** If we have found a count for which [vtr_brs_eq tr brs] is true,
  increasing the [count] value does not change the outcome *)
Lemma vtr_brs_eq_more {p'} (tr : (@ABtree rul_gr_finType gatom_finType)) (brs : {set dbranch p'}) (h1 h2 : nat)
  : vtr_brs_eq tr brs h1 -> h1 <= h2 -> vtr_brs_eq tr brs h2.
Proof.
move:brs h1 h2.
apply (@abtree_ind_prop _ _ (fun tr => forall brs h1 h2,
  vtr_brs_eq tr brs h1 -> h1 <= h2 -> vtr_brs_eq tr brs h2)).
move=>ga brs h1 h2.
destruct h1 as [|h1]. auto.
simpl. destruct h2 as [|h2]. simpl. move=>H Hf. inversion Hf.
simpl. auto.
move=> [cl s] l Hall brs h1 h2 Hprev Hsup.
destruct h1 as [|h1]. inversion Hprev.
destruct h2 as [|h2]. inversion Hsup.
simpl. simpl in Hprev.
destruct (andP Hprev) as [Hprev1 Hprev2]. clear Hprev.
apply/andP;split. apply Hprev1.
apply/forallP=>part. apply/implyP=>Hpartin.
destruct (andP (implyP (forallP Hprev2 part) Hpartin)) as [Hprev21 Hprev22].
clear Hprev2.
apply/andP;split.
apply Hprev21. destruct (existsP Hprev22) as [k Hk]. clear Hprev22.
destruct (andP Hk) as [Hk1 Hk2]. clear Hk.
apply/existsP. exists k. apply/andP;split. apply Hk1.
destruct (nth_error_case l k) as [Hnone|[trb [Htrbin Htrbeq]]].
by rewrite Hnone in Hk2.
rewrite Htrbeq. rewrite Htrbeq in Hk2.
apply (all_prop_in Hall (nth_error_in Htrbeq)) with (h1 := h1).
apply Hk2.
auto.
Qed.

(** If [vtr_brs_eq_height tr brs] will ever be valid, it will be valid
   for (ABheight tr). *)
Lemma vtr_brs_eq_height {p'} (tr : (@ABtree rul_gr_finType gatom_finType)) (brs : {set dbranch p'})
  : (exists h, vtr_brs_eq tr brs h) -> vtr_brs_eq tr brs (ABheight tr).+1.
Proof.
move:brs.
apply (@abtree_ind_prop _ _ (fun tr => forall brs,
  ((exists h, vtr_brs_eq tr brs h) -> vtr_brs_eq tr brs (ABheight tr).+1))).
move=> ga brs [[|h] Hh]. inversion Hh. apply Hh.
move=> [cl s] l Hprev brs [[|h] Hall]. inversion Hall.
simpl in Hall. destruct (andP Hall) as [Hall1 Hall2].
apply/andP;split. apply Hall1.
apply/forallP=>part. apply/implyP=>Hpartin.
destruct (andP (implyP (forallP Hall2 part) Hpartin)) as [Hall21 Hall22]. clear Hall2.
apply/andP;split. apply Hall21.
destruct (existsP Hall22) as [k Hk]. clear Hall22.
destruct (andP Hk) as [Hkall Hknth]. clear Hk.
apply/existsP. exists k. apply/andP;split. apply Hkall.
destruct (nth_error_case l k) as [Hnone|[trb [Htrbin Htrbeq]]]. by rewrite Hnone in Hknth.
rewrite Htrbeq in Hknth. rewrite Htrbeq.

assert (Htprev : (exists h : nat, vtr_brs_eq trb [set useq_behead x | x in pred_of_set part] h)).
exists h.
simpl. destruct h as [|h]. inversion Hknth. apply Hknth.
pose Hf := ((all_prop_in Hprev (nth_error_in Htrbeq)) _ Htprev). clearbody Hf.

apply (@vtr_brs_eq_more _ trb [set useq_behead x | x in pred_of_set part]
                          (ABheight trb).+1 (ABheight (ABNode (RS cl s) l))).
apply Hf. apply sstree_height. apply/hasP.
exists trb. apply Htrbin. apply subtree_refl.
Qed.

(** If no branches are given, the property is trivially verified. *)
Lemma vrs_brs_eq_set0 {p'} tr m : @vtr_brs_eq p' tr set0 m.+1.
Proof.
unfold vtr_brs_eq.
destruct tr. apply/forallP=>br. by rewrite in_set0.
destruct s. apply/andP;split. apply/forallP=>x.
apply/implyP. by rewrite in_set0. apply/forallP=>part.
apply/implyP=>Hf. by rewrite equiv_part_set0 in_set0 in Hf.
Qed.

(** For a given trace [tr], the union of two sets verifying of properties verifying the property [vtr_brs_eq tr] will also verify this property. *)
Lemma vtr_brs_eq_morph {p'} (tr : (@ABtree rul_gr_finType gatom_finType))
                    (brs1 brs2 : {set dbranch p'}) (count : nat) :
 @vtr_brs_eq p' tr brs1 count -> @vtr_brs_eq p' tr brs2 count ->
 @vtr_brs_eq p' tr (brs1 :|: brs2) count.
Proof.
move:count brs1 brs2.
apply (@abtree_ind_prop _ _ (fun x => forall count brs1 brs2,
  (vtr_brs_eq x brs1 count -> vtr_brs_eq x brs2 count
    -> vtr_brs_eq x (brs1 :|: brs2) count))).
destruct count. auto.
move=>brs1 brs2 H1 H2 /=.
apply/forallP=>br. apply/implyP=>/setUP [Hh1|Hh2].
apply (implyP (forallP H1 br) Hh1).
apply (implyP (forallP H2 br) Hh2).
move=>[cl s] l Hall count brs1 brs2 Heq1 Heq2.
destruct count as [|count]. inversion Heq1. apply/andP;split.
destruct (andP Heq1) as [H1 Ht1]. destruct (andP Heq2) as [H2 Ht2].
apply/forallP=>x. apply/implyP=>/setUP [Hin1|Hin2].
apply (implyP (forallP H1 _) Hin1).
apply (implyP (forallP H2 _) Hin2).
apply/forallP=>part. apply/implyP=>/imsetP [br] Hbrin Hparteq.
rewrite Hparteq.
apply/andP;split.
apply/forallP=>brb. apply/implyP. rewrite in_set.
move=>/andP [/setUP [Hin1|Hin2] Heq].
destruct brb as [[|brbh brbtl] Hbrb]. destruct br as [[|brh brtl] Hbr].
inversion Heq.
destruct brh. inversion Heq.
destruct br as [[|brh brtl] Hbr]. by destruct brbh.
apply/existsP. exists brbh. apply/andP;split. auto.
assert (Hpartb : ([set y in brs1 | br_h_b_eq
                          {| useq := brbh :: brbtl; buniq := Hbrb |} y]
          \in equivalence_partition (T:=dbranch p') br_h_b_eq brs1)).
apply/imsetP.
exists  {| useq := brbh :: brbtl; buniq := Hbrb |} .
apply Hin1. apply/eqP.
rewrite eqEsubset. apply/andP;split;apply/subsetP;move=>y; rewrite !in_set;
move=>/andP [Hyin Hyeq];apply/andP;split;auto;
destruct brbh;destruct brh;destruct y as [[|]];simpl in *;try (inversion Hyeq).
move:Heq1. move=>/andP [Hall1 Heq1].
destruct (andP (implyP (forallP Heq1 [set y in brs1 | br_h_b_eq {| useq := brbh:: brbtl;
                         buniq := Hbrb |} y]) Hpartb)) as [Hl Hr].
pose Hlb := ((forallP Hl {| useq := brbh :: brbtl; buniq := Hbrb |})).
clearbody Hlb. rewrite in_set in Hlb.
assert (Hlbb : ({| useq := brbh :: brbtl; buniq := Hbrb |} \in brs1) &&
      br_h_b_eq {| useq := brbh :: brbtl; buniq := Hbrb |}
        {| useq := brbh :: brbtl; buniq := Hbrb |}).
apply/andP;split. apply Hin1. destruct brbh. simpl. auto.
destruct (existsP (implyP Hlb Hlbb)) as [bhbb Hbrbb].
destruct (andP Hbrbb) as [Hbrbl Hbrbr]. clear Hbrbb.
pose Heqb := eqP Hbrbl. inversion Heqb. apply Hbrbr.
destruct brb as [[|brbh brbtl] Hbrb]. destruct br as [[|brh brtl] Hbr].
inversion Heq.
destruct brh. inversion Heq.
destruct br as [[|brh brtl] Hbr]. by destruct brbh.
apply/existsP. exists brbh. apply/andP;split. auto.
assert (Hpartb : ([set y in brs2 | br_h_b_eq
                          {| useq := brbh :: brbtl; buniq := Hbrb |} y]
          \in equivalence_partition (T:=dbranch p') br_h_b_eq brs2)).
apply/imsetP.
exists  {| useq := brbh :: brbtl; buniq := Hbrb |} .
apply Hin2. apply/eqP.
rewrite eqEsubset. apply/andP;split;apply/subsetP;move=>y; rewrite !in_set;
move=>/andP [Hyin Hyeq];apply/andP;split;auto;
destruct brbh;destruct brh;destruct y as [[|]];simpl in *;try (inversion Hyeq).
move:Heq2. move=>/andP [Hall2 Heq2].
destruct (andP (implyP (forallP Heq2 [set y in brs2 | br_h_b_eq {| useq := brbh:: brbtl;
                         buniq := Hbrb |} y]) Hpartb)) as [Hl Hr].
pose Hlb := ((forallP Hl {| useq := brbh :: brbtl; buniq := Hbrb |})).
clearbody Hlb. rewrite in_set in Hlb.
assert (Hlbb : ({| useq := brbh :: brbtl; buniq := Hbrb |} \in brs2) &&
      br_h_b_eq {| useq := brbh :: brbtl; buniq := Hbrb |}
        {| useq := brbh :: brbtl; buniq := Hbrb |}).
apply/andP;split. apply Hin2. destruct brbh. simpl. auto.
destruct (existsP (implyP Hlb Hlbb)) as [bhbb Hbrbb].
destruct (andP Hbrbb) as [Hbrbl Hbrbr]. clear Hbrbb.
pose Heqb := eqP Hbrbl. inversion Heqb. apply Hbrbr.

assert (Hueq : [set y in brs1 :|: brs2 | br_h_b_eq br y]
               = [set y in brs1 | br_h_b_eq br y] :|: [set y in brs2 | br_h_b_eq br y]).
apply/eqP. rewrite eqEsubset. apply/andP;split;apply/subsetP;move=>y; rewrite !in_set.
move=>/andP [/orP [Hin|Hin] Heq];apply/orP. by left;apply/andP;split. by right;apply/andP;split.
move=>/orP [/andP [Hin Heq] |/andP [Hin Heq]];apply/andP;split;auto. by apply/orP;left. by apply/orP;right.

destruct br as [[|brh brtl] Hbr].

destruct (setUP Hbrin) as [Hin1|Hin2].
assert (Hpartb : ([set y in brs1 | br_h_b_eq
                          {| useq := [::]; buniq := Hbr |} y]
          \in equivalence_partition (T:=dbranch p') br_h_b_eq brs1)).
    apply/imsetP.
    by exists {| useq := [::]; buniq := Hbr |} .
move:Heq1. move=>/andP [Hall1 Heq1].
destruct (andP (implyP (forallP Heq1 [set y in brs1 | br_h_b_eq _ y]) Hpartb))
  as [Hl Hr]. destruct (existsP Hr) as [k Hk]. destruct (andP Hk) as [Hk1 Hk2].
clear Hk. clear Hr.
apply/existsP. exists k. apply/andP;split.
apply/forallP=>br. rewrite in_set. apply/implyP.
move=>/andP [Ht Hf]. destruct br as [[|]]. inversion Hf.
destruct s0. inversion Hf.
assert (Hseq:[set useq_behead x | x in [set y in brs1 :|: brs2 | br_h_b_eq {| useq := [::]; buniq := Hbr |} y]] =
          [set useq_behead x | x in [set y in brs1 | br_h_b_eq {| useq := [::]; buniq := Hbr |} y]]).
apply/eqP. rewrite eqEsubset. apply/andP;split;apply/subsetP;move=>y; move=> /imsetP [brb];
rewrite in_set. move=>/andP [Hbrbin Hbrbeq]. destruct brb as [[|[]]]; inversion Hbrbeq.
move=>/andP [Hbrbin Hbrbeq]. destruct brb as [[|[]]]; inversion Hbrbeq.
rewrite Hseq. apply Hk2.

assert (Hpartb : ([set y in brs2 | br_h_b_eq
                          {| useq := [::]; buniq := Hbr |} y]
          \in equivalence_partition (T:=dbranch p') br_h_b_eq brs2)).
    apply/imsetP.
    by exists {| useq := [::]; buniq := Hbr |}.
move:Heq2. move=>/andP [Hall2 Heq2].
destruct (andP (implyP (forallP Heq2 [set y in brs2 | br_h_b_eq _ y]) Hpartb))
  as [Hl Hr]. destruct (existsP Hr) as [k Hk]. destruct (andP Hk) as [Hk1 Hk2].
clear Hk. clear Hr.
apply/existsP. exists k. apply/andP;split.
apply/forallP=>br. rewrite in_set. apply/implyP.
move=>/andP [Ht Hf]. destruct br as [[|]]. inversion Hf.
destruct s0. inversion Hf.
assert (Hseq:[set useq_behead x | x in [set y in brs1 :|: brs2 | br_h_b_eq {| useq := [::]; buniq := Hbr |} y]] =
          [set useq_behead x | x in [set y in brs2 | br_h_b_eq {| useq := [::]; buniq := Hbr |} y]]).
apply/eqP. rewrite eqEsubset. apply/andP;split;apply/subsetP;move=>y; move=> /imsetP [brb];
rewrite in_set. move=>/andP [Hbrbin Hbrbeq]. destruct brb as [[|[]]]; inversion Hbrbeq.
move=>/andP [Hbrbin Hbrbeq]. destruct brb as [[|[]]]; inversion Hbrbeq.
rewrite Hseq. apply Hk2.

destruct brh. apply/existsP. exists b_ind. apply/andP;split.
- apply/forallP=>brb. rewrite in_set. apply/implyP=>/andP /= [/setUP [Hbrbin1|Hbrbin2] Hbrbeq].
  + assert (Hpartb : ([set y in brs1 | br_h_b_eq
                          brb y]
          \in equivalence_partition (T:=dbranch p') br_h_b_eq brs1)).
    apply/imsetP.
    exists brb .
    apply Hbrbin1. apply/eqP.
    rewrite eqEsubset. apply/andP;split;apply/subsetP;move=>y; rewrite !in_set;
    move=>/andP [Hyin Hyeq];apply/andP;split;auto.
    move:Heq1. move=>/andP [Hall1 Heq1].
    destruct (andP (implyP (forallP Heq1 [set y in brs1 | br_h_b_eq brb y]) Hpartb))
      as [Hl Hk]. assert (Hbrbin : (brb \in [set y in brs1 | br_h_b_eq brb y])).
    rewrite in_set. apply/andP;split;auto. destruct brb as [[|[]]].
    inversion Hbrbeq. simpl;auto.
    destruct (existsP (implyP (forallP Hl brb) Hbrbin)) as [to Hto].
    destruct (andP Hto) as [Hl1 Hl2]. clear Hto.
    destruct brb as [[|[rb bb ab] brbtl]]. pose Hf := eqP Hl1. inversion Hf.
    simpl. by rewrite (eqP Hbrbeq).
  + assert (Hpartb : ([set y in brs2 | br_h_b_eq
                          brb y]
          \in equivalence_partition (T:=dbranch p') br_h_b_eq brs2)).
    apply/imsetP.
    exists brb .
    apply Hbrbin2. apply/eqP.
    rewrite eqEsubset. apply/andP;split;apply/subsetP;move=>y; rewrite !in_set;
    move=>/andP [Hyin Hyeq];apply/andP;split;auto.
    move:Heq2. move=>/andP [Hall2 Heq2].
    destruct (andP (implyP (forallP Heq2 [set y in brs2 | br_h_b_eq brb y]) Hpartb))
      as [Hl Hk]. assert (Hbrbin : (brb \in [set y in brs2 | br_h_b_eq brb y])).
    rewrite in_set. apply/andP;split;auto. destruct brb as [[|[]]].
    inversion Hbrbeq. simpl;auto.
    destruct (existsP (implyP (forallP Hl brb) Hbrbin)) as [to Hto].
    destruct (andP Hto) as [Hl1 Hl2]. clear Hto.
    destruct brb as [[|[rb bb ab] brbtl]]. pose Hf := eqP Hl1. inversion Hf.
    simpl. by rewrite (eqP Hbrbeq).
- destruct (set_0Vmem [set y in brs1 | br_h_b_eq
                          {| useq := {| r_ind := r_ind; b_ind := b_ind; t_ind := t_ind |} :: brtl;
                             buniq := Hbr |} y]) as [H1set0|[wit1 Hwit1]];
  destruct (set_0Vmem [set y in brs2 | br_h_b_eq
                          {| useq := {| r_ind := r_ind; b_ind := b_ind; t_ind := t_ind |} :: brtl;
                             buniq := Hbr |} y]) as [H2set0|[wit2 Hwit2]].
  (* brs1_eq = brs2_eq = set0 *)
  + assert (Huset0 : [set y in brs1 :|: brs2 | br_h_b_eq
                            {| useq := {| r_ind := r_ind; b_ind := b_ind; t_ind := t_ind |} :: brtl;
                            buniq := Hbr |} y] = set0).
    apply/eqP. rewrite -subset0. apply/subsetP=>x. rewrite in_set.
    move=>/andP [/setUP [Hxin1|Hxin2] Hxeq].
    rewrite -H1set0 in_set. apply/andP;split. apply Hxin1. auto.
    rewrite -H2set0 in_set. apply/andP;split. apply Hxin2. auto.
    assert (Hf : {| useq := {| r_ind := r_ind; b_ind := b_ind; t_ind := t_ind |}
                              :: brtl; buniq := Hbr |} \in set0).
    rewrite -Huset0 in_set. apply/andP;split. auto. simpl;auto. by rewrite in_set0 in Hf.
  (* brs1_eq = set0 /\ wit2 \in brs2_eq *)
  + rewrite in_set in Hwit2. destruct (andP Hwit2) as [Hw21 Hw22]. simpl in Heq2.  clear Hwit2.
    simpl in Heq2.
    assert (Hpart : ([set y in brs2 | br_h_b_eq wit2 y]
         \in equivalence_partition (T:=dbranch p') br_h_b_eq brs2)).
    apply/imsetP. by exists wit2.
    move:Heq2. move=>/andP [Hall2 Heq2].
    destruct (andP (implyP (forallP Heq2 [set y in brs2 | br_h_b_eq wit2 y]) Hpart))
       as [Hk1 Hk2].
    destruct (existsP Hk2) as [k Hk]. clear Hk2.
    destruct (andP Hk) as [Hk11 Hk12]. clear Hk.
    assert (Hkb : k = b_ind).
    destruct wit2 as [[|[rw2 bw2 aw2] tlw2]]. inversion Hw22.
    rewrite (eqP Hw22).
    assert (Hin : {| useq := {| r_ind := rw2; b_ind := bw2; t_ind := aw2 |} :: tlw2;
                                 buniq := buniq |} \in [set y in brs2 | br_h_b_eq
                                 {|
                                 useq := {| r_ind := rw2; b_ind := bw2; t_ind := aw2 |} :: tlw2;
                                 buniq := buniq |} y]).
    rewrite in_set. apply/andP;split;simpl;auto.
    pose Heq:= (implyP (forallP Hk11 {| useq := {| r_ind := rw2;
           b_ind := bw2; t_ind := aw2 |} :: tlw2; buniq := buniq |}
            )Hin). simpl in Heq. by rewrite (eqP Heq).
    rewrite Hkb in Hk12.
    assert (Hseq: [set useq_behead x | x in [set y in brs2 | br_h_b_eq wit2 y]] =
[set useq_behead x | x in [set y in brs1 :|: brs2 | br_h_b_eq
           {| useq := {| r_ind := r_ind; b_ind := b_ind; t_ind := t_ind |} :: brtl;
                                            buniq := Hbr |} y]]).
    apply/eqP. rewrite eqEsubset. apply/andP;split;apply/subsetP;move=>y.
    move=>/imsetP [brb]. rewrite in_set. move=>/andP [Hbrbin Hbrbeq] ->.
    apply/imsetP. exists brb. rewrite in_set. apply/andP;split.
    apply/setUP;right;apply Hbrbin. simpl. destruct wit2 as [[|]]. inversion Hw22.
    destruct brb as [[|]]. simpl in Hbrbeq. destruct s0. inversion Hbrbeq.
    destruct s1. destruct s0. simpl in Hbrbeq. simpl in Hw22. by rewrite (eqP Hw22) (eqP Hbrbeq).
    auto.
    move=>/imsetP [brb]. rewrite in_set. move=>/andP [/setUP [Hbrbin1|Hbrbin2]] /= Hbrbeq ->.
    assert (Hf: brb \in set0). rewrite -H1set0. rewrite in_set. apply/andP;split.
    apply Hbrbin1. apply Hbrbeq. by rewrite in_set0 in Hf.
    apply/imsetP. exists brb. rewrite in_set. apply/andP;split. apply Hbrbin2.
    simpl. destruct brb as [[|]]. inversion Hbrbeq. destruct wit2 as [[|]].
    simpl in Hw22. inversion Hw22. destruct s1. destruct s0. simpl.
    simpl in Hw22. by rewrite -(eqP Hw22) -(eqP Hbrbeq). auto.
    rewrite Hseq in Hk12. apply Hk12.
  (* wi1 \in brs1_eq /\ brs2_eq = set0 *)
  + rewrite in_set in Hwit1. destruct (andP Hwit1) as [Hw11 Hw12]. simpl in Heq1. clear Hwit1.
    assert (Hpart : ([set y in brs1 | br_h_b_eq wit1 y]
         \in equivalence_partition (T:=dbranch p') br_h_b_eq brs1)).
    apply/imsetP. by exists wit1.
    move:Heq1. move=>/andP [Hall1 Heq1].
    destruct (andP (implyP (forallP Heq1 [set y in brs1 | br_h_b_eq wit1 y]) Hpart))
       as [Hk1 Hk2].
    destruct (existsP Hk2) as [k Hk]. clear Hk2.
    destruct (andP Hk) as [Hk11 Hk12]. clear Hk.
    assert (Hkb : k = b_ind).
    destruct wit1 as [[|[rw1 bw1 aw1] tlw1]]. inversion Hw12.
    rewrite (eqP Hw12).
    assert (Hin : {| useq := {| r_ind := rw1; b_ind := bw1; t_ind := aw1 |} :: tlw1;
                                 buniq := buniq |} \in [set y in brs1 | br_h_b_eq
                                 {|
                                 useq := {| r_ind := rw1; b_ind := bw1; t_ind := aw1 |} :: tlw1;
                                 buniq := buniq |} y]).
    rewrite in_set. apply/andP;split;simpl;auto.
    pose Heq:= (implyP (forallP Hk11 {| useq := {| r_ind := rw1;
           b_ind := bw1; t_ind := aw1 |} :: tlw1; buniq := buniq |}
            )Hin). simpl in Heq. by rewrite (eqP Heq).
    rewrite Hkb in Hk12.
    assert (Hseq: [set useq_behead x | x in [set y in brs1 | br_h_b_eq wit1 y]] =
[set useq_behead x | x in [set y in brs1 :|: brs2 | br_h_b_eq
           {| useq := {| r_ind := r_ind; b_ind := b_ind; t_ind := t_ind |} :: brtl;
                                            buniq := Hbr |} y]]).
    apply/eqP. rewrite eqEsubset. apply/andP;split;apply/subsetP;move=>y.
    move=>/imsetP [brb]. rewrite in_set. move=>/andP [Hbrbin Hbrbeq] ->.
    apply/imsetP. exists brb. rewrite in_set. apply/andP;split. apply/setUP;left. apply Hbrbin.
    simpl. destruct brb as [[|]]. destruct wit1 as [[|]].
    simpl in Hw12. inversion Hw12. simpl in Hbrbeq. destruct s0. inversion Hbrbeq. destruct s0. simpl.
    simpl in Hw12. destruct wit1 as [[|]]. inversion Hw12. destruct s0. by rewrite (eqP Hw12) -(eqP Hbrbeq). auto.
    move=>/imsetP [brb]. rewrite in_set. move=>/andP [/setUP [Hbrbin1|Hbrbin2]] /= Hbrbeq ->.
    apply/imsetP. exists brb. rewrite in_set. apply/andP;split. apply Hbrbin1.
    destruct brb as [[|]]. inversion Hbrbeq. destruct s0. destruct wit1 as [[|]]. simpl in Hw12. inversion Hw12.
    destruct s0. simpl. by rewrite -(eqP Hw12) (eqP Hbrbeq). auto.
    assert (Hf: brb \in set0). rewrite -H2set0. rewrite in_set. apply/andP;split.
    apply Hbrbin2. apply Hbrbeq. by rewrite in_set0 in Hf.
    rewrite Hseq in Hk12. apply Hk12.
  + rewrite in_set in Hwit1. destruct (andP Hwit1) as [Hwit11 Hwit12].
    rewrite in_set in Hwit2. destruct (andP Hwit2) as [Hwit21 Hwit22].
    assert (Hpart1 : ([set y in brs1 | br_h_b_eq wit1 y]
         \in equivalence_partition (T:=dbranch p') br_h_b_eq brs1)).
    apply/imsetP. by exists wit1.
    assert (Hpart2 : ([set y in brs2 | br_h_b_eq wit2 y]
         \in equivalence_partition (T:=dbranch p') br_h_b_eq brs2)).
    apply/imsetP. by exists wit2.
    move:Heq1. move=>/andP [Hall1 Heq1].
    destruct (andP (implyP (forallP Heq1 _) Hpart1)) as [Heq11 Heq12].
    destruct (existsP Heq12) as [k1 Hk1]. destruct (andP Hk1) as [Hk11 Hk12].
    move:Heq2. move=>/andP [Hall2 Heq2].
    destruct (andP (implyP (forallP Heq2 _) Hpart2)) as [Heq21 Heq22].
    destruct (existsP Heq22) as [k2 Hk2]. destruct (andP Hk2) as [Hk21 Hk22].
    assert (Hk1b : k1 = b_ind).
      destruct wit1 as [[|]]. simpl in Hwit12. inversion Hwit12.
      destruct s0. simpl in Hwit12. rewrite (eqP Hwit12).
      assert (Heqb: br_h_b_seq {| useq := {| r_ind := r_ind0; b_ind := b_ind0; t_ind := t_ind0 |} :: l0; buniq := buniq |} k1).
      apply (implyP (forallP Hk11 _)). rewrite in_set. apply/andP;split. apply Hwit11. simpl. auto.
      by rewrite (eqP Heqb).
    assert (Hk2b : k2 = b_ind).
      destruct wit2 as [[|]]. simpl in Hwit22. inversion Hwit22.
      destruct s0. simpl in Hwit22. rewrite (eqP Hwit22).
      assert (Heqb: br_h_b_seq {| useq := {| r_ind := r_ind0; b_ind := b_ind0; t_ind := t_ind0 |} :: l0; buniq := buniq |} k2).
      apply (implyP (forallP Hk21 _)). rewrite in_set. apply/andP;split. apply Hwit21. simpl. auto.
      by rewrite (eqP Heqb).
    rewrite Hk1b in Hk12.
    rewrite Hk2b in Hk22.
    destruct (nth_error_case l b_ind) as [Hnone|[desc [Hdin Hdeq]]].
    rewrite Hnone in Hk22. rewrite Hnone in Hk12. clear Hk2.
    inversion Hk22.

    rewrite Hdeq Hueq imsetU.
    apply (all_prop_in Hall Hdin).
    rewrite Hdeq in Hk12.
    assert (Hseq : [set useq_behead x
     | x in [set y in brs1 | br_h_b_eq
                               {| useq := {| r_ind := r_ind; b_ind := b_ind; t_ind := t_ind |} :: brtl; buniq := Hbr |} y]]
        =  [set useq_behead x | x in [set y in brs1 | br_h_b_eq wit1 y]]).
    apply/eqP. rewrite eqEsubset. apply/andP;split;apply/subsetP;move=>y.
    move=>/imsetP [brb]. rewrite in_set. move=>/andP /= [Hbrbin Hbrbeq] ->.
    apply/imsetP. exists brb. rewrite in_set. apply/andP;split. apply Hbrbin.
    destruct brb as [[|]]. inversion Hbrbeq. destruct wit1 as [[|]]. simpl in Hwit12.
    inversion Hwit12. destruct s1. simpl in Hwit12.
    destruct s0. simpl. by rewrite -(eqP Hwit12) -(eqP Hbrbeq). auto.
    move=>/imsetP [brb]. rewrite in_set. move=>/andP [Hbrbin Hbrbeq] ->.
    apply/imsetP. exists brb. rewrite in_set. apply/andP;split. apply Hbrbin.
    destruct brb as [[|]]. destruct wit1 as [[|]]. inversion Hwit12. destruct s0.
    simpl in Hbrbeq. inversion Hbrbeq. destruct wit1 as [[|]]. destruct s0.
    simpl in Hbrbeq. inversion Hbrbeq. destruct s0. simpl. simpl in Hbrbeq. destruct s1.
    by rewrite -(eqP Hbrbeq) (eqP Hwit12). auto.
    rewrite Hseq. apply Hk12.
    rewrite Hdeq in Hk22.
    assert (Hseq : [set useq_behead x
     | x in [set y in brs2 | br_h_b_eq
                               {| useq := {| r_ind := r_ind; b_ind := b_ind; t_ind := t_ind |} :: brtl; buniq := Hbr |} y]]
        =  [set useq_behead x | x in [set y in brs2 | br_h_b_eq wit2 y]]).
    apply/eqP. rewrite eqEsubset. apply/andP;split;apply/subsetP;move=>y.
    move=>/imsetP [brb]. rewrite in_set. move=>/andP /= [Hbrbin Hbrbeq] ->.
    apply/imsetP. exists brb. rewrite in_set. apply/andP;split. apply Hbrbin.
    destruct brb as [[|]]. inversion Hbrbeq. destruct wit2 as [[|]]. simpl in Hwit22.
    inversion Hwit22. destruct s1. simpl in Hwit22.
    destruct s0. simpl. by rewrite -(eqP Hwit22) -(eqP Hbrbeq). auto.
    move=>/imsetP [brb]. rewrite in_set. move=>/andP [Hbrbin Hbrbeq] ->.
    apply/imsetP. exists brb. rewrite in_set. apply/andP;split. apply Hbrbin.
    destruct brb as [[|]]. destruct wit2 as [[|]]. inversion Hwit22. destruct s0.
    simpl in Hbrbeq. inversion Hbrbeq. destruct wit2 as [[|]]. destruct s0.
    simpl in Hbrbeq. inversion Hbrbeq. destruct s0. simpl. simpl in Hbrbeq. destruct s1.
    by rewrite -(eqP Hbrbeq) (eqP Hwit22). auto.
    rewrite Hseq. apply Hk22.
Qed.

(** Let [typs] be a sequence of non Top types, such that for each, there
   is a conjunct verifying [vtr_brs_eq tr], then taking the conjunct of
   the typses, there exist a conjunct, verifying [vtr_brs_eq tr] *)
Lemma has_all_vtr {p'} (ctxt : tocs p') (typs : seq (DDtype ctxt)) tr :
        has (fun x => x != Triv p') (map val typs) ->
        all (fun x : Dtype p' => (x != Triv p') ==>
          [exists ct in dt_get_dcb x, vtr_brs_eq tr ct (ABheight tr).+1])
         [seq val i | i <- typs] ->
   [exists ct in dt_get_dcb (fold_type_alg DtConj typs (mk_DDtype (@TrivDDtype _ _))),
     vtr_brs_eq tr ct (ABheight tr).+1].
Proof.
induction typs as [|h tl Htyps];move=>//.
destruct h as [[|h] Hh]. move=>//.
move=>Htriv /andP [Hexh Hexr].
destruct (existsP Hexh) as [cth Hcth].
destruct (andP Hcth) as [Hcthin Hctheq]. clear Hcth.
destruct (bool_des_rew (has (fun x : Dtype p' => x != Triv p') (map val tl)))
  as [Htlhas|Htltriv].
destruct (existsP (Htyps Htlhas Hexr)) as [ctl Hctl].
destruct (andP Hctl) as [Hctlin Htcleq]. clear Hctl.
apply/existsP. simpl.
exists (cth :|: ctl). apply/andP;split.
pose Hnottriv := (tr_conj Htlhas). clearbody Hnottriv.
destruct ((fold_type_alg DtConj tl)).
unfold negb in Hnottriv. simpl in Hnottriv.
destruct dt. by rewrite eq_refl in Hnottriv. simpl.
apply/imset2P. exists cth ctl.
apply Hcthin. apply Hctlin. auto.
assert (Hr : vtr_brs_eq tr (cth :|: ctl) (ABheight tr).+1).
by apply vtr_brs_eq_morph. apply Hr.
have Halltriv := negb_has_predC_all Htltriv.
simpl. rewrite (triv_conj Halltriv). apply/existsP. exists cth.
apply/andP;split. apply Hcthin. apply Hctheq.
Qed.

(** Let [ABNode (cl,s) descs] in the semantics of [p] and [v] a variable of
  [cl] that appears at [tocc] within atom [ato], then [descs] is long enough
  to have an element for [b_ind tocc] *)
Lemma desc_tocc def cl s descs Hwht k v tocc :
   {| wht := ABNode (RS cl s) descs; Hwht := Hwht |} \in sem_t p dga def k i
-> v \in tail_vars (body_cl cl)
-> t_at tocc = Some (Var v)
-> (exists ato, nth_error (body_cl cl) (b_ind tocc) = Some ato)
-> exists tr', nth_error descs (@b_ind p tocc) = Some tr'.
Proof.
move:cl s descs Hwht.
induction k as [|k Hk];move=>cl s descs Hwht.
move=>/imsetP [ga Hga Hf]. inversion Hf.
move=>/setUP [Hrec|Hnew] Hvin Htat Hnth.
by apply (Hk cl s descs Hwht Hrec).
move:Hnew.
move=>/bigcup_seqP [clb Hclbin /andP [/mem_pset_set /imset2P [descsb sb Hsbin Hded Hclseq] Htriv]].
clear Htriv. rewrite in_set in Hded. destruct (andP Hded) as [Hsbmatch H2].
destruct (andP H2) as [Hdedeq Hall]. clear Hded. clear H2.
move:Hclseq. unfold wu_pcons_seq. unfold wu_pcons_wlist.
destruct Sumbool.sumbool_of_bool;move=> // [Hcleq Hseq Hdescseq]. clear e.
rewrite Hdescseq seq_wlistK.
unfold ded_sub_equal in Hdedeq.
assert (Hs : size descsb = size (body_cl clb)).
by rewrite -(@size_map _ _ (fun x => @ded dga def x)) (eqP Hdedeq) size_map.
apply nth_error_size_leq. rewrite size_map Hs.
apply nth_error_leq_size. destruct Hnth as [ato Hato]. exists ato. by rewrite -Hcleq.
destruct descsb as [t Ht]. rewrite (eqP Ht).
destruct clb as [hclb tlclb]. simpl.
apply wlist_to_seq_size.
Qed.

(** If we have a typing judgement [progPredTyping v p f j typs],
  folding the [typs] to build a disjunction, we find a real type that is
  not [tInit] *)
Lemma semt_bis v (ct : tocs p) f j typs :
   progPredTyping v p f j typs
-> predtype f = Idb
-> val (@fold_type_alg p ct DtDisj typs DEmpty) <> tInit p.
Proof.
apply (@progPredTyping_mrec
  (fun pb (ctxt' : tocs pb) v' (t : DDtype ctxt') (Hvt : varTyping v' t) =>
    val t <> tInit pb)
  (* for each "subtype", a ct matches *)
  (fun p' v' (ctxt' : tocs p') (l : {set (enotin ctxt')}) (l0 : seq (DDtype ctxt')) (Hott : OccsToTypes v' l l0)
       => (val (@fold_type_alg p' ctxt' DtConj l0 (mk_DDtype (@TrivDDtype _ _))) <> tInit p'))
  (* preserved by insert *)
  (fun p' v' (ctxt' : tocs p') f (o : 'I_max_ar) (d : (DDtype ctxt')) (Hpt : predTyping v' f o d)
    => predtype f = Idb -> (val d <> tInit p'))
  (* preserved by disj *)
  (fun p' v' (ctxt' : tocs p') ip' f (ind : 'I_max_ar) (l : seq (DDtype ctxt')) (Hppt : progPredTyping v' ip' f ind l)
      => predtype f = Idb ->
        val (fold_type_alg DtDisj l DEmpty) <> tInit p'));
move=>//.
- intros. apply tConj_not_init.
  apply tInsert_not_init. apply H.
- move=> pb v' ctb fb k -> //.
- intros. move=>Hf. inversion Hf as [Hff].
  assert (Hfff : [set @unil (Finite.eqType (t_occ_finType fp))] \in set0).
  rewrite Hff. by apply/set1P.
  by rewrite in_set0 in Hfff.
- intros. apply tDisj_not_init. apply H0.
  apply/H/H1.
Qed.

(** If the program does not share variables, when we know that a [t_occ] points
  to [v] and [v] appears in [cl], then [t_occ] points to clause [cl]*)
Lemma vns_v_in {p'} (tocc : t_occ_finType p') cl v :
   cl \in p'
-> vars_not_shared p'
-> v \in tail_vars (body_cl cl)
-> t_at tocc = Some (Var v)
-> nth_error p' (r_ind tocc) = Some cl.
Proof.
move=>Hin Hvns Hvin Htat.
pose Htatb := Htat. clearbody Htatb. move:Htat.
unfold t_at. unfold at_at.
destruct (nth_error_case p' (r_ind tocc))
  as [Hnone|[c [Hcin Hceq]]].
by rewrite Hnone.
rewrite Hceq.
destruct (nth_error_case (body_cl c) (b_ind tocc))
  as [Hnone|[a [Hain Haeq]]].
by rewrite Hnone.
rewrite Haeq.
assert (Hvinb : v \in tail_vars (body_cl c)).
apply t_at_vars_in with (p := p') (tocc := tocc).
apply Htatb. by rewrite Hceq.
move=>H.
by rewrite (vns_cl_eq Hvin Hvinb Hin Hcin Hvns).
Qed.

(** If [ct] appears in one conjunct of a sequence of types,
   [ct] still appears in one of the conjunct of the disjunction of types *)
Lemma ct_in_fold_disj {p'} (ctxt : tocs p') (typs : seq (DDtype ctxt))
        ct (ntyp : Dtype p') :
        ct \in dt_get_dcb ntyp -> ntyp \in map val typs ->
        val (fold_type_alg DtDisj typs DEmpty) <> Triv p' ->
        ct \in dt_get_dcb (fold_type_alg DtDisj typs DEmpty).
Proof.
move:ntyp. induction typs as [|h l Hl];
move=>ntyp /= Hctin.
by rewrite in_nil.
rewrite in_cons. move=>/orP [Hinh|Hinrec].
move:Hctin.
destruct h as [[|h]];
destruct (fold_type_alg DtDisj l DEmpty) as [[|d]];
move=>//.
rewrite (eqP Hinh). move=>/= H1 H2. apply/setUP. left. apply H1.
move:Hctin. destruct h as [[|h]];
destruct (fold_type_alg DtDisj l DEmpty) as [[|d]];
move=>//.
move=>/= H1 H2. apply/setUP;right. by apply Hl with (ntyp := ntyp).
Qed.

(** [tr = ABNode (cl,s) desc] in the trace semantics of [p], forall variable [v]
   of [cl] there is [cl] in the typing of [v], such that [vtr_brs_eq tr ct]
*)
Lemma semt_exists_ad_mintype (tr : trace_sem_trees dga) def k cl s v 
                             (typ : @DDtype p set0) :
   varTyping v typ
-> [exists t, val typ == @Tr p t]
-> v \in tail_vars (body_cl cl)
-> tr \in sem_t p dga def k i
-> ABroot (val tr) = inl (RS cl s)
-> [exists ct in dt_get_dcb typ, 
      (vtr_brs_eq (val tr) ct (ABheight (val tr)).+1)].
Proof.
move=> Htyping Hvtyped Hvincl Htrin Htreq.
move:tr cl s Htrin Htreq Hvtyped Hvincl.
move:psafe pvars phsafe.
apply (@varTyping_mrec 
  (fun pb (ctxt' : tocs pb) v' (typ : DDtype ctxt') (Hvt : varTyping v' typ) => 
     prog_safe pb -> vars_not_shared pb ->
      prog_safe_hds pb ->
    forall (tr : trace_sem_trees dga) (cl : clause) (s : sub),
    tr \in sem_t pb dga def k i ->
    ABroot (val tr) = inl (RS cl s) ->
    [exists t, val typ == @Tr pb t] ->
      v' \in tail_vars (body_cl cl) ->
    [exists ct in dt_get_dcb typ,
      vtr_brs_eq (val tr) ct (ABheight (val tr)).+1])
  (* for each "subtype", a ct matches *)
  (fun p' v' (ctxt' : tocs p') (l : {set (enotin ctxt')}) (l0 : seq (DDtype ctxt')) (Hott : OccsToTypes v' l l0)
       => prog_safe p' -> vars_not_shared p' -> prog_safe_hds p' ->
    forall (tr : trace_sem_trees dga) (cl : clause) (s : sub), v' \in (tail_vars (body_cl cl)) ->
    tr \in sem_t p' dga def k i -> 
    ABroot (val tr) = inl (RS cl s) -> 
    ([forall x in l, ((t_at (val x)) == Some (Var v'))]) 
          -> all (fun x =>  (x != Triv p') ==> [exists ct in dt_get_dcb x, vtr_brs_eq (val tr) ct (ABheight (val tr)).+1]) (map val l0))
  (* preserved by insert *)
  (fun p' v' (ctxt' : tocs p') f (o : 'I_max_ar) (d : (DDtype ctxt')) (Hpt : predTyping v' f o d) 
    => prog_safe p' ->  vars_not_shared p' -> prog_safe_hds p' -> val d <> Triv p' ->
    forall tocc (Htocc : notInT tocc d), t_at tocc = Some (Var v') -> p_at tocc = Some f
   -> (t_ind tocc) = o 
   ->  forall (tr : trace_sem_trees dga) (cl : clause) (s : sub),
        tr \in sem_t p' dga def k i -> v' \in (tail_vars (body_cl cl)) ->
        ABroot (val tr) = inl (RS cl s) ->
    [exists ct in dt_get_dcb (tInsert Htocc), vtr_brs_eq (val tr) ct (ABheight (val tr)).+1])
  (* preserved by disj *)
  (fun p' v' (ctxt' : tocs p') ip' f (ind : 'I_max_ar) (l : seq (DDtype ctxt')) (Hppt : progPredTyping v' ip' f ind l)
      => prog_safe p' ->  vars_not_shared p' -> prog_safe_hds p' -> val (fold_type_alg DtDisj l DEmpty) <> Triv p' ->
          ip' \subset p' -> size (pmap (fun x => term_to_var (nth_error (arg_atom (head_cl x)) ind)) 
              [seq cl <- ip' | hsym_cl cl == f]) = size l ->
        all_prop (fun x => exists vl, (nth_error (arg_atom (head_cl x)) ind) = Some (Var vl)
   /\ exists typ, typ \in (map val l) /\ (forall (tr : trace_sem_trees dga) (cl : clause) (s : sub),
        tr \in sem_t p' dga def k i -> vl \in (tail_vars (body_cl cl)) ->
        ABroot (val tr) = inl (RS cl s) ->
    [exists ct in dt_get_dcb typ, vtr_brs_eq (val tr) ct (ABheight (val tr)).+1])) [seq cl <- ip' | hsym_cl cl == f]))
  with (p := p) (ctxt := set0) (o := v) (d := typ);
move=>//.
(*- move=>pb ct vb H1 H2 H3 trb clb sb Htrin Hroot /existsP [trtb Htrb]. inversion Htrb.*)
- move => p0 ct' tot v' occsTypes Hoccs Hall Hsafe Hvns Hsfh tr cl s Htrin Hrooteq Hvtyped Hvin.
  assert (Halloccs : [forall x,
          (x \in seq_to_enotin (occsInProgram p0 v') ct') ==>
          (t_at (val x) == Some (Var v'))]).
    - apply/forallP. move => x. apply/implyP. move => Hx.
      destruct (imsetP (mem_pset_set Hx)) as [xocc Hxoccin Hxeq].
      unfold insub in Hxeq. destruct idP in Hxeq ; inversion Hxeq.
      apply/eqP/occsInProgramV/Hxoccin. 
  apply has_all_vtr.   
  destruct (bool_des_rew (has (fun x => x != Triv p0) (map val occsTypes))) as [Ht|Hf].
  apply Ht. have Halltriv := negb_has_predC_all Hf. clear Hf.  
  destruct (existsP Hvtyped) as [trb Htrb]. 
  rewrite (triv_conj Halltriv) in Htrb. pose Hf := eqP Htrb. inversion Hf. 
  apply (Hall Hsafe Hvns Hsfh tr cl s Hvin Htrin Hrooteq Halloccs).
- intros. apply/andP;split.
  + apply/implyP=>Hnottriv. destruct dt as [[|dt] Hdt].
    - inversion Hnottriv. 
    - assert (Hneq : val {| dt := Tr (p:=p0) dt; Hdd := Hdt |} <> Triv p0). 
      move=>Hf. inversion Hf. 
      dependent destruction p1.
      (* base case using H0 *)
      + assert (Hindt : [set (@unil (t_occ_finType p0))] \in [set [set unil]]). apply/set11.
        apply/existsP. 
        exists (tInsert_conj (implyP (forallP (ddtextract {| dt := tInit p0; Hdd := not_in_init (ct :|: [set (val tocc)]) |}) [set unil]) Hindt)).    
        apply/andP;split. 
        - apply/imsetP.
           exists (@exist ({set (@uniq_seq_finType (t_occ_finType p0))}) 
                       (fun x => x \in [set [set unil]]) 
                       [set (@unil (t_occ_finType p0))] 
                       Hindt).
          + rewrite in_set mem_pmap_sub mem_enum. by apply Hindt.  
          + apply/eqP. rewrite eqEsubset. apply/andP;split;apply/subsetP;move=>y /imsetP [yo Hyo ->].
            - apply/imsetP. simpl. assert (Hin : @unil (t_occ_finType p0) \in [set unil]). by apply/set1P.
              exists (@exist (@uniq_seq_finType (t_occ_finType p0)) (fun x => x \in [set unil]) unil Hin).
              rewrite in_set mem_pmap_sub mem_enum. by apply/set1P.
              apply/val_inj. simpl. rewrite in_set mem_pmap_sub mem_enum in Hyo. by rewrite (set1P Hyo).
            - apply/imsetP. simpl. assert (Hin : @unil (t_occ_finType p0) \in [set unil]). by apply/set1P.
              exists (@exist (@uniq_seq_finType (t_occ_finType p0)) (fun x => x \in [set unil]) unil Hin).
              rewrite in_set mem_pmap_sub mem_enum. by apply/set1P.
              apply/val_inj. simpl. rewrite in_set mem_pmap_sub mem_enum in Hyo. by rewrite (set1P Hyo).
        - destruct tr as [[|[clb sb] descs]]. simpl in *. inversion H7.
          assert (Htat : t_at (val tocc) = Some (Var v0)).
          apply/eqP. apply (implyP (forallP H8 tocc)). by apply/setUP;left;apply/set1P.
          apply/andP;split. apply/forallP=>x. apply/implyP=>/imsetP [y Hyin ->]. auto.
          apply/forallP=>part. apply/implyP=>/imsetP [brb /imsetP [bbrb Hbbrbi ->] ->].
          assert (Hnth : nth_error p0 (r_ind (val tocc)) == Some clb).
          inversion H7 as [[Hcleq Hseq]]. 
          apply/eqP/(vns_v_in (tr_cl_in H6 H7) H3 H5 Htat). 
          apply/andP;split. 
          + apply/forallP=>br. rewrite in_set. 
            apply/implyP=>/andP [/imsetP [snil Hsnilin ->] /= Heq].
            apply/existsP. exists (val tocc). apply/andP;split;auto. 
          + destruct tocc as [[rind bind aind] Htocc]. 
            apply/existsP. exists bind. 
            apply/andP;split. 
            - apply/forallP=>br. rewrite in_set. 
              by apply/implyP=>/andP [/imsetP [x Hx ->]] /= Hbreq.  
            - destruct (edb_in_sem_t_descs H6 H4 (eqP Hnth) e0 H0)
                  as [ga Hga].
              simpl in *. rewrite Hga. 
              apply/forallP=>brn. apply/implyP=>/imsetP [[[| hbrnb tlbrnb] Hbnrb]];
              rewrite in_set; move=>/andP [/imsetP [brnbb Hbrbnbbin ->]] //.
              destruct hbrnb. move=>/eqP -> -> /=. destruct brnbb as [x Hx].
              simpl. by rewrite (set1P Hx).   
      + assert (Htatb : t_at (val tocc) = Some (Var v0)). 
        apply/eqP/(implyP (forallP H9 _)). apply/setUP;left. by apply/set1P.  
        assert (Hind : t_ind (val tocc) = j). destruct tocc. simpl. simpl in e. by rewrite e.
        assert (Hnottrivb : val {| dt := Tr (p:=p0) dt; Hdd := Hdt |} <> Triv p0). auto.   
        apply (@H2 H3 H4 H5 Hnottrivb (val tocc) _ Htatb e0 Hind tr cl s H7);auto. 
  + apply H with (cl:=cl) (s:=s);auto.
    apply/forallP=>x. apply/implyP=>Hx. 
    apply (implyP (forallP H7 x)). apply/setUP. by right.

- move=> pb vb ct f j Hptype Hsafe Hvns Hsafe_hds Hnottriv tocc Htocc Htat Hpat Htind
         tr clb sb Htrded Hvbin Hroot. 
  apply/existsP. 
  assert (Hindt : [set (@unil (t_occ_finType pb))] \in [set [set unil]]). apply/set11.
  assert (Hindtb : [forall b, (b \in [set unil]) ==> (negb (@in_mem (t_occ pb) tocc (@mem
                                   (Equality.sort (Finite.eqType (t_occ_finType pb))) (seq_predType
                                      (Finite.eqType (t_occ_finType pb))) (@useq
                                      (Finite.eqType (t_occ_finType pb)) b))))]).
  apply/forallP=>b. by apply/implyP=>/set1P ->. 
  exists (@tInsert_conj pb tocc [set (@unil (t_occ_finType pb))] Hindtb).
  apply/andP;split. 
  + simpl. apply/imsetP. 
    exists (@exist (set_of_finType (dbranch pb)) 
                       (fun x => x \in [set [set unil]]) 
                       [set (@unil (t_occ_finType pb))] 
                       Hindt).
    unfold equip. rewrite in_set. rewrite mem_pmap. apply/mapP. 
    exists [set (@unil (t_occ_finType pb))]. rewrite mem_enum. by apply/set1P.
    unfold insub. destruct idP as [Hi|Hi]. by apply/f_equal/val_inj.
    exfalso. apply Hi. apply Hindt. simpl. apply/f_equal/Eqdep_dec_bool.
  + simpl.
    destruct tr as [[|[clbb sbb] descsb] Htr]; inversion Hroot as [[Hcleq Hseq]].
    - simpl. apply/andP;split. 
      + apply/forallP=>x. by apply/implyP=>/imsetP [[y Hyin] Hyinb ->].  
      + apply/forallP=>part. apply/implyP=>/imsetP [brb Hbrbin ->].
        apply/andP;split. 
        - apply/forallP=>br. rewrite in_set. apply/implyP=>/andP [/imsetP [[brbb Hbrbbin] Hbrbbinb ->] /= Hbrbhbeq].
          apply/existsP. exists tocc. apply/andP;split. auto. simpl in *. 
        - rewrite Hcleq. apply/eqP/vns_v_in;auto. apply (tr_cl_in Htrded Hroot).
          apply Hvbin. apply Htat.
    - apply/existsP. exists (b_ind tocc). apply/andP;split.
      + apply/forallP=>br. rewrite in_set. apply/implyP=>/andP [/imsetP [[y Hyin] Hy ->] /= Hbrbeq].
        destruct tocc as [rind bind tind]. auto.
      + assert (Hnth : nth_error pb (r_ind tocc) = Some clbb). 
        rewrite Hcleq.
        apply (vns_v_in (tr_cl_in Htrded Hroot) Hvns Hvbin Htat). 
        destruct (edb_in_sem_t_descs Htrded Hsafe_hds Hnth Hpat Hptype) as [ga Hga].
        rewrite Hga.
        apply/forallP=>br. apply/implyP=>/imsetP [y]. rewrite in_set.
        move=>/andP [/imsetP [[z Hzin] Hz ->] /= Hbrbeq ->] /=.
        by rewrite (set1P Hzin).

- move=> pb vb ct f j typs Hptype Hppt Hprev Hsafe Hvns Hsafe_hds Hnottriv tocc Htocc Htat Hpat Htind
         tr clb sb Htrded Hvbin Hroot.
  unfold vtr_brs_eq. 
  destruct tr as [[|[clbb sbb] descsb] Htr]; inversion Hroot as [[Hcleq Hseq]].
  simpl.

  have Hnth := (vns_v_in (tr_cl_in Htrded Hroot) Hvns Hvbin Htat).
  rewrite -Hcleq in Hnth.
  destruct (idb_in_sem_t_descs Htrded isafe Hnth Hpat Hptype) as [cls Hcls].
  destruct Hcls as [descss Hb].
  destruct Hb as [Hsymeq Hnthb].
  destruct cls as [clt st]. simpl in *. 
  assert (Hsubtree : subtree (val {| wht := (ABNode (RS clt st) descss) ;
                                     Hwht := (allP (wu_pred_descs Htr) _ (nth_error_in Hnthb))|})
                             (val {| wht := ABNode (RS clbb sbb) descsb; Hwht := Htr |})).
  apply/orP. right. apply/hasP. exists (ABNode (RS clt st) descss). 
  apply/nth_error_in/Hnthb. by apply/orP;left.
  have Htrdedb := (trace_sem_prev_trees Htrded Hsubtree). 
  assert (Hcltin : clt \in [seq cl <- pb | hsym_cl cl == f] ).
  rewrite mem_filter. apply/andP;split. apply/eqP/Hsymeq.
  by apply (@tr_cl_in _ _ _ _ _ st _ _ Htrdedb). 
  destruct (all_prop_in (Hprev Hsafe Hvns Hsafe_hds Hnottriv (subxx _) (ppt_sizes Hppt)) Hcltin) as [vt [Hnthvt [ntyp [Hntypin Hntyp]]]].
  assert (Hcltinb : clt \in pb). rewrite mem_filter in Hcltin. by destruct (andP Hcltin).  
  assert (Hvthead : vt \in atom_vars (head_cl clt)). 
  apply/bigcup_seqP. exists (Var vt). apply (nth_error_in Hnthvt). apply/andP;split. by apply/set1P. trivial.
  have Hvtin := (subsetP (allP Hsafe clt Hcltinb) vt Hvthead).
  assert (Htriv : @eq (sum rul_gr gatom) (@inl rul_gr gatom (RS clt st))
              (@inl rul_gr gatom (RS clt st))). reflexivity. 
  destruct (existsP (Hntyp _ _ st Htrdedb Hvtin Htriv)) as [ctb Hctb].
  destruct (andP Hctb) as [Hctbin Hctbm]. clear Hctb. simpl in *.
  destruct (andP Hctbm) as [Hctb1 Hctb2]. clear Hctbm.  
  apply/existsP.

  have Htoccb := (notInTDisj_fold Hnottriv Htocc Hntypin).

  assert (Htoccconjb : [forall b, (b \in ctb) ==> (negb
                             (@in_mem (t_occ pb) tocc (@mem
                                   (Equality.sort (Finite.eqType (t_occ_finType pb)))
                                   (seq_predType (Finite.eqType (t_occ_finType pb)))
                                   (@useq (Finite.eqType (t_occ_finType pb))
                                      b))))]).
  assert (Hter : Din ctb ntyp). 
  unfold Din. destruct ntyp. by rewrite in_set0 in Hctbin. 
  apply Hctbin.  
  apply (implyP (forallP Htoccb ctb) Hter). 
 
  exists (@tInsert_conj _ tocc ctb Htoccconjb).

  have Hinctb := (ct_in_fold_disj Hctbin Hntypin Hnottriv). 
  move:Hnottriv.
  destruct (fold_type_alg DtDisj typs DEmpty) as [[|d]];
  move=>// Hnottriv.   
  apply/andP;split.
  apply/imsetP. exists (@exist _ _ ctb Hinctb).
  unfold equip. rewrite in_set mem_pmap.
  apply/mapP. exists ctb. rewrite mem_enum. apply Hinctb.
  unfold insub. destruct idP as [Hf|Hf]. by apply/f_equal/val_inj.
  exfalso. apply Hf. apply Hinctb. apply/f_equal/Eqdep_dec_bool.
  
  apply/andP;split. 
  apply/forallP=>x. apply/implyP=>/imsetP [y Hy ->] //.
  apply/forallP=>part. 
  apply/implyP=>/imsetP [brb /imsetP [[brbb Hbrbbin] Hbrbbinb ->] ->].
  apply/andP;split.
  apply/forallP=>br. rewrite in_set. 
  apply/implyP=>/andP [/imsetP [[x Hxin] Hxinb ->]] /=.
  destruct tocc as [rind bind tind]. move=>Htrivb.
  apply/existsP. exists ({| r_ind := rind; b_ind := bind; t_ind := tind |}). 
  apply/andP;split. auto. apply/eqP/Hnth.
  apply/existsP. exists (b_ind tocc).
  apply/andP;split. 
  apply/forallP=>br. rewrite in_set. 
  apply/implyP=>/andP [/imsetP [[x Hxin] Hxinb ->]] /=.
  destruct tocc as [rind bind tind]. move=>Htrivb. auto.
  rewrite Hnthb. apply/andP;split. 
  apply/forallP=>x. apply/implyP=>/imsetP [y]. rewrite in_set. 
  move=>/andP [/imsetP [z Hz ->]] /=. destruct tocc as [rind bind tind].
  move=> Htrivt -> /=. apply (implyP (forallP Hctb1 _)).
  destruct z as [z Hzb]. apply Hzb.
  assert (Hctbeq : [set useq_behead x
            | x in [set y in tInsert_conj (al:=tocc) (t:=ctb) Htoccconjb | 
          br_h_b_eq
            (ucons (t:=tocc)
               (b:=sval
                     (exist (fun x : dbranch pb => (mem ctb) x) brbb Hbrbbin))
               (implyP
                  (forallP Htoccconjb
                     (sval
                        (exist (fun x : dbranch pb => (mem ctb) x) brbb
                           Hbrbbin)))
                  (proj2_sig
                     (exist (fun x : dbranch pb => (mem ctb) x) brbb Hbrbbin))))
            y]] = ctb).
  apply/eqP;rewrite eqEsubset. apply/andP;split;apply/subsetP=>y.
  move=>/imsetP [z]. rewrite in_set. move=>/andP [/imsetP[t Ht ->]] /= Hbrq ->.
  destruct t as [t Htin]. simpl in *.
  assert (Hteq : {| useq := t; buniq := uniq_behead (s:=tocc :: t)
           (andP_to_uniq  (conj (implyP (forallP Htoccconjb t) Htin) (buniq t))) |} = t).
  by apply/val_inj. rewrite Hteq. apply Htin.
  move=>Hy. apply/imsetP. exists (ucons (t:=tocc)
  (b:=sval (exist (fun x : uniq_seq_finType => (mem ctb) x) y Hy))
  (implyP
     (forallP Htoccconjb
        (sval (exist (fun x : uniq_seq_finType => (mem ctb) x) y Hy)))
     (proj2_sig (exist (fun x : uniq_seq_finType => (mem ctb) x) y Hy)))). rewrite in_set. 
  apply/andP;split. apply/imsetP. exists (exist _ y Hy). 
  rewrite in_set mem_pmap. apply/mapP. exists y. rewrite mem_enum. apply Hy.
  unfold insub. destruct idP as [Hf|Hf]. by apply/f_equal/val_inj.
  exfalso. apply Hf. apply Hy. 
  reflexivity.
  destruct tocc. simpl. auto. by apply/val_inj.
   
  rewrite Hctbeq. 
  assert (H : vtr_brs_eq
          (ABNode (RS clt st) descss) ctb (ABheight (ABNode (RS clt st) descss)).+1).
  apply vtr_brs_eq_height. exists ((foldr maxn 0 [seq ABheight i | i <- descss]).+2). 
  simpl. apply/andP;split. apply Hctb1. apply Hctb2.
  assert (Hheight : ABheight (ABNode (RS clt st) descss) < ABheight (ABNode (RS clbb sbb) descsb)).
  apply sstree_height. apply/hasP. exists (ABNode (RS clt st) descss).
  apply/nth_error_in/Hnthb. apply subtree_refl. 
  have Hb :=  (vtr_brs_eq_more H Hheight).
  simpl in Hb. destruct (andP Hb) as [H1 H2]. 
  apply H2. 
- move=>pb vb ctxt ip  pred new_cl j typs Hppt Hprev Hneqpred Hsafe Hvns Hsafe_hds Hntriv Hsub Hsize.
  simpl. destruct (bool_des_rew (hsym_cl new_cl == pred)) as [Hpeq|Hneq].
  rewrite (eqP Hpeq) in Hneqpred. exfalso. by apply Hneqpred.
  rewrite Hneq. apply Hprev;auto. apply/subsetP=>x Hx. apply/(subsetP Hsub x)/mem_body/Hx.
  simpl in Hsize. rewrite Hneq in Hsize. apply Hsize. 

- move=>pb vb ctxt ip  new_cl j typs ntyp v' Hppt Hprev Hnth Hvt H 
  Hsafe Hvns Hsafe_hds Hntriv Hsub Hsize /=.
  rewrite eq_refl. split.
  + exists v'. split. apply/eqP/Hnth.
    exists ntyp. split. rewrite in_cons;apply/orP;by left.
    move=> trb clb sb Htrdedb Hvib Hrootb. 
    assert (Hntrivb : [exists tr, val ntyp == Tr (p:=pb) tr]).
    destruct ntyp as [[|tr]]. exfalso. by apply Hntriv.
    apply/existsP. by exists tr.   
    apply (H Hsafe Hvns Hsafe_hds trb clb sb Htrdedb Hrootb Hntrivb Hvib).
  + assert (Hsubb : ip \subset pb). 
    apply/subsetP=>x Hx. apply (subsetP Hsub x). rewrite in_cons. 
    apply/orP;right;apply Hx. simpl in Hsize.
    rewrite eq_refl in Hsize. simpl in Hsize. unfold oapp in Hsize.
    rewrite (eqP Hnth) in Hsize. simpl in Hsize. 
    inversion Hsize as [Hsizeb].
    assert (Hntrivt : val (fold_type_alg DtDisj typs DEmpty) <> Triv pb).
    move:Hntriv. simpl. unfold tDisj. destruct ntyp as [[|]]; move=>//=.
    destruct (fold_type_alg DtDisj typs DEmpty) as [[|]];move=>//.
    apply (all_prop_prop_decr (Hprev Hsafe Hvns Hsafe_hds Hntrivt Hsubb Hsizeb)).
    move=>cl Hclin [vl [H1 [typb [H2 H3]]]].
    exists vl. split. apply H1. exists typb. split.
    rewrite in_cons. apply/orP;right. apply H2. apply H3. 
Qed.

(** [semt_exists_ad_mintype] with a subtype *)
Lemma semt_exists_ad_type (tr : trace_sem_trees dga) def k cl s :
   tr \in sem_t p dga def k i
-> ABroot (val tr) = inl (RS cl s)
-> [forall v in typed_vars c_var_typing :&: tail_vars (body_cl cl), 
    [exists ct in dt_get_dcb (var_typ (c_var_typing v)), 
      (vtr_brs_eq (val tr) ct (ABheight (val tr)).+1)]].
Proof.
move=> Htrin Htreq. apply/forallP=>v. apply/implyP=> /setIP [Hvtyped Hvincl].
unfold typed_vars in Hvtyped. rewrite in_set in Hvtyped.
destruct ((c_var_typing v)) as [typ mintyp Hsub Htyping].
assert (Hvmtyped : [exists t, val mintyp == Tr (p:=p) t]).
destruct (existsP Hvtyped) as [x Hx].
have Hxx := eqP Hx. destruct typ as [|]; inversion Hxx as [H].
destruct (subtype_Tr Hsub) as [y [Hy1 Hy2]]. apply/existsP.
exists y. apply/eqP/Hy1.
simpl in Hvtyped. simpl var_typ. 
destruct (existsP (semt_exists_ad_mintype Htyping Hvmtyped Hvincl Htrin Htreq))
  as [c Hc]. destruct (andP Hc) as [Hc1 Hc2].
destruct typ as [|typ]. 
destruct (existsP Hvtyped) as [x Hf]. have Hff := eqP Hf. inversion Hff.
apply/existsP.
destruct (dt_get_dcb_subtype Hsub Hc1 Hvtyped) as [x [Hx1 Hx2]].
exists x. apply/andP;split.
apply Hx1.
apply (vtr_brs_eq_decr_brs Hc2). apply (csub_subset Hx2).
Qed.

End trace_cap.

(** ** Types and derivation adequacy *)

Section br_pred.

(** [br_pred br] iff for evey [....; a; b; ... ] occurence in branch [br], if
   [b] refers to some clause [cl] and variable [v], then [v] appears in
   the head of [cl] at the term position indicated by the term position in
   [a] *)
Fixpoint br_pred {p'} (br : seq (t_occ p')) := match br with
  | a :: (b :: _) as tl =>
    [forall v, (t_at a == Some (Var v)) ==>
     [forall v', (t_at b == Some (Var v')) ==>
      [forall cl, ((nth_error p' (r_ind b)) == Some cl) ==>
        (nth_error (arg_atom (head_cl cl)) (t_ind a) == Some (Var v'))]]]
   && (br_pred tl)
  | _ => true end.

(** Let [tr = ABNode (cl,s) l] be a trace in the semantics of [p] for [i]
  and [ct] verifying [vtr_brs_eq tr ct], let [br] a branch in [ct]
  verifying [br_pred] and where all [toccs] refer to actual variables,
  the first one referring to [v], then there is [ga] in [i], such
  that for all branch [br'] [dep]-equivalent to [br] and verifying
  [br_pred], the variable identified by the head of [br'] can be
  matched with the right term in [ga] by [s] *)
Lemma sem_t_vtr_exists_ga cl s l Htr def k v br ct tocc :
   {| wht := ABNode (RS cl s) l; Hwht := Htr |}
              \in sem_t p dga def k i
-> vtr_brs_eq (val {| wht := ABNode (RS cl s) l; Hwht := Htr |})
           ct (ABheight (ABNode (RS cl s) l)).+1
(*-> ct \in dt_get_dcb (var_typing p v)*)
-> br \in ct
-> br_pred br
-> all (fun x => [exists v', (t_at x) == (Some (Var v'))]) br
-> nth_error (val br) 0 = Some tocc
-> t_at tocc = Some (Var v)
-> [exists ga in i, [forall breq, dep breq br ==> br_pred breq
             ==> all (fun x => [exists v', (t_at x) == (Some (Var v'))]) breq
             ==> [exists toccb, (nth_error (val breq) 0 == Some toccb)
                            && [exists v', (t_at toccb == Some (Var v'))
                                         && @ga_match_br p ga breq v' s]]]].
Proof.
move:br ct v s cl l tocc Htr.
induction k as [|k Hk].
move=> br ct v s cl l tocc Htr /imsetP [x] //.
move=> br ct v s cl l tocc Htr Hsemt.
pose Hsemt_cop := Hsemt. clearbody Hsemt_cop. move:Hsemt.
move=>/setUP [Hrec|].
by apply Hk.
move=>/bigcup_seqP [ccl hcclin /andP [/mem_pset_set /imset2P [descs ss Hdescsin]]].
rewrite in_set. move=>/andP [Hssmatch /andP [Hded Hall]].
unfold wu_pcons_seq. unfold wu_pcons_wlist. destruct Sumbool.sumbool_of_bool;
move=>// [Hcleq Hseq Hleq] Htriv /= Heq (*Hctin*) Hbrin Hbrpred Hallv. clear Htriv.
assert (Hpart : [set y in ct | br_h_b_eq br y] \in equivalence_partition (T:=dbranch p) br_h_b_eq ct).
apply/imsetP. exists br. apply Hbrin. auto.
move:Heq. move=>/andP [Hallsize Heq].
destruct (andP (implyP (forallP Heq [set y in ct | br_h_b_eq br y]) Hpart)) as [Hparthead H].
destruct (existsP H) as [pk Hpk]. clear H.
destruct (andP Hpk) as [Hparteq Hpartrec]. clear Hpk.
destruct (nth_error_case l pk) as [Hnone|[[gab|[ncl ns] nl] [Hnin Hneq]]].
- rewrite Hnone in Hpartrec. inversion Hpartrec.
  (* the under-tree is a leaf, carrying the desired gatom *)
- move=>Hbreq Htat.
  rewrite Hneq in Hpartrec.
  assert (Hbrbhd : val (useq_behead br) == [::]).
  apply (implyP (forallP Hpartrec (useq_behead br))).
  apply/imsetP. exists br. rewrite in_set. apply/andP;split.
  apply Hbrin. destruct br as [[|[]]]. inversion Hbreq. by simpl. auto.
  destruct br as [[|hbr tlbr] Hbr]. inversion Hbreq.
  simpl in Hbrbhd. simpl.
  apply/existsP. exists gab. apply/andP;split.
  assert (Hsemtb :
    {|wht := ABLeaf rul_gr gab ; Hwht := @wu_pred_leaf rul_gr_eqType _ bn (ABLeaf rul_gr gab) |} \in sem_t p dga def k.+1 i).
  apply (trace_sem_prev_trees Hsemt_cop). apply/orP;right. apply/hasP. exists (ABLeaf rul_gr gab).
  apply Hnin. auto.
  apply (sem_t_leaf Hsemtb).
  apply/forallP=>breq. unfold dep. apply/implyP=>/= Hdep.
  rewrite (eqP Hbrbhd) in Hdep. destruct (andP Hdep) as [Hdep1 Hdep2].
  pose Hdep1b := eqP Hdep1. clearbody Hdep1b. clear Hdep1.
  destruct breq as [[|hbreq [|mbreq tlbreq]] Hbreqd]; try (inversion Hdep1b).
  inversion Hbreq as [Htocc]. clear Hpartrec. apply/implyP=>Hbrpredd.
  apply/implyP=>/= /andP [Hallbreq Htriv]. clear Htriv.
  apply/existsP. exists hbreq. apply/andP;split. auto.
  apply/existsP. destruct (existsP Hallbreq) as [vd Hvd].
  exists vd. apply/andP;split. apply Hvd.
  unfold ded_sub_equal in Hded.
  unfold t_at in Htat. unfold at_at in Htat.
  unfold t_at in Hvd. unfold at_at in Hvd.
  assert(Hin: ({| useq := hbr :: tlbr; buniq := Hbr |}
          \in [set y in ct | br_h_b_eq {| useq := hbr :: tlbr; buniq := Hbr |} y])).
  rewrite in_set. apply/andP;split. apply Hbrin. simpl. by destruct hbr.
  destruct (existsP (implyP (forallP Hparthead {| useq := hbr :: tlbr; buniq := Hbr |}) Hin))
    as [toccb Htb]. clear Hparthead. clear Hbrin.
  destruct (andP Htb) as [Htb1 Htb2]. clear Htb.
  simpl in Htb1. pose Htb3 := eqP Htb1. inversion Htb3 as [Htbeq].
  rewrite -Htbeq Htocc in Htb2. clear Htbeq. clear Htb3. clear Htb1. clear toccb.
  rewrite (eqP Htb2) in Htat.
  simpl in Hdep2. destruct (andP Hdep2) as [Hdep2b Htriv]. clear Hdep2. clear Htriv.
  unfold pred_occ in Hdep2b. pose Hdep2t := eqP Hdep2b. inversion Hdep2t as [[Hreq Hbeq]].
  rewrite -Htocc -Hreq in Htb2. rewrite (eqP Htb2) in Hvd.
  destruct (nth_error_case (body_cl cl) (b_ind tocc)) as [Hnone|[ato [Hatoin Hatoeq]]].
  by rewrite Hnone in Htat.
  rewrite Hbeq Htocc Hatoeq in Hvd.
  rewrite Hatoeq in Htat.
  rewrite Hcleq in Hatoeq.

  rewrite seq_wlistK in Hleq.
  rewrite Hleq in Hnin. (*destruct (mapP Hnin) as [lfd Hlfdin Hlfdeq].*)
  rewrite Hleq in Hneq.
  destruct (nth_error_preim Hneq) as [lfd [Hlfdin Hlfdeq]].
  pose H1 := (nth_error_map (fun x => ded (gat_def:=dga) def x) Hlfdin). clearbody H1.
  simpl in H1.

  pose Hatoeqb := (nth_error_map (fun x => gr_atom_def def ss x) Hatoeq). clearbody Hatoeqb.
  rewrite -(eqP Hded) in Hatoeqb.

  pose Hpk := (implyP (forallP Hparteq  {| useq := hbr :: tlbr; buniq := Hbr |}) Hin).
  destruct hbr as [rind bind aind].
  simpl in Hpk. clearbody Hpk. rewrite -(eqP Hpk) in H1.
  destruct tocc as [rindb bindb aindb]. simpl in Hbreq.
  inversion Hbreq as [[Hrindeq Hbindeq Haineq]].
  simpl in *. rewrite -Hbindeq in Hatoeqb.
  rewrite -Hseq H1 in Hatoeqb. inversion Hatoeqb as [Hdedeq].
  destruct lfd as [lfd Hlfd]. unfold ded in Hdedeq. simpl in Hdedeq.
  simpl in Hlfdeq. rewrite Hlfdeq in Hdedeq. rewrite Hdedeq.
  rewrite -Hseq in Hssmatch.
  pose Hdom := match_vars_subset Hssmatch. clearbody Hdom.
  rewrite -Hcleq in Hdom.
  destruct hbreq. simpl in Hvd.
  assert (Hvin : vd \in tail_vars (body_cl cl)).
  apply/bigcup_seqP. exists ato. apply Hatoin. apply/andP;split;trivial.
  apply/bigcup_seqP. exists (Var vd). apply (nth_error_in (eqP Hvd)).
  apply/andP;split;trivial. by apply/set1P.
  pose Hdomb := ((subsetP Hdom _) Hvin). clearbody Hdomb. clear Hdom. clear Hvin.
  destruct (sub_elim s vd) as [[c Hc]|Hnone]. rewrite Hc.
  unfold gr_atom_def. simpl. rewrite (nth_error_map (fun x => gr_term_def def s x) (eqP Hvd)).
  simpl in *.
  unfold p_at. unfold at_at.
  rewrite (eqP Htb2) Hcleq Hbeq Hbindeq Hatoeq. apply/andP;split.
  auto.
  apply/eqP/f_equal. simpl. by rewrite Hc.
  unfold dom in Hdomb. by rewrite in_set Hnone in Hdomb.
  destruct descs as [d Hd]. rewrite (eqP Hd). apply wlist_to_seq_size.
- move=>Hbreq Htat. assert (Hbr_refl : br_h_b_eq br br). destruct br as [[|[]]]. inversion Hbreq.
  simpl. auto.
  rewrite Hneq in Hpartrec.
  assert (Hnt_wu : @wu_pred _ _ bn (ABNode (RS ncl ns) nl)).
  apply wu_pred_sub with (t2 := (ABNode (RS cl s) l)).
  apply/orP;right. apply/hasP. exists (ABNode (RS ncl ns) nl). apply Hnin.
  by apply/orP;left. apply Htr.


  assert (Hss : strict_subtree (ABNode (RS ncl ns) nl) (ABNode (RS cl s) l)).
  apply/hasP. exists (ABNode (RS ncl ns) nl). apply Hnin. apply subtree_refl.
  assert (Hnsem_t : {| wht := (ABNode (RS ncl ns) nl); Hwht := Hnt_wu |} \in sem_t p dga def k i).
  apply (trace_sem_prev_trees_m1 Hsemt_cop). apply Hss.

 assert (Hpartn : [set y in [set useq_behead x0
                | x0 in [set y0 in ct | br_h_b_eq br y0]] |
                   br_h_b_eq (useq_behead br) y]
                \in equivalence_partition (T:=dbranch p) br_h_b_eq
                    [set useq_behead x | x in [set y in ct | br_h_b_eq br y]]).
  apply/imsetP. exists (useq_behead br). apply/imsetP. exists br. rewrite in_set.
  apply/andP;split. apply Hbrin. apply Hbr_refl. reflexivity. auto.

  destruct (andP Hpartrec) as [Hsize Hrec].
  destruct br as [[|hbr [|mbr tlbr]] Hbr]. inversion Hbreq.
  assert (Hf1 : ((useq_behead {| useq := [:: hbr]; buniq := Hbr |}) \in
    [set useq_behead x0 | x0 in [set y in ct | br_h_b_eq {| useq := [:: hbr]; buniq := Hbr |} y]])).
  apply/imsetP. exists {| useq := [:: hbr]; buniq := Hbr |}. rewrite in_set. apply/andP;split.
  apply Hbrin. by destruct hbr. reflexivity.
  pose Hf := implyP (forallP Hsize (useq_behead {| useq := [:: hbr]; buniq := Hbr |})) Hf1.
  inversion Hf.
  (* br = [:: hbr mbr tlbr] *)
  assert (Hmbrin : mbr \in val {| useq := [:: hbr, mbr & tlbr]; buniq := Hbr |}).
  rewrite in_cons. apply/orP;right. rewrite in_cons. by apply/orP;left.
  destruct (existsP (allP Hallv mbr Hmbrin))
    as [v' Hv'].
  pose Hv'_cop := Hv'. clearbody Hv'_cop.
  assert (Hallvb : all (fun x : t_occ p => [exists v', t_at x == Some (Var v')])
         (useq_behead {| useq := [:: hbr, mbr & tlbr]; buniq := Hbr |})).
  by destruct (andP Hallv).
  assert (Hheadmb : nth_error  (val (useq_behead
               {| useq := [:: hbr, mbr & tlbr]; buniq := Hbr |})) 0 = Some mbr).
  auto.

  assert (Hpartb : ([set y in [set useq_behead x0
                     | x0 in [set y0 in ct | br_h_b_eq
                                               {|
                                               useq := [:: hbr, mbr & tlbr];
                                               buniq := Hbr |} y0]] |
        br_h_b_eq
          (useq_behead {| useq := [:: hbr, mbr & tlbr]; buniq := Hbr |}) y]
          \in [set [set y in [set useq_behead x0
                                | x0 in [set y0 in ct |
                              br_h_b_eq
                                {|
                                useq := [:: hbr, mbr & tlbr];
                                buniq := Hbr |} y0]] |
               br_h_b_eq x y]
                 | x in [set useq_behead x
                           | x in [set y in ct | br_h_b_eq
                                                 {|
                                                 useq := [:: hbr, mbr & tlbr];
                                                 buniq := Hbr |} y]]])).
  apply/imsetP. exists (useq_behead  {| useq := [:: hbr, mbr & tlbr]; buniq := Hbr |}).
  apply/imsetP. exists {| useq := [:: hbr, mbr & tlbr]; buniq := Hbr |}.
  rewrite in_set. apply/andP;split. apply Hbrin. by destruct hbr. reflexivity.
  reflexivity.

  destruct (andP (implyP (forallP Hrec _) Hpartb))
    as [Hrecb1 Hrecb2].
  destruct (existsP Hrecb2) as [kb Hbk].



  assert (Hreck : (vtr_brs_eq
             (val {| wht := ABNode (RS ncl ns) nl; Hwht := Hnt_wu |})
             [set useq_behead x | x in [set y in ct | br_h_b_eq {| useq := [:: hbr, mbr & tlbr]; buniq := Hbr |} y]]
             (ABheight (ABNode (RS ncl ns) nl)).+1)).

  apply/andP;split.
  + apply/forallP=>x. destruct hbr as [rhbr bhbr ahbr]. apply/implyP=>/imsetP [brb]. rewrite in_set.
    move=>/andP [Hbrbin]. destruct brb as [[|[]]]. auto. move=>/eqP H ->. simpl.
    apply (implyP (forallP Hsize (useq_behead {| useq := {| r_ind := r_ind; b_ind := b_ind; t_ind := t_ind |} :: l0; buniq := buniq |}))).
    apply/imsetP. exists {| useq := {| r_ind := r_ind; b_ind := b_ind; t_ind := t_ind |} :: l0; buniq := buniq |}.
    rewrite in_set. apply/andP;split. apply Hbrbin. by simpl;rewrite H. reflexivity.
  + apply/forallP=>part. apply/implyP=>Hpartin.
    destruct (andP (implyP (forallP Hrec part) Hpartin)) as [Hphead Hpex].
    apply/andP;split.
    - apply Hphead.
    - destruct (existsP Hpex) as [kp Hkp].
      destruct (andP Hkp) as [Hkp1 Hkp2]. clear Hpex. clear Hkp.
      apply/existsP. exists kp.
      apply/andP;split. apply Hkp1.
      destruct (nth_error_case nl kp) as [Hnone|[trb [Htrbin Htrbeq]]]. by rewrite Hnone in Hkp2.
      rewrite Htrbeq in Hkp2. rewrite Htrbeq.
      assert (Hex : exists h, vtr_brs_eq trb [set useq_behead x | x in pred_of_set part] h).
      exists (foldr maxn 0 [seq ABheight i | i <- l]). apply Hkp2.
      pose Hrex := (vtr_brs_eq_height Hex).
      assert (Hheight : ABheight trb < (foldr maxn 0 [seq ABheight i | i <- nl]).+1).
      rewrite ltnS. apply/fold_maxn_n_map_geq/hasP. exists trb. apply Htrbin.
      auto.
      apply (vtr_brs_eq_more Hrex Hheight).

  assert (Hbrinb : (useq_behead {| useq := [:: hbr, mbr & tlbr]; buniq := Hbr |}
             \in [set useq_behead x
                    | x in [set y in ct | br_h_b_eq
                                            {|
                                            useq := [:: hbr, mbr & tlbr];
                                            buniq := Hbr |} y]])).
  apply/imsetP. exists {| useq := [:: hbr, mbr & tlbr]; buniq := Hbr |}.
  rewrite in_set. apply/andP;split. apply Hbrin. by destruct hbr.
  reflexivity.

  assert (Hbrinbb : useq_behead {| useq := [:: hbr, mbr & tlbr]; buniq := Hbr |}
         \in [set y in [set useq_behead x0
                          | x0 in [set y0 in ct | br_h_b_eq {| useq := [:: hbr, mbr & tlbr]; buniq := Hbr |} y0]] |
       br_h_b_eq (useq_behead {| useq := [:: hbr, mbr & tlbr]; buniq := Hbr |}) y]).
  rewrite in_set. apply/andP;split. apply/imsetP. exists {| useq := [:: hbr, mbr & tlbr]; buniq := Hbr |}.
  rewrite in_set. apply/andP;split. apply Hbrin. by destruct hbr. reflexivity. by destruct mbr;simpl.


  destruct (andP Hbrpred) as [Hbrpredh Hbrpredb]. clear Hbrpred.

  destruct (existsP ((@Hk (useq_behead {| useq := hbr :: mbr :: tlbr; buniq := Hbr |})
          _ v' ns ncl nl mbr Hnt_wu Hnsem_t Hreck) Hbrinb Hbrpredb Hallvb Hheadmb (eqP Hv')))
    as [ga Hga]. destruct (andP Hga) as [Hgain Hgamatch]. clear Hga.
  apply/existsP. exists ga. apply/andP;split. apply Hgain.

  apply/forallP=>breq. apply/implyP=>Hdep. apply/implyP=>Hbrpedd. apply/implyP=>Halldep.

  destruct breq as [[|hbreq [|mbreq tlbreq]] Hbreqd];unfold dep in Hdep; simpl in Hdep;
  try (by inversion Hdep).

  assert (Hdepb : dep (p:=p) (useq_behead {| useq := [:: hbreq, mbreq & tlbreq]; buniq := Hbreqd |})
                             (useq_behead {| useq := [:: hbr, mbr & tlbr]; buniq := Hbr |})).
  unfold dep. simpl. destruct (andP Hdep) as [Hdep1 Hdep2]. destruct (andP Hdep2) as [Hdep3 Hdep4].
  destruct (andP Hdep4) as [Hdep5 Hdep6].
  apply/andP;split. apply Hdep1. apply/andP;split. apply Hdep5. apply Hdep6.

  assert (Halldb : all (fun x : t_occ p => [exists v', t_at x == Some (Var v')])
         (useq_behead {| useq := [:: hbreq, mbreq & tlbreq]; buniq := Hbreqd |})).
  by destruct (andP Halldep).

  assert (Hbrpreddb : (br_pred (useq_behead {| useq := [:: hbreq, mbreq & tlbreq]; buniq := Hbreqd |}))).
  by destruct (andP Hbrpedd).

  destruct (existsP (implyP (implyP (implyP (forallP Hgamatch _) Hdepb) Hbrpreddb) Halldb)) as
    [toccb Htoccb]. destruct (andP Htoccb) as [Htoccb_nth Hvmatch].  clear Htoccb.
  apply/existsP. exists hbreq. destruct (existsP Hvmatch) as [vhb Hvhb]. clear Hvmatch.
  simpl in Htoccb_nth. pose Htoccb_nthb := eqP Htoccb_nth. inversion Htoccb_nthb as [Hmbreqtoccb].
  clear Htoccb_nthb. clear Htoccb_nth.
  apply/andP;split. auto. apply/existsP.
  destruct (andP Halldep) as [Halldep1 Halldep2]. clear Halldep.
  destruct (existsP Halldep1) as [vhbb Hvhbb]. exists vhbb. apply/andP;split.
  apply Hvhbb.
  destruct (existsP (implyP (forallP Hrecb1 (useq_behead {| useq := [:: hbr, mbr & tlbr]; buniq := Hbr |})) Hbrinbb))
    as [toccn Htoccn]. destruct (andP Htoccn) as [Htoccneq Hnthn]. clear Htoccn.
  unfold t_at in Hv'. unfold at_at in Hv'. simpl in Htoccneq. pose Htoccneqb := eqP Htoccneq. clearbody Htoccneqb.
  inversion Htoccneqb as [Htoccneqt]. clear Htoccneqb. clear Htoccneq. rewrite Htoccneqt (eqP Hnthn) in Hv'.

  rewrite -Htoccneqt in Hv'. rewrite -Htoccneqt in Hnthn.
  simpl. simpl in Hgamatch.
  assert (Hsubeq : ns vhb = s vhbb).

  unfold ded_sub_equal in Hded. (*pose Htat_cop := Htat. clearbody Htat_cop.*)
  pose Hvtat_cop := Hvhbb. clearbody Hvtat_cop.
  unfold t_at in Htat. unfold at_at in Htat.
  unfold t_at in Hvhbb. unfold at_at in Hvhbb.
  assert(Hin: ({| useq := hbr :: mbr :: tlbr; buniq := Hbr |}
          \in [set y in ct | br_h_b_eq {| useq := hbr :: mbr :: tlbr; buniq := Hbr |} y])).
  rewrite in_set. apply/andP;split. apply Hbrin. simpl. by destruct hbr.
  destruct (existsP (implyP (forallP Hparthead {| useq := hbr :: mbr :: tlbr; buniq := Hbr |}) Hin))
    as [tocct Htb]. clear Hparthead. clear Hbrin.
  destruct (andP Htb) as [Htb1 Htb2]. clear Htb.
  simpl in Htb1. pose Htb3 := eqP Htb1. inversion Htb3 as [Htbeq].
  inversion Hbreq as [Htocc]. destruct (andP Hdep) as [Hdep1 Hdep2].
  destruct (andP Hdep2) as [Hdep3 Hdep4]. pose Hdep5 := eqP Hdep3.
  inversion Hdep5 as [[Hdep6 Hdep7]]. clear Hdep5. clear Hdep3. clear Hdep2. clear Hdep.
  rewrite Hdep6 Htbeq (eqP Htb2) in Hvhbb.
  (*destruct (andP Hdepb) as [Hdepb1 Hdepb2]. destruct (andP Hdepb2) as [Hdepb3 Hdepb4].
  clear Hdepb. clear Hdepb2. pose Hdepb5 := eqP Hdepb3. inversion Hdepb5 as [[Hdepb6 Hdepb7]].
  clear Hdepb5. clear Hdepb3. rewrite Hdepb6 Htoccneqt (eqP Hnthn) in Hvhbb1.
  rewrite (eqP Htb2) in Htat. *)
  destruct (nth_error_case (body_cl cl) (b_ind hbreq)) as [Hnone|[ato [Hatoin Hatoeq]]].
  by rewrite Hnone in Hvhbb. rewrite Hatoeq in Hvhbb.
  rewrite Hcleq in Hatoeq.

  rewrite seq_wlistK in Hleq.
  rewrite Hleq in Hnin. (*destruct (mapP Hnin) as [lfd Hlfdin Hlfdeq].*)
  rewrite Hleq in Hneq.
  destruct (nth_error_preim Hneq) as [lfd [Hlfdin Hlfdeq]].
  pose H1 := (nth_error_map (fun x => ded (gat_def:=dga) def x) Hlfdin). clearbody H1.
  simpl in H1.

  pose Hatoeqb := (nth_error_map (fun x => gr_atom_def def ss x) Hatoeq). clearbody Hatoeqb.
  rewrite -(eqP Hded) in Hatoeqb.

  pose Hpk := (implyP (forallP Hparteq  {| useq := hbr :: mbr:: tlbr; buniq := Hbr |}) Hin).
  destruct hbr as [rind bind aind].
  simpl in Hpk. clearbody Hpk. rewrite -(eqP Hpk) in H1.
  destruct tocc as [rindb bindb aindb]. simpl in Hbreq.
  inversion Hbreq as [[Hrindeq Hbindeq Haineq]].
  simpl in *. rewrite Hdep7 in Hatoeqb.
  rewrite -Hseq H1 in Hatoeqb. inversion Hatoeqb as [Hdedeq].
  destruct lfd as [lfd Hlfd]. unfold ded in Hdedeq. simpl in Hdedeq.
  simpl in Hlfdeq. rewrite Hlfdeq in Hdedeq.

  destruct ncl as [hncl tlncl].
  unfold gr_atom_def in Hdedeq.
  inversion Hdedeq as [[Hsymeq Hargeq]]. clear Hdedeq.

  destruct hbreq. simpl in Hvhbb.

  pose Heqa := (nth_error_map (fun x => gr_term_def def s x) (eqP Hvhbb)). clearbody Heqa.
  rewrite -Hargeq in Heqa.
  destruct (nth_error_preim Heqa) as [tb [Htbin Htbeqb]].
  move:Hvtat_cop. simpl in Hdep6; simpl in Hdep7. rewrite Hdep6 Hdep7.

  simpl in Hnthn. move=>Hvtat_cop. destruct (andP Hbrpedd) as [Hbrpedd1 Hbrpedd2]. clear Hbrpedd.
  rewrite -Hdep6 -Hdep7 in Hvtat_cop. destruct (andP Hdep4) as [Hdep8 Hdep9]. clear Hdep4.
  pose Hdep10 := eqP Hdep8. inversion Hdep10 as [[Hdep11 Hdep12]]. clear Hdep10. clear Hdep8.
  rewrite -Hdep11 in Hnthn. destruct (andP Hvhb) as [Hvhb1 Hvhb2]. rewrite -Hmbreqtoccb in Hvhb1.
  rewrite (eqP (implyP (forallP (implyP (forallP (implyP (forallP Hbrpedd1 _) Hvtat_cop) _) Hvhb1) _) Hnthn))
    in Htbin.
  inversion Htbin as [Htbinb]. rewrite -Htbinb in Htbeqb.
  simpl in Htbeqb. unfold odflt in Htbeqb. unfold oapp in Htbeqb.
  destruct (sub_elim ns vhb) as [[c Hc]|Hnone];[|by rewrite Hnone in Hvhb2].
  assert (Hdom : vhbb \in dom s). rewrite Hseq. apply (subsetP (match_vars_subset Hssmatch)).
  apply/bigcup_seqP. exists ato. rewrite -Hcleq. apply Hatoin.
  apply/andP;split;auto. apply arg_atom_vars_in. apply (nth_error_in (eqP Hvhbb)).
  destruct (sub_elim s vhbb) as [[d Hd]|Hnone]. rewrite Hc Hd in Htbeqb.
  by rewrite Hc Hd Htbeqb. by rewrite in_set Hnone in Hdom.
  destruct descs as [descs Hdescs]. rewrite (eqP Hdescs).
  apply wlist_to_seq_size.
  destruct (andP Hvhb) as [Hvhb1 Hvhb2].
  destruct (sub_elim ns vhb) as [[c Hc]|Hnone].
  simpl in Hvhb2.
  rewrite Hc in Hvhb2. rewrite -Hsubeq Hc. apply Hvhb2.
  simpl in Hvhb2.
  by rewrite Hnone in Hvhb2.
Qed.

(** A type vefies [all_bpred], if all its branches in all its conjunct
  verify [br_pred] *)
Definition all_brpred {p'} (t : Dtype p') :=
  forall ct, ct \in dt_get_dcb t ->
    forall br, br \in pred_of_set ct -> br_pred br.

(** [all_brpred] is increasing wrt. its given type *)
Lemma all_brpred_incr {p'} (t1 t2 : Dtype p') :
  all_brpred t1 -> subtype t1 t2 -> all_brpred t2.
Proof.
move=>Hall Hsub. induction Hsub as [d1 d2 Hsub|].
move=>ct /= Hct br Hbr.
destruct (dsub_subset_rev Hsub Hct) as [x [Hx1 Hx2]].
apply (Hall x Hx1 br (subset_to_in Hbr (csub_subset Hx2))).
move=>x. by rewrite in_set0.
Qed.

(** If [progPredTyping v ip f j typs] for [ip] a subset of [p], then in
   any branch of any conjunct of [typs] seen as a disjunction, the head occurrence refers to a variable [v] in a clause [cl], then in the head
    of [cl], [v] appears at position [j] *)
Lemma ppt_v {p' ip} {ctxt : tocs p'} v f j (typs: seq (DDtype ctxt))
(Hppt : progPredTyping v ip f j typs) :
 prog_safe p' -> prog_safe_hds p' -> vars_not_shared p' ->
  ip \subset p' ->
  [forall ct in dt_get_dcb (fold_type_alg DtDisj typs DEmpty),
          [forall br in pred_of_set ct,
            [forall tocc, ((useq_hd br) == (Some tocc)) ==>
              [forall v, ((t_at tocc == Some (Var v)) ==>
                [forall cl, ((nth_error p' (r_ind tocc) == Some cl) ==>
                 ((nth_error (arg_atom (head_cl cl)) j) == Some (Var v)))])]]]].
Proof.
apply (@progPredTyping_mrec
  (fun p' (ctxt' : tocs p') v' (t : DDtype ctxt') (Hvt : varTyping v' t) => 
true)
  (fun p' v' (ctxt' : tocs p') (l : {set (enotin ctxt')}) (l0 : seq (DDtype ctxt')) (Hott : OccsToTypes v' l l0)
       => true)
  (fun p' v' (ctxt' : tocs p') (f : symtype) (o : 'I_max_ar) (d : (DDtype ctxt')) (Hpt : predTyping v'  f o d) 
     (* val d <> tInit p' -> forall tocc, P (insert tocc d) (et éventuellement P d en sus) *)
    => true)
  (fun p' v' (ctxt' : tocs p') ip' f (ind : 'I_max_ar) (l : seq (DDtype ctxt')) (Hppt : progPredTyping v' ip' f ind l)
      => prog_safe p' ->
prog_safe_hds p' ->
vars_not_shared p' -> ip' \subset p' -> [forall ct in dt_get_dcb (fold_type_alg DtDisj l DEmpty), 
          [forall br in pred_of_set ct,
            [forall tocc, ((useq_hd br) == (Some tocc)) ==>  
              [forall v, ((t_at tocc == Some (Var v)) ==> 
                [forall cl, ((nth_error p' (r_ind tocc) == Some cl) ==> 
                 ((nth_error (arg_atom (head_cl cl)) ind) == Some (Var v)))])]]]]))
with (ctxt := ctxt) (ip := ip) (f7 := f) (ind := j) (l := typs) (v := v);move=>//.
- intros. apply/forallP=>x. apply/implyP. by rewrite in_set0. 
- move=>pb v' ctb ip' new_cl j0 typs0 t Hpptb H1 H2 Hsafe Hsafehds Hvns Hsub.
  apply H1;auto. apply/subsetP=>x Hx. apply (subsetP Hsub x). apply/mem_body/Hx.  
- move=> pb vb ctb ip' new_cl j0 typs0 t v' Hpptb H1 Hnth Hvt Htriv Hsafe Hsafehds Hvns Hsub.
  assert (Hnclin : new_cl \in pb). apply/(subsetP Hsub)/mem_head.    
  simpl. unfold dt_get_dcb. unfold tDisj. 
  destruct t as [[|t]]. apply/forallP=>x. apply/implyP. by rewrite in_set0.
  move:H1. unfold dt_get_dcb. simpl. destruct (fold_type_alg DtDisj typs0) as [[|]];
  move=>/=H. apply/forallP=>x. apply/implyP. by rewrite in_set0. 
  apply/forallP=>y. apply/implyP. move=>/setUP [Hint|Hind].
  simpl in Hvt.
  apply/forallP=>br. apply/implyP=>Hbriny.
  apply/forallP=>tocc. apply/implyP=>Htocc.
  assert (Htoccb : nth_error br 0 == Some tocc). destruct br as [[|]]. inversion Htocc.
  apply Htocc. 
  apply/forallP=>vt. apply/implyP=>Htat. 
  have Hv:= (eqP (implyP (forallP (implyP (forallP (implyP (forallP (typing_v_head Hvt) _) Hint) _) Hbriny) _) Htoccb)).
  rewrite Hv in Htat. have Heq:= eqP Htat. inversion Heq as [Heqb].
  apply/forallP=>cl. apply/implyP=>Hcl. rewrite -Heqb. 
  clear H. clear Hdd0. 
  assert (Hcleq : cl = new_cl). apply vns_cl_eq with (p := pb) (v := vt).
  unfold t_at in Hv. unfold at_at in Hv. rewrite (eqP Hcl) in Hv.
  destruct (nth_error_case (body_cl cl) (b_ind tocc)) as [Hnone|[ato [Hatoin Hatoeq]]].
  rewrite Hnone in Hv. inversion Hv.
  apply/bigcup_seqP. exists ato. apply Hatoin. apply/andP;split;auto. 
  rewrite Hatoeq in Hv. destruct tocc. rewrite -Heqb. 
  apply/bigcup_seqP. exists (Var v'). apply (nth_error_in Hv).
  apply/andP;split;auto. by apply/set1P.
  apply (subsetP (allP Hsafe new_cl Hnclin)).
  rewrite -Heqb. 
  apply/bigcup_seqP. exists (Var v'). 
  apply (nth_error_in (eqP Hnth)). 
  apply/andP;split. by apply/set1P. auto.
  apply (nth_error_in (eqP Hcl)). 
  apply Hnclin. 
  auto. 
  rewrite Hcleq. apply Hnth.
  assert (Hsubb : ip' \subset pb). 
  apply/subsetP=>z Hz. apply/(subsetP Hsub)/mem_body/Hz. 
  apply (implyP (forallP (H Hsafe Hsafehds Hvns Hsubb) _) Hind). 
Qed. 

(** If [t] is a type for [v], it verifies [all_brpred] *)
Lemma typing_brpred {p'} {ctxt : tocs p'} (v : 'I_n) (t : DDtype ctxt) (Hvt : varTyping v t):
prog_safe p' -> prog_safe_hds p' -> vars_not_shared p' ->
  all_brpred t.
Proof.
apply (@varTyping_mrec
  (fun p' (ctxt' : tocs p') v' (t : DDtype ctxt') (Hvt : varTyping v' t) 
      => prog_safe p' -> prog_safe_hds p' -> vars_not_shared p' -> all_brpred t)
  (fun p' v' (ctxt' : tocs p') (l : {set (enotin ctxt')}) (l0 : seq (DDtype ctxt')) (Hott : OccsToTypes v' l l0)
       => [forall x in l, (t_at (val x)) == Some (Var v')]
          -> prog_safe p' -> prog_safe_hds p' -> vars_not_shared p' -> all_prop all_brpred (map val l0))
  (fun p' v' (ctxt' : tocs p') f (o : 'I_max_ar) (d : (DDtype ctxt')) (Hpt : predTyping v' f o d) 
     (* val d <> tInit p' -> forall tocc, P (insert tocc d) (et éventuellement P d en sus) *)
    => prog_safe p' -> prog_safe_hds p' -> vars_not_shared p' -> all_brpred d)
  (fun p' v' (ctxt' : tocs p') ip' f (ind : 'I_max_ar) (l : seq (DDtype ctxt')) (Hppt : progPredTyping v' ip' f ind l)
      => prog_safe p' -> prog_safe_hds p' -> vars_not_shared p' -> all_prop all_brpred (map val l))) with (o := v);move=>//; try (by intros;apply/forallP=>x;apply/implyP;rewrite in_set0).
- move=> pb ctb j vb lb Hlb. 
  assert (Hoccs: [forall tocc in (seq_to_enotin (occsInProgram pb vb) ctb), (t_at (val tocc)) == (Some (Var vb))]).
  apply/forallP=>o. apply/implyP=>Ho. apply/eqP. apply occsInProgramV. 
  destruct (imsetP (mem_pset_set Ho)) as [xocc Hxoccin Hxeq].
  unfold insub in Hxeq. destruct idP in Hxeq ; inversion Hxeq.
  apply Hxoccin. clear Hlb. move:Hoccs. 
  induction lb as [|[[|h]] l Hl]; move=> Hlb Hr Hsafe Hsafehds Hvns;
  move=>x. by rewrite in_set0. 
  move=>/= Hxin. 
  assert (Hrb : ([forall x in seq_to_enotin (occsInProgram pb vb) ctb, t_at (val x) == Some (Var vb)] ->
  prog_safe pb -> prog_safe_hds pb -> vars_not_shared pb -> all_prop all_brpred (map val l))).
  move=>H H1 H2 H3. by destruct (Hr H Hsafe Hsafehds Hvns). 
  apply (Hl Hlb Hrb Hsafe Hsafehds Hvns). apply Hxin.
  simpl. destruct (fold_type_alg DtConj l) as [[|]].  simpl. simpl in Hr. 
  destruct (Hr Hlb Hsafe Hsafehds Hvns) as [H1 H2]. apply H1.
  move=>/imset2P [y z Hyin Hzin ->] br.
  destruct (Hr Hlb Hsafe Hsafehds Hvns) as [H1 H2]. 
  move=>/setUP [Hbry|Hbrz]. 
  apply (H1 _ Hyin _ Hbry).
  assert (Hrb : ([forall x in seq_to_enotin (occsInProgram pb vb) ctb, t_at (val x) == Some (Var vb)] ->
  prog_safe pb -> prog_safe_hds pb -> vars_not_shared pb -> all_prop all_brpred (map val l))).
  move=>H H11 H22 H33. by destruct (Hr H Hsafe Hsafehds Hvns).
  apply (Hl Hlb Hrb Hsafe Hsafehds Hvns _ Hzin _ Hbrz). 
- move=>pb vb ctb tocc l typs dt ato rind bind aind Hott Hall Htocceq Hatat Hpting Hprev Hvareq Hsafe Hsafehds Hvns.
  split.
  move=>x. unfold dt_get_dcb. unfold DtInsert. 
  unfold tInsert. simpl.
  dependent destruction Hpting.
  move=>/imsetP [[y Hyinb] Hyin ->] br /imsetP [[z Hzinb] Hzin ->]. 
  simpl. simpl in Hzinb. 
  clear Hzin. 
  rewrite (set1P Hyinb) in Hzinb. rewrite (set1P Hzinb). auto.
  have Hppt := (ppt_v H0). clear H0. move:Hppt. 
  move:x Hvareq Hprev. 
  induction typs0 as [|[[|htyps0]] tltyps0 Ht0];move=>x Hvareq Hprev. simpl.
  move=>Hb /imsetP [[ct Hctin]]. exfalso. by rewrite -unfold_in in_set0 in Hctin.
  by rewrite in_set0.  
  simpl. unfold dt. move:Hprev. simpl. 
  destruct (fold_type_alg DtDisj tltyps0) as [[|]];move=>/= Hprev Hppt. 
  by rewrite in_set0. 
  move=>/imsetP [[y Hy] Hyin ->] br /imsetP [[z Hz] Hzin Hzeq]. simpl in Hzeq. rewrite Hzeq.
  clear Hzin. clear Hyin. simpl in *. destruct z as [[|hz tlz]]. auto.
  apply/andP;split.
  apply/forallP=>vt. apply/implyP=>/eqP Htat.
  apply/forallP=>v'. apply/implyP=>Htatb. 
  apply/forallP=>cl. apply/implyP=>Hnthcl.
  assert (Hhd : (useq_hd {| useq := hz :: tlz; buniq := buniq |} == Some hz)). auto.
  destruct tocc. inversion Htocceq. 
  apply (implyP (forallP (implyP (forallP (implyP (forallP (implyP 
        (forallP (implyP (forallP (Hppt Hsafe Hsafehds Hvns (subxx _)) _) Hy) _) Hz) _) Hhd) _) Htatb) _) Hnthcl).
  simpl. assert (Hprevb : all_brpred {| dt := Tr (p:=p0) d; Hdd := Hdd0 |}). 
  move=>brb Hbrb. 
  assert (Hbrbb : brb
         \in dt_get_dcb
               (DtDisj {| dt := Tr (p:=p0) htyps0; Hdd := Hdd |} {| dt := Tr (p:=p0) d; Hdd := Hdd0 |})).
  apply/setUP. right.  apply Hbrb. 
  apply (Hprev Hsafe Hsafehds Hvns brb Hbrbb).

  apply (Hprev Hsafe Hsafehds Hvns y Hy _ Hz). 

  apply Hall. apply/forallP=>x. apply/implyP=>Hx. apply (implyP (forallP Hvareq _)).
  apply/setUP;right;apply Hx. auto. auto. auto.   
- intros. by move=>x /set1P -> br /set1P ->.
- move=>pb ctb pred j vb l Hptyp Hppt Hall Hsafe Hsafehds Hvns. 
  move=>x /=.
  unfold dt_get_dcb. clear Hptyp. clear Hppt. 
  assert (Hallb : all_prop all_brpred (map val l)). apply Hall;auto.  
  move:Hallb.
  induction l as [|[[|h]] l Hl]. by rewrite in_set0.
  by rewrite in_set0. 
  simpl. destruct (fold_type_alg DtDisj l) as [[|]];
  move=>[H1 H2] /=. by rewrite in_set0.
  move=>/setUP [Hinh|Hind]. 
  apply (H1 _ Hinh). simpl in Hl. 
  assert (H3 : (prog_safe pb -> prog_safe_hds pb -> vars_not_shared pb -> all_prop all_brpred (map val l))). 
  auto.
  apply (Hl H3 H2 Hind).
- move=>pb ctb ip new_cl j vt typs ntyp vb Hppt Hall Hnth Hvtb Hallb Hsafe Hsafehds Hvns.
  split.
  apply Hallb; auto. 
  apply Hall;auto.  
Qed.

End br_pred.


End dep_completeness.