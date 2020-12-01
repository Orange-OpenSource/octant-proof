(************************************************************************************)
(**                                                                                 *)
(**                             The DatalogCert Library                             *)
(**                                                                                 *)
(**             CNRS & Université Paris-Sud, Université Paris-Saclay                *)
(**                                                                                 *)
(**                        Copyright 2016-2019 : FormalData                         *)
(**                                                                                 *)
(**         Original authors: Véronique Benzaken                                    *)
(**                           Évelyne Contejean                                     *)
(**                           Stefania Dumbrava                                     *)
(**                                                                                 *)
(************************************************************************************)

(** Fifth part of the original file "pengine.v" with modifications
    (including some names that were changed). *)

Require Import utils.
Require Import syntax.
Require Import subs.
Require Import pmatch.
Require Import bSemantics.

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype.
From mathcomp
Require Import tuple finset bigop finfun.

Require Import bigop_aux.
Require Import finseqs.

Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (s : sub) (t : term) (a : atom) (v : 'I_n)
         (b : 'I_n * syntax.constant) (i : interp) (cl : clause).

(** * Increasing functions *)
Section Increasing.

(** [bindS] increasing for its two arguments *)
Lemma bindS_incr {A B : finType} (i1 i2 : {set A}) (f1 f2 : A -> {set B}) :
  i1 \subset i2 -> (forall x, f1 x \subset f2 x) ->
  bindS i1 f1 \subset bindS i2 f2.
Proof.
move=> H1 H2; apply/subsetP => r; case/bindP=> u ui1 ri1.
apply/bindP; exists u; move/subsetP: H1. by apply.
by move/subsetP: (H2 u) => H _; apply: H.
Qed.

(** [foldS] increasing (same l) *)
Lemma foldS_incr {A : eqType} {B : finType} (f1 f2 : A -> B -> {set B}) (l : seq A)
  (f_incr : forall x y, f1 x y \subset f2 x y) :
  (forall (s1 s2 : {set B}), (s1 \subset s2) -> foldS f1 s1 l \subset foldS f2 s2 l).
Proof. by elim: l => //= x l ihl s1 s2 hs12; apply/bindS_incr=> // y; exact/ihl. Qed.

(** [match_atom_all] increasing for the interpretation *)
Lemma match_atom_all_incr i1 i2 s a :
 i1 \subset i2 -> match_atom_all i1 a s \subset match_atom_all i2 a s.
Proof. move=> s12; apply preimsetS. by apply/imsetS. Qed.

(** [match_body] increasing for interpretation argument *)
Lemma match_body_incr i1 i2 cl :
  i1 \subset i2 -> match_body i1 (body_cl cl) \subset match_body i2 (body_cl cl).
Proof.
by move=> H; apply/foldS_incr => //; move=> u s'; apply: match_atom_all_incr.
Qed.

(** [cons_clause] increasing for interpretation argument *)
Lemma cons_cl_incr (i1 i2 : interp) cl def :
  i1 \subset i2 -> cons_clause def cl i1 \subset cons_clause def cl i2.
Proof. by move=> Hs; rewrite //; apply/imsetS/match_body_incr. Qed.

(** [fwd chain] increasing for interpretation argument *)
Lemma fwd_chain_incr i1 i2 p def :
  i1 \subset i2 ->
  fwd_chain def p i1 \subset fwd_chain def p i2.
Proof.
move=> Hs; apply/setUSS/subsetP; move=> // ga /bigcup_seqP[cl cl_in /andP[ga_in _]].
apply/bigcup_seqP; exists cl => //; apply/andP; split; auto.
by move/subsetP: (cons_cl_incr cl def Hs); apply.
Qed.

(** [fwd chain] increasing for program argument *)
Lemma fwd_chain_pincr i p1 p2 def :
  p1 \subset p2 ->
  fwd_chain def p1 i \subset fwd_chain def p2 i.
Proof.
move=> Hs; apply/setUSS/subsetP;auto.
move=>x /bigcup_seqP [cl cl_in H].
apply/bigcup_seqP. exists cl.
apply (subsetP Hs cl cl_in). apply H.
Qed.

(** [sem] is increasing wrt. for each iteration *)
Lemma sem_m_incr (p : program) (def : syntax.constant) (m : nat) (i : interp) :
  sem p def m i \subset sem p def m.+1 i.
Proof.
induction m as [|m Hm];apply/subsetP=>x.
move=>/= Hxin. apply/setUP. by left.
move=>Hxin. apply/setUP. by left.
Qed.

Section Overlinear.

(**[fwd_chain i] greater than [i] *)
Lemma fwd_chain_inc i p def : i \subset fwd_chain def p i.
Proof. exact: subsetUl. Qed.

(**[sem i] greater than [i] *)
Lemma sem_inc i m p def : i \subset sem def p m i.
Proof. 
induction m as [|m Hrec].
auto.
apply/subset_trans. apply Hrec. apply sem_m_incr.
Qed.

End Overlinear.

(** The iteration of [fwd_chain pp] on [i] contains [i]*)
Lemma iter_fwd_chain_subset def p (i : interp) k :
  i \subset iter k (fwd_chain def p) i.
Proof.
elim: k => //= k ihk; rewrite (subset_trans (fwd_chain_inc i p def)) //.
exact: fwd_chain_incr.
Qed.

(** [sem] is increasing wrt. number of iterations *)
Lemma sem_m_star_incr (p : program) (def : syntax.constant) (m m' : nat) (i : interp) :
  m < m' -> sem p def m i \subset sem p def m' i.
Proof.
move:m'. induction m as [|m Hrec];
move=>[|m'] //= H.
apply/subset_trans. apply sem_inc.
apply (@iter_fwd_chain_subset def p (sem p def m' i) 1).
apply/fwd_chain_incr/Hrec/H.
Qed.

End Increasing.
