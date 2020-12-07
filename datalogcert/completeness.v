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

(** Eigth and last part of the original file "pengine.v" with modifications *)

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset bigop finfun. 

Require Import syntax.
Require Import subs.
Require Import pmatch.
Require Import bSemantics.
Require Import monotonicity.
Require Import soundness.
Require Import fixpoint.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Completeness.

(** * Completeness *)
Variable n   : nat.
(** default constant *)
Variable def : syntax.constant.
(** program *)
Variable p   : program.
(** [p] is safe *)
Hypothesis p_safe : prog_safe p.
(** the set of ground atoms *)
Definition bp : {set gatom} := setT.

(** Proof that B(P) is a model of the safe program [p]. *)
Lemma bpM : prog_true p bp.
Proof. by move=> gr; apply/allP=> cl cl_in; apply/implyP; rewrite inE. Qed.

(** There is a set of ground atoms, shuch that it is an iteration
 of [fwd_chain] from the empty set, it is a model of [p] and it is
 the smallest one *)
Lemma fwd_chain_complete :
{ m : {set gatom} &
{ n : nat | [/\ prog_true p m
              , m = iter n (fwd_chain def p) set0
              & forall m', prog_true p m' -> m \subset m']}}.
Proof.
have h_inc : increasing (fwd_chain def p).
  by move=> i; apply: fwd_chain_inc.
have h_incr := fwd_chain_incr p def.
have h_fp  := fwd_chain_stable def bpM.
have h_ub  :  ubound bp (fwd_chain def p).
  by move=> ss H; rewrite subsetT.
have h_lb  : set0 \subset bp by rewrite /bp.
have [m [m_fix [m_def m_min]]] := has_lfp h_lb h_incr h_inc h_ub.
exists m, #|bp|; do ! split; auto.
  exact/(fwd_chain_sound p_safe)/esym/m_fix.
by move=> m' /(fwd_chain_stable def)/esym/m_min; apply; rewrite sub0set.
Qed.

(** ** Forward Chain Completeness: 
Let [p] be a safe program. The iterative forward chain
inference engine terminates (after iterating as many times as there are elements in B(P)) 
and outputs a minimal model for [p]. *)
Lemma incr_fwd_chain_complete (s0 : {set gatom}) :
{ m : {set gatom} &
{ n : nat | [/\ prog_true p m
              , n = #|bp|
              , m = iter n (fwd_chain def p) s0
              & forall (m' : {set gatom}), s0 \subset m' -> prog_true p m' -> m \subset m']}}.
Proof.
have h_inc : increasing (fwd_chain def p).
  by move=> i; apply: fwd_chain_inc.
have h_incr := fwd_chain_incr p def.
have h_fp  := fwd_chain_stable def bpM.
have h_ub  :  ubound bp (fwd_chain def p).
  by move=> ss H; rewrite subsetT.
have h_lb  : s0 \subset bp by rewrite /bp.
have [m [m_fix [m_def m_min]]] := has_lfp h_lb h_incr h_inc h_ub.
exists m, #|bp|; do ! split; auto.
  exact/(fwd_chain_sound p_safe)/esym/m_fix.
by move=> m' hs /(fwd_chain_stable def)/esym/m_min; apply.
Qed.

End Completeness.

