(************************************************************************************)
(**                                                                                 *)
(**                             The DatalogCert Library                             *)
(**                                                                                 *)
(**             CNRS & Université Paris-Sud, Université Paris-Saclay                *)
(**                                                                                 *)
(**                        Copyright 2016-2019 : FormalData                         *)
(**                                                                                 *)
(**         Authors: Véronique Benzaken                                             *)
(**                  Évelyne Contejean                                              *)
(**                  Stefania Dumbrava                                              *)
(**                                                                                 *)
(************************************************************************************)

(** This is the seventh part of the original file "pengine.v" with modifications
    by Pierre-Léo Bégay. *)

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset bigop finfun. 


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(** * Fixed Points *)
(** Once a fixed point is reached. Any iteration gives the fixed point *)
Lemma fix_iter T (f : T -> T) n s (s_fix : s = f s) : s = iter n f s.
Proof. by elim: n => //= n {1}<-. Qed.

(** If after n iteration, fixpoint is reached so is after m for m > n *)
Lemma iter_leq_fix T (f : T -> T) x n m (i_eq: iter n f x = iter n.+1 f x) :
  n <= m -> iter m f x = iter m.+1 f x.
Proof. by move=>/subnK<-; elim: {m}(m-n) => //= m {2}<-. Qed.

(** note: minsetP lemma subsumes all this *)
Section iter_mon.

Variables (T : finType).
Implicit Types (s : {set T}) (f : {set T} -> {set T}).

(** Increasing function *)
Definition monotone   f := forall s1 s2, s1 \subset s2 -> f s1 \subset f s2.

(** Inflating function *)
Definition increasing f := forall s, s \subset f s.
(** Let f be an increasing function on sets ot [T] *)
Variables (f : {set T} -> {set T}) (f_mon : monotone f).

(** If [f] increasing so is [f^n] *)
Lemma iter_mon n : monotone (iter n f).
Proof. by elim: n => // n ihn s1 s2 /= s_in; exact/f_mon/ihn. Qed.

(** Let [lb] such that if [s] contains [lb], so does [f s] *)
Variable (lb : {set T}) (f_lb : forall s, lb \subset s -> lb \subset f s).

(** [iterf n] is |f^n(lb)]*)
Definition iterf n := iter n f lb.

(** [iterf] is increasing *)
Lemma subset_iterf m n : m <= n -> iterf m \subset iterf n.
Proof.
move/subnK<-; rewrite /iterf addnC iter_add; apply/iter_mon.
by elim: {n m} (n-m); [rewrite ?fsubset_refl | move=> n ihn; apply/f_lb].
Qed.

End iter_mon.

Section Fixpoints.

(** ub and s0 sets of T where T is a finite type  with s0 subset of ub *)
Variables (T : finType) (s0 ub : {set T}).

Hypothesis (s0_bound : s0 \subset ub).

Implicit Types (s : {set T}) (f : {set T} -> {set T}).

Variables (f : {set T} -> {set T}).

(** [ubound] means if [ub] contains [s], it also contains [f s] *)
Definition ubound := forall s, s  \subset ub -> f s \subset ub.

(** we assume that [f] is monotone increasing and verifies [ubound] *)
Hypothesis (f_mono : monotone f) (f_inc : increasing f) (f_ubound: ubound).

Notation iterf_incr n := (iterf f s0 n).
Notation lfp_incr     := (iterf f s0 #|ub|).

(** [f^(s0)] is included in [ub] *)
Lemma iterf_incr_bound n : (iterf_incr n) \subset ub.
Proof. by elim: n => /= [|n ihn]; rewrite ?lb_bound ?f_ubound //=. Qed.

(** [lfp_incr], the N iterate of [f] where N is the cardinal of [ub]
  is a fixpoint for [f]

Adapted from the lfpE lemma in http://www.ps.uni-saarland.de/extras/jaritp14/
   (C) Christian Doczkal and Gert Smolka *)
Lemma lfpE : lfp_incr = f lfp_incr.
Proof.
suff/exists_eqP: [exists k : 'I_#|ub|.+1 , iterf_incr k == iterf_incr k.+1].
   case=> k E; exact/(iter_leq_fix E)/leq_ord.
apply/contraT; rewrite negb_exists => /forallP /= H.
have/(_ #|ub|.+1 (leqnn _)): forall k , k <= #|ub|.+1 -> k <= #|iterf_incr k|.
  elim=> // n IHn Hn.
  rewrite (leq_ltn_trans (IHn (ltnW Hn))) ?proper_card //.
  rewrite properEneq subset_iterf // ?andbT.
  exact: H (Ordinal Hn).
  move=> s hs; have := f_mono hs; have := f_inc s0.
  apply: subset_trans.
rewrite leqNgt ltnS subset_leq_card ?f_ubound //.
exact/iterf_incr_bound.
Qed.

(** [lfp_incr] is smaller than any fixpoint that would be greater than
   [s0] the starting point of the iterations *)
Lemma min_lfp_all s (hs : s0 \subset s) (sfp : s = f s) : lfp_incr \subset s.
Proof. by rewrite (fix_iter #|ub| sfp); apply/iter_mon. Qed.

(** Rephrase the existence of the LFP and its properties *)
Lemma has_lfp :
  { lfp : {set T} | lfp = f lfp
                  /\ lfp = iter #|ub| f s0
                  /\ forall s', s0 \subset s' -> s' = f s' -> lfp \subset s'}.
Proof.
by exists lfp_incr; rewrite -lfpE /lfp_incr; repeat split; apply/min_lfp_all.
Qed.

End Fixpoints.
