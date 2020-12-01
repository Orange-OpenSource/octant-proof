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
Require Import subs.
Require Import pmatch.
Require Import bSemantics.
Require Import monotonicity.
Require Import soundness.

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset bigop finfun.

Require Import bigop_aux.
Require Import utils.
Require Import finseqs.

Require Import Coq.Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.

Section Purge.
(** * Purging a program *)
(** The underlying idea of this section is that if we have computed the semantic
  of our program and found all the values of the [i]th argument of
  atoms with symbol [f], now we can look at the clauses of our program and
  remove all the clauses that contains atom with symbol [f] where the [i]th
  argument is another constant because they do not play a role in our semantics
   *)
Variable p : program.
Variable i : interp.
Variable def : syntax.constant.

(** A symbol *)
Variable f : symtype.
(** The index of an argument of this symbol *)
Variable ind : 'I_(arity f).
(** A set of value *)
Variable vals : {set syntax.constant}.

(** The hypothesis states that [vals] contains all the values of the [ind]eth
   argument of [f] that appear in the computation of the
   semantics of [p] for interpretation [i] *)
Hypothesis vals_adeq : forall (c def : syntax.constant) (m : nat) (ga : gatom),
           ga \in (sem p def m i) -> sym_gatom ga = f
        -> nth_error (arg_gatom ga) ind = Some c
        -> c \in vals.

(** [keep_atom a] filters out the atom [a] that have symbol [f] and whose [ind]eth
  argument is a constant that is not in [vals] *)
Definition keep_atom (a : atom) : bool :=
  (* the atom must obviously be the currently studied predicate *)
  if (sym_atom a == f)
    then match nth_error (arg_atom a) ind with
            (* if the argument position holds a variable, nothing to do *)
          | Some (Var v) => true
            (* if it is a value, the rule is erased iff. it is not captured in vals *)
          | Some (Val c) => c \in vals
            (* this hopefuly won't happen *)
          | None => false end
    else true.

(** We keep a clause if all its atoms in the body and the head
   are keepable *)
Definition keep_rule (cl : clause) : bool :=
  match cl with Clause hd tl =>
    (keep_atom hd) && all keep_atom tl end.

(** We define pp as the restriction of p purged of non keepable clauses *)
Definition pp := filter keep_rule p.

Lemma pp_p : pp \subset p.
Proof.
apply/subsetP=>x.
rewrite mem_filter.
by move=>/andP [H1].
Qed.

(** If there is a substitution [s] such that [s a] is in the semantic of [p] for [i],
   then [a] can be kept. (ie it will not have as [ind] argument something that was
   not captured by [vals] *)
Lemma keep_atom_sem (m : nat) (s : sub) (a : atom) : gr_atom_def def s a \in sem p def m i -> keep_atom a.
Proof.
move=>Hxded.
unfold keep_atom.
destruct (bool_des_rew (sym_atom a == f)) as [Hpred|Hpred];rewrite Hpred;trivial.
destruct (nth_error_case (arg_atom a) ind) as [Hnone|[[v|c] [H1 H2]]].
rewrite Hnone. have H := (@oob_atom_args a). rewrite (eqP Hpred) in H.
by apply/ReflectF/(H ind Hnone).
by rewrite H2.
rewrite H2. apply (vals_adeq Hxded). apply/eqP/Hpred.
simpl.
assert (H : gr_term_def def s (Val c) = c). auto.
rewrite -H.
apply/(@nth_error_map _ _ (gr_term_def def s))/H2.
Qed.

(** if [tl] can be extended by [s] to be in the semantics of [p] for [i], then
   we can keep [tl].*)
Lemma keep_atom_tail_match (m : nat) (s : sub) (tl : seq atom) :
  s \in match_body (sem p def m i) tl -> all keep_atom tl.
Proof.
move=> /match_tl_sound [gtl Htaileq Htlded].
apply/allP. move=>a Hain.
apply (@keep_atom_sem m s a).
apply/(allP (tail_mem def Htaileq Htlded))/mapP.
exists a. apply Hain. by rewrite gr_atom_defE.
Qed.

(** The semantics of the purged program contains the semantics of [p] *)
Lemma purge_sem_completeness : forall m, sem p def m i \subset sem pp def m i.
Proof.
move=>m.
apply/subsetP.
induction m as [|m Hm];move=> x //.
move=>Hxded. have Hxdedb := Hxded. move:Hxded.
move=>/setUP [Hprev | Hnew];apply/setUP.
left. apply/Hm/Hprev.
right. move:Hnew.
move=>/bigcup_seqP [cl Hclinpp /andP [/imsetP [s Hsmatch Hxeq] Htriv]].
rewrite Hxeq. rewrite Hxeq in Hxdedb.
apply/bigcup_seqP. exists cl.
rewrite mem_filter. apply/andP;split.
 (* pour la tête : faire avec vals_adeq et Hxdedb *)
 (* pour le body, avec match_tl_sound ou assimilé *)
destruct cl as [hcl acl]. apply/andP;split.
apply/keep_atom_sem/Hxdedb.
apply/keep_atom_tail_match/Hsmatch.
apply Hclinpp.
apply/andP;split.
apply/imsetP.
exists s.
assert (Hdedsub : (sem p def m i) \subset (sem pp def m i)).
apply/subsetP/Hm.
apply ((subsetP (match_body_incr _ Hdedsub) s) Hsmatch).
reflexivity.
trivial.
Qed.

(** The semantics of the purged program is a subset of the semantics of p *)
Lemma purge_sem_soundness : forall m, sem pp def m i \subset sem p def m i.
Proof.
move=>m.
apply iter_fun_incr.
apply/forallP=>x;apply/forallP=>y;apply/implyP=>H.
apply/fwd_chain_incr/H.
apply/forallP=>x. 
apply/fwd_chain_pincr/pp_p.
Qed.

(** The semantics of the program and its purged version coincide *)
Lemma purge_sem_adequacy : forall m, sem pp def m i = sem p def m i.
Proof.
move=>m.
apply/eqP ; rewrite eqEsubset;apply/andP ;split ;
[apply purge_sem_soundness|apply purge_sem_completeness].
Qed.

End Purge.
