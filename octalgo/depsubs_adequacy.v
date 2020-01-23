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
Require Import pmatch.
Require Import subs.
Require Import bSemantics.
Require Import ddTypes.
Require Import rules.
Require Import ctransfo.
Require Import depsubs.
Require Import depsubs_completeness.
Require Import soundness.
Require Import depsubs_filter.

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset bigop finfun. 

Set Implicit Arguments.
Unset Strict Implicit.

Section ctyp_adequacy.

Variable p : program.
Variable i : interp.
(** Defaults *)
Variable def : syntax.constant.
Variable dv  : 'I_n.

(** * Main adequacy theorem *)
(** Safety constraints on [p] and [i} *)
Hypothesis psafe : prog_safe p.
Hypothesis phsafe : prog_safe_hds p.
Hypothesis pvars : vars_not_shared p.
Hypothesis ext_edb : safe_edb i.

(** set of variables to replace *)
Variable Rv : {set 'I_n}.

(** assuming a typing to study *)
Variable typing : forall v, var_type p v.

(** The actually typed variables are exactly Rv *)
Hypothesis ad_typed: typed_vars typing = Rv.

Variable dga : gatom.

(** [subs] is defined as the restriction of [dep_subs i typing] to [Rv] *)
Definition subs := [set sub_filter s Rv | s in (dep_subs i typing)].

(** The transformation of [p] by the substitutions from [subs] preserves the
  semantic of the original program *)
Theorem c_typ_trans_adequacy (m : nat)
  : (sem (tprog p Rv subs) def m i) = (sem p def m i).
Proof.
rewrite cadequacy.
reflexivity.
apply/forallP=>cl. apply/implyP=>Hcl.
apply/forallP=>s.  apply/implyP=>Hsmatch.
unfold subs. apply/imsetP. exists s.
destruct (bmatch_match_body Hsmatch)
  as [r Hr1 Hr2].
apply (dep_subs_mon Hr2). 
apply (subs_comp dv psafe phsafe pvars ext_edb typing dga Hcl Hr1).
reflexivity.
Qed. 

End ctyp_adequacy.
