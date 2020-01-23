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
Require Import dTypes.
Require Import ddTypes.
Require Import rules.

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset bigop finfun. 

Require Import bigop_aux.
Require Import utils.
Require Import finseqs.

Set Implicit Arguments.
Unset Strict Implicit.

Section Transformation.

(** * Definition of dependent substitutions of clauses for a typing *)
(** [p] a program and [i] an interpretation *)
Variable p : program.
Variable i : interp.
Variable def : syntax.constant.

(** assuming a typing to study *)
Variable var_typing : forall v, var_type p v.
(** A ground atom *)
Variable dga : gatom.

(** [typed_var] is the set of variables for which the type is not top *)
Definition typed_vars := [set v | [exists t, (var_typ (var_typing v)) == Tr t]].

(** [tvars cl] gives back the variables of the clause having a non top type *)
Definition tvars (cl : clause) :=
  typed_vars :&: tail_vars (body_cl cl).

(** returns the seq of the \/-set(s) of branches for each type 
   with the associated variable                               *)
Definition seq_of_conj_trees cl :=
  [seq [set (v,x) | x in (dt_get_dcb (var_typ (var_typing v)))]
      | v <- (enum (tvars cl))].

(** [stv cl] is the number of typed variables of [cl] *)
Definition stv cl := #|tvars cl|.

(** technical lemma on size of [seq_of_conj_trees] *)
Lemma seq_of_conj_trees_size cl : size (seq_of_conj_trees cl) = stv cl.
Proof.
by rewrite size_image.
Qed.

(** same as seq_of_conj_trees as a tuple *)
Definition tup_of_conj_trees cl :=
  tcast (seq_of_conj_trees_size cl) (in_tuple (seq_of_conj_trees cl)).

(** returns the cartesian product (ie. all combinations) of 
   /\ trees of the different (non-trivial) types           *)
(** { < (v1,c_v1), (v2,c_v2), ..., (vn,c_vn) > }*)
(** i.e., \/ was unfolded *)
Definition conj_branches_comb cl := 
  setXn (tup_of_conj_trees cl).

(** Two branche coincide if they have the same size and the atom they
  refer to are the same (but may be not the terms) *)
Definition dep (b1 b2 : dbranch p) := 
   (size b1 == size b2) 
&& all (fun x => pred_occ x.1 == pred_occ x.2) (zip b1 b2).

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
Definition vdep (x1 x2 : ('I_n * dbranch p)%type) : bool.
destruct x1 as [v1 b1];destruct x2 as [v2 b2]; apply (dep b1 b2).
Defined.

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

(** [dep_subs_cl cl] computes the set of substitution that one can apply
  on [cl] while respecting the dependencies between variables of [cl].
   [par] is a group of variables with identic branches up to atoms.
   Each corespond to a clause that must be added.
    There must be an atom in the interpretation that makes the match for
    [s] and the different variables in [par]. The [par] are built by
    considering the types of [cl] *)
Definition dep_subs_cl (cl : clause) : {set sub} := 
  (* simulating disjunction *) 
  \bigcup_(vtyps in conj_branches_comb cl) 
    [set s : sub | 
      [forall par in 
        (* building the partition of all branches wrt. vdep (variable still stored) *)
        (equivalence_partition vdep (\bigcup_(vt <- vtyps) [set (vt.1,x) | x in (pred_of_set vt.2)])),
        (* each partition needs a "witness" element in i that matches s *)
        [exists ga in i, [forall vb in (pred_of_set par), ga_match_br ga vb.2 vb.1 s]]]].

(** [dep_subs] is the set of dependent substitutions for the program *)
Definition dep_subs := \bigcup_(cl in p) dep_subs_cl cl.

End Transformation.
