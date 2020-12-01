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

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset bigop finfun.

Require Import bigop_aux.
Require Import utils.
Require Import finseqs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Occurrences of atoms or terms *)
Section occurrences.

Section t_occ.

Variable p : program.

(** ** Atom occurrence *)
(** [occ] is a pair representing a position in
   a program. (occ x y) is the yth atom in the
   body of the xth clause of the program *)
Definition occ := ('I_(size p) * 'I_bn)%type.

(** ** Term occurrence *)
(** a term occurrence is a triple made of a clause
 position in the program, atom position in the body of the clause and term position in the atom *)
Record t_occ := T_occ {r_ind : 'I_(size p) ; b_ind : 'I_bn ; t_ind : 'I_max_ar}.

(** Type for the representation of [t_occ]*)
Definition tocc_countprod := prod_countType (prod_countType (ordinal_countType (size p)) (ordinal_countType bn)) (ordinal_countType max_ar).

(** Representation and cancellation lemma for [t_occ] *)
Definition t_occ_rep (a : t_occ) : tocc_countprod :=
  let: T_occ b c d := a in (b,c,d).
Definition t_occ_pre (a : tocc_countprod) :=
  let: (b,c,d) := a in T_occ b c d.

Lemma prod_of_t_occK : cancel t_occ_rep t_occ_pre.
Proof.
by case.
Qed.

(** [t_occ] is a finite type *)
Definition t_occ_eqMixin :=
  CanEqMixin prod_of_t_occK.
Canonical t_occ_eqType :=
  Eval hnf in EqType t_occ t_occ_eqMixin.
Definition t_occ_choiceMixin :=
  CanChoiceMixin prod_of_t_occK.
Canonical t_occ_choiceType :=
  Eval hnf in ChoiceType t_occ t_occ_choiceMixin.
Definition t_occ_countMixin :=
  (@CanCountMixin tocc_countprod _ t_occ_rep t_occ_pre prod_of_t_occK).
Canonical t_occ_countType :=
  Eval hnf in CountType t_occ t_occ_countMixin.
Definition t_occ_finMixin :=
  CanFinMixin prod_of_t_occK.
Canonical t_occ_finType :=
  Eval hnf in FinType t_occ t_occ_finMixin.

(** Accessing the atom matching a given t_occ *)
Definition at_at (o : t_occ) : option atom :=
  match nth_error p (r_ind o) with
    | None => None
    | Some cl => nth_error (body_cl cl) (b_ind o) end.

(** Accessing the term matching a given t_occ *)
Definition t_at (o : t_occ) : option term.
destruct (at_at o).
- destruct o as [x y z].
  apply (nth_error (arg_atom a) z).
- apply None.
Defined.

(** Accessing the predicate matching a given t_occ *)
Definition p_at (t : t_occ) := match (at_at t) with
  | None => None
  | Some ato => Some (sym_atom ato) end.

(** If [t_at] returns a variable, it an actual var of a clause. *)
Lemma t_at_vars_in (tocc : t_occ) v cl :
    t_at tocc = Some (Var v)
  -> Some cl = nth_error p (r_ind tocc)
  -> v \in tail_vars (body_cl cl).
Proof.
unfold tail_vars.
move => Htat Heq. apply/bigcup_seqP.
unfold t_at in Htat.
unfold at_at in Htat. rewrite -Heq in Htat.
assert (Haex : exists a, nth_error (body_cl cl) (b_ind tocc) = Some a).
destruct (nth_error (body_cl cl) (b_ind tocc)) as [a|] ; [|inversion Htat].
by exists a.
destruct Haex as [a Ha].
rewrite Ha in Htat.
exists a.
apply (nth_error_in Ha).
apply/andP ; split ; [|trivial].
apply/bigcup_seqP ; exists (Var v) ; [|apply/andP ; split ; by [|apply/set1P|]].
destruct tocc. apply (nth_error_in Htat).
Qed.

End t_occ.

Section a_occ.

Variable p : program.

(** ** Atom occurrence *)
(** an atom occurrence is a couple made of a clause
 position in the program and atom position in the body of the clause *)
Record a_occ := A_occ {ar_ind : 'I_(size p) ; ab_ind : 'I_bn}.

(** Extract the atom occurence from the term occurence*)
Definition atom_occ (t : t_occ p) := A_occ (r_ind t) (b_ind t).

(** Type for the representation of [t_occ]*)
Definition aocc_countprod := prod_countType (ordinal_countType (size p)) (ordinal_countType bn).

(** Representation and cancellation lemma for [t_occ] *)
Definition a_occ_rep (a : a_occ) : aocc_countprod :=
  let: A_occ b c := a in (b,c).
Definition a_occ_pre (a : aocc_countprod) :=
  let: (b,c) := a in A_occ b c.

Lemma prod_of_a_occK : cancel a_occ_rep a_occ_pre.
Proof.
by case.
Qed.

(** [a_occ] is a finite type *)
Definition a_occ_eqMixin :=
  CanEqMixin prod_of_a_occK.
Canonical a_occ_eqType :=
  Eval hnf in EqType a_occ a_occ_eqMixin.
Definition a_occ_choiceMixin :=
  CanChoiceMixin prod_of_a_occK.
Canonical a_occ_choiceType :=
  Eval hnf in ChoiceType a_occ a_occ_choiceMixin.
Definition a_occ_countMixin :=
  (@CanCountMixin aocc_countprod _ a_occ_rep a_occ_pre prod_of_a_occK).
Canonical a_occ_countType :=
  Eval hnf in CountType a_occ a_occ_countMixin.
Definition a_occ_finMixin :=
  CanFinMixin prod_of_a_occK.
Canonical a_occ_finType :=
  Eval hnf in FinType a_occ a_occ_finMixin.

End a_occ.

Section prog_occ.

(** ** Collecting occurrences of a variable *)
(** Set of term occurrences for p *)
Definition tocs p := {set (t_occ p)}.

(** ** Computing of occurrences of variables in terms, atoms, clauses *)
(** Given a list of pair with a bounded number as first element gives back the list with the
   numbers incremented *)
Definition shift1 {k : nat} {A : finType} (l : {set ('I_k * A)%type}) : {set ('I_k.+1 * A)%type} :=
  [set ((ord_shift x.1), x.2) | x in l].

(** For a given list of terms [l] gives back the set of indices of terms of l that are a variable *)
Definition occsInTermList (v : 'I_n) (l : seq term) : {set 'I_max_ar} :=
  [set i : 'I_max_ar | nth_error l i == Some (Var v)].

(** Gives back the indexes of the variables in an atom *)
Definition occsInAtom (a : atom) (v : 'I_n) : {set 'I_max_ar} :=
  (@occsInTermList v (arg_atom a)).

(** Accessing the term in atom [a] at an index from [occsInAtom a] will indeed give back a
  variable *)
Lemma occsInAtomV occ a v : occ \in occsInAtom a v -> nth_error (arg_atom a) occ = Some (Var v).
Proof.
rewrite in_set.
by move=>/eqP. 
Qed.

(** Given a list of atoms, computes the positions of the variables in that list *)
Fixpoint occsInAtomList (al : seq atom) (v : 'I_n) : {set ('I_(size al) * 'I_max_ar)} :=
  match al with
  | [::] => set0
  | a::al => ([set (Ordinal (ltn0Sn _), x) | x in (occsInAtom a v)] :|: (shift1 (@occsInAtomList al v))) end.

(** [occsInAtomList] computes correct positions coresponding 
  to atoms and to variables in those atoms *)
Lemma occsInAtomListVint (tl : seq atom) v aton termn :
               ((aton, termn) \in occsInAtomList tl v)
            -> (exists ato, nth_error tl aton = Some ato /\ nth_error (arg_atom ato) termn = Some (Var v)).
Proof.
move:aton termn.
induction tl.
- by move => aton termn; rewrite in_set0.
- move => aton termn /setUP [/imsetP [occ Hocc Heq]|Hrec].
  + exists a.
    inversion Heq. split.
    - auto.
    - by apply occsInAtomV.
  + destruct (imsetP Hrec) as [[atonm1 termnm1] Hinrec Heqrec].
    inversion Heqrec.
    apply/IHtl/Hinrec.
Qed.

(** [occsInAtomList] can be augmented with the clause index to get
  a tocc that references to a variable term in the program *)
Lemma occsInAtomListV {p} (cl : clause) (cln : 'I_(size p)) v aton termn : Some cl = nth_error p cln
            -> ((aton, termn) \in occsInAtomList (body_cl cl) v)
            -> @t_at p {| r_ind := cln; b_ind := widen_ord
                (wlist_to_seq_size (body_cl cl)) aton;
                      t_ind := termn |} = Some (Var v).
Proof.
destruct cl as [h tl].
move:tl aton.
apply (@wlist_ind atom_finType bn (fun tl => forall (aton : ordinal_finType (size (body_cl (Clause h tl))))
(Hcleq : Some (Clause h tl) = nth_error p cln)
(Hin : (aton, termn) \in occsInAtomList (body_cl (Clause h tl)) v),
t_at {| r_ind := cln; b_ind := widen_ord (wlist_to_seq_size (body_cl (Clause h tl))) aton;
  t_ind := termn |} = Some (Var v))).
repeat (unfold wlist_to_seq_co).
move => s Ps aton Hcleq Hin.
destruct (occsInAtomListVint Hin) as [ato [Hato Hterm]].
unfold t_at. unfold at_at.
by rewrite -Hcleq Hato.
Qed.

(** [occsInRule] is ocssInAtomList where the first element of the pairs
is widened to be 'I_bn *)
Definition occsInRule (v : 'I_n) (cl : clause) : {set ('I_bn * 'I_max_ar)} :=
  [set ((widen_ord (wlist_to_seq_size (body_cl cl)) (fst x)), (snd x)) | x in (occsInAtomList (body_cl cl) v)].

(** [ocssInRule] designates also valid variable indexes *)
Lemma occsInRuleV {p} cl v aton termn : ((aton, termn) \in occsInRule v (tnth (in_tuple p) cl))
                             -> t_at {| r_ind := cl; b_ind := aton; t_ind := termn |} = Some (Var v).
Proof.
move => /imsetP [[atonbis termnbis] Hin Heq]. inversion Heq as [[Hatoneq Htermneq]].
apply occsInAtomListV. simpl in *. by rewrite tnth_nth_error. apply Hin.
Qed.

(** A function to compute t_occs from a clause index and a list of pairs
  of bounded indexes. *)
Definition attach_cl_nb p (cl_nb : 'I_(size p)) (occs : {set ('I_bn * 'I_max_ar)}) : tocs p :=
  [set @T_occ p cl_nb (fst x) (snd x) | x in occs].
(** Computes all the variables t_occurence of a program *)
Definition occsInProgram p (v : 'I_n) : tocs p :=
  \bigcup_(cln in 'I_(size p)) attach_cl_nb cln (@occsInRule v (tnth (in_tuple p) cln)).

(** There is a variable indexed by each element of [occsInProgram p] *)
Lemma occsInProgramV {p} v (xocc : t_occ p) : xocc \in occsInProgram p v -> t_at (xocc) = Some (Var v).
Proof.
move => /bigcupP [cl Hclp /imsetP [[aton termn] HoccsInR Hocceq]].
rewrite Hocceq. by apply occsInRuleV.
Qed.

(** All vars of an atom arguments are in [atom_vars] *)
Lemma arg_atom_vars_in (v : 'I_n) (ato : atom) : (Var v \in arg_atom ato) <-> v \in atom_vars ato.
Proof.
destruct ato as [[ha tla] Ha].
simpl. unfold atom_vars. simpl. unfold raw_atom_vars. clear Ha.
induction tla.
- split ; [|rewrite big_nil in_set0] ; move => //.
- split ; [|rewrite big_cons] ; rewrite in_cons ; [move=>/orP ; rewrite big_cons |move=>/setUP] ; move => [Hnew | Hold].
  + apply/setUP. left. rewrite <- (eqP Hnew). by apply/set1P.
  + apply/setUP. right. apply/IHtla/Hold.
  + apply/orP. left. destruct a as [vv | cv].
    - by rewrite (set1P Hnew).
    - by rewrite in_set0 in Hnew.
  + apply/orP. right. apply/IHtla/Hold.
Qed.

End prog_occ.

(** default values *)
Variable dt : term.
Variable dv : 'I_n.
Variable df : symtype.

Definition term_to_var (t : term) :=
  match t with
    | Val c => dv
    | Var v => v end.

(** Returns (as a variable) the [j]th term in the head of [cl] *)
Definition get_cl_var (cl : clause) (j : nat) : 'I_n :=
  term_to_var (nth dt (arg_atom (head_cl cl)) j).

Lemma get_cl_var_leq (cl : clause) (j : nat) :
   only_variables_head cl
-> j < size (arg_atom (head_cl cl))
-> Var (get_cl_var cl j) \in arg_atom (head_cl cl).
Proof.
destruct cl as [[[f args] Hhcl] tlcl]. simpl. unfold get_cl_var. unfold hsym_cl.
unfold arg_atom. unfold only_variables_head. unfold only_variables_atom. unfold arg_atom.
simpl. clear Hhcl. clear tlcl.
move:j. induction args as [|hargs args];move=>[|j]//.
- move=>/= /andP [Hv1 _] _. destruct hargs as [x|x].
  simpl. apply/mem_head.
  inversion Hv1.
- move=>/andP [Hv1 Hv2] Hj. apply/mem_body.
  apply/IHargs;auto.
Qed.

End occurrences.