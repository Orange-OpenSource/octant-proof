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

(** This is the fourth part of the original file "pengine.v" with a new part added
    by Pierre-Léo Bégay *)

Require Import syntax.
Require Import subs.
Require Import pmatch.

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset bigop finfun.

Require Import bigop_aux.
Require Import finseqs.
Require Import utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Semantics of a Datalog program *)
Section bSemantics.

(** ** Consequences of a clause *)

(** one iteration of fwd_chain for a one-clause program *)
(** Given a clause [cl: h :- b] gives back [s h] for all [s] that match
 [b] in interpretation [i]. [def] is usually not used as [cl] should be safe and does not introduce variables in its head. *)
Definition cons_clause (def : syntax.constant) (cl : clause) i : {set gatom} :=
  [set gr_atom_def def s (head_cl cl) | s in match_body i (body_cl cl)].

(** If clause verifies safe_cl_hd then the symbols we get are all in IDB *)
Lemma cons_clause_idb (def : syntax.constant) (cl : clause) i :
  safe_cl_hd cl -> [forall x in cons_clause def cl i, predtype (sym_gatom x) == Idb].
Proof.
move => Hsafe ; apply/forallP ; move => x ; apply/implyP ; move => Hin.
unfold cons_clause in Hin. unfold safe_cl_hd in Hsafe.
destruct (imsetP Hin) as [s Hsmatch Hxeq].
by rewrite Hxeq.
Qed.

(** one iteration of fwd_chain for a program *)
Definition fwd_chain def p i : {set gatom} :=
  i :|: \bigcup_(cl <- p) cons_clause def cl i.

(** ** Semantic of a program up to m steps *)

(** [sem p d m i] iterates fwd_chain m times over i. Added to the original files *)
Definition sem (p : program) (def : syntax.constant) (m : nat) (i : interp) :=
  iter m (fwd_chain def p) i.

(** [sem] is increasing for subset *)
Lemma sem_m_incr (p : program) (def : syntax.constant) (m : nat) (i : interp) :
  sem p def m i \subset sem p def m.+1 i.
Proof.
induction m as [|m Hm];apply/subsetP=>x.
move=>/= Hxin. apply/setUP. by left.
move=>Hxin. apply/setUP. by left.
Qed.

(** If [p] has safe heads, 
   [sem] is safe (only defines elements in the IDB or it was in i_init *)
Lemma sem_idb_safe (p : program) (def : syntax.constant) (m : nat) i_init :
  prog_safe_hds p ->
  [forall x in (sem p def m i_init) :\: i_init, predtype (sym_gatom x) == Idb].
Proof.
move:i_init. induction m as [|m Hm]; move=>i_init Hsafe;
apply/forallP ; move => x ; apply/implyP ; move => Hin.
- by rewrite setDv in_set0 in Hin.
- destruct (setDP Hin) as [Hxded Hxnotinit].
  destruct (setUP Hxded) as [Hxjded | Hxfwd].
  + by apply/((implyP ((forallP (Hm i_init Hsafe)) x)))/setDP.
  + rewrite big_seq in Hxfwd. destruct (bigcup_seqP _ _ _ _ _ _ Hxfwd) as [cl Hclinp Hx].
    destruct (andP Hx) as [Hxconscl].
    apply ((implyP ((forallP (cons_clause_idb def _ (allP Hsafe _ Hclinp))) x)) Hxconscl).
Qed.

(** If [p] has safe heads, any atom in the semantics from the EDB comes from [init] *)
Lemma sem_idb_in (p : program) (def : syntax.constant) (m : nat) i_init ga :
  prog_safe_hds p -> ga \in (sem p def m i_init) ->
  predtype (sym_gatom ga) == Edb -> ga \in i_init.
Proof.
move => Hpsafe Hgaded Hpredt.
rewrite <- (@setID _ _ i_init) in Hgaded.
destruct (setUP Hgaded) as [Hinit | Hded].
- by destruct (setIP Hinit).
- by rewrite (eqP ((implyP ((forallP (@sem_idb_safe p def m i_init Hpsafe)) ga)) Hded)) in Hpredt.
Qed.

End bSemantics.

