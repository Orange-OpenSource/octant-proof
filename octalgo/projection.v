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
Require Import fixpoint.
Require Import completeness.

From mathcomp
Require Import ssreflect ssrbool eqtype seq ssrnat ssrfun choice fintype tuple finset bigop finfun. 

Require Import bigop_aux.
Require Import utils.
Require Import finseqs.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Projection over a Datalog program *)
Section Projection.

(** ** Base hypotheses *)
(** ***  a safe program [p], an interpretation [i]
  and [def] a default constant *)
Variable p : program.
Hypothesis psafe : prog_safe p.

Variable i : interp.
Hypothesis isafe : safe_edb i.

Variable def : syntax.constant.

(** *** an intensional predicate and an argument index to project over *)
Variable f : symtype.
Hypothesis ftype : predtype f = Idb.
Variable ind : 'I_(arity f).
(** *** The predicate is always defined with a constant at the given index *)
Hypothesis always_cons : 
  [forall cl in p, ((hsym_cl cl) == f) ==> 
    [exists c:syntax.constant, nth_error (arg_atom (head_cl cl)) ind == (Some (Val c))]].

(** *** A function to build new value-indexed predicates *)
Variable pclone : syntax.constant -> symtype.
(** the cloned predicates are not f, different from one another and 
    have the right arity *)
Hypothesis pnotf : [forall c, pclone c != f].
Hypothesis pinj : injective pclone.
Hypothesis parity : [forall c, arity f == (arity (pclone c)).+1].

(** There are enough variables for the P(..,c,..) :- P_c(...) rules *)
Hypothesis arity_vars : arity f < n.+1. 
(** Rule can have at least one element in their bodies *)
Hypothesis bn_not_zero : 0 < bn.


(** ** Checking if a predicate or a ground atom is a clone *)
Definition is_clone_pred (g : symtype) : bool :=
 [exists c, g == pclone c].

Lemma is_clone_clone_pred c : 
 is_clone_pred (pclone c).
Proof.
apply/existsP. by exists c.
Qed.

Definition is_clone_ga (ga : gatom) : bool :=
  is_clone_pred (sym_gatom ga).

(** Hypotheses: no clone in the original program or the EDB *)
Hypothesis pfresh : [forall c, pclone c \notin sym_prog p].
Hypothesis ifresh : ~~ [exists x in i, is_clone_ga x].

(** more usable version of pfresh *)
Lemma Hclp_not_cloned (cl : clause) : 
  cl \in p -> [forall x in wlist_to_seq_co (body_cl cl), ~~ is_clone_pred (sym_atom x)].
Proof.
move=>Hclp. 
apply/forallP=>x. apply/implyP=>Hx.
rewrite negb_exists. apply/forallP=>c.
have Hf := forallP pfresh c.
destruct (bool_des_rew (sym_atom x == pclone c)) as [Hsym|Hsym].
assert (Hff : pclone c \in sym_prog p).
apply/flattenP. exists (sym_cl cl).
apply/mapP. by exists cl.
rewrite -(eqP Hsym). apply/mapP.
exists x. apply/mem_body/Hx.
auto.
by rewrite Hff in Hf.
by rewrite Hsym.
Qed.

(** no clone in the original semantic *)
Lemma original_sem_no_clone (m : nat) :
  [forall x in sem p def m i, ~~ is_clone_ga x].
Proof.
induction m as [|m Hrec].
- apply/forallP=>/= x. apply/implyP=>Hx.
  rewrite negb_exists.
  apply/forallP=>c. 
  destruct (bool_des_rew (sym_gatom x == pclone c)) as [Hc|Hc];
  rewrite Hc;auto.
  assert (Hf : [exists x in i, is_clone_ga x]).
  apply/existsP. exists x. apply/andP;split;auto.
  apply/existsP. exists c. apply Hc.
  have Hff := ifresh.
  by rewrite Hf in Hff.
- apply/forallP=>/=x.
  apply/implyP=>/setUP [Hold|].
  apply (implyP (forallP Hrec _) Hold).
  move=>/bigcup_seqP [cl Hclp /andP [/imsetP [H1 H2 ->] _]].
  rewrite negb_exists.
  apply/forallP=>c. simpl.
  destruct (bool_des_rew (sym_atom (head_cl cl) == pclone c)) as [Hc|Hc];
  rewrite Hc;auto.
  have Hfr := forallP pfresh c.
  rewrite -(eqP Hc) in Hfr.
  assert (Hf : sym_atom (head_cl cl) \in sym_prog p).
  apply/flattenP. exists (sym_cl cl).
  apply/mapP. by exists cl.
  apply/mapP. exists (head_cl cl). apply/mem_head. auto.
  by rewrite Hf in Hfr.
Qed.

(** ** Computing the set of constants used in the definition of f *)
Definition ind_terms :=
  pmap (fun cl => nth_error (arg_atom (head_cl cl)) ind) [seq cl <- p | hsym_cl cl == f].

Definition ind_vals :=
  pmap (fun t => if t is Val c then Some c else None) ind_terms.

Lemma always_cons_in_vals : 
     [forall cl in p, ((hsym_cl cl) == f) 
==>  [exists c in ind_vals, nth_error (arg_atom (head_cl cl)) ind == (Some (Val c))]].
Proof.
apply/forallP=>cl.  apply/implyP=>Hclin.
apply/implyP=>Hsym. apply/existsP.
destruct (existsP (implyP (implyP (forallP always_cons _) Hclin) Hsym)) as [c Hc].
exists c. apply/andP;split. 
rewrite mem_pmap. apply/mapP. exists (Val c).
rewrite mem_pmap. apply/mapP. exists cl.
rewrite mem_filter. apply/andP;split. apply Hsym.
apply Hclin. by rewrite (eqP Hc). reflexivity.
apply Hc.
Qed.

(** ** Cloning the different elements of the program *)

(** *** Atoms *)
Definition raw_atom_clone (j : 'I_(arity f)) (a : raw_atom) : raw_atom :=
  match a with
  | RawAtom pr args => 
      (* we do something only if the atom is about f *)
      if (pr == f) then 
        match nth_error args j with
          | Some (Val c) => RawAtom (pclone c) (sremove args j)
          | _ => RawAtom pr args end
      else RawAtom pr args end.


Lemma wf_clone (j : 'I_(arity f)) (a : atom) : wf_atom (raw_atom_clone j a).
Proof.
destruct a as [[pred args] Ha]. simpl.
destruct (bool_des_rew (pred == f)) as [Hpred|Hpred];rewrite Hpred;[|apply Ha].
unfold wf_atom. simpl.
unfold wf_atom in Ha. simpl in Ha.
have H := @sremove_size _ args. 
rewrite (eqP Ha) (eqP Hpred) in H.
have Hb := (H j).
destruct (nth_error_case args j) as [Hnone|[[v|c] [Hc1 Hc2]]].
- rewrite Hnone. apply Ha.
- rewrite Hc2. apply Ha. 
- rewrite Hc2. 
  have Ht := (eqP (forallP parity c)).
  rewrite Hb in Ht. inversion Ht as [Htb].
  by rewrite Htb.
Qed.

Definition atom_clone (j : 'I_(arity f)) (a : atom) : atom :=
  Atom (wf_clone j a).

(** *** Ground atoms *)
Definition raw_gatom_clone (j : 'I_(arity f)) (a : raw_gatom) : raw_gatom :=
  match a with
  | RawGAtom pr args => 
      (* we do something only if the atom is about f *)
      if (pr == f) then 
        match nth_error args j with
          | Some c => RawGAtom (pclone c) (sremove args j)
          | None => RawGAtom pr args end
      else RawGAtom pr args end.

Lemma wf_gclone (j : 'I_(arity f)) (ga : gatom) : wf_gatom (raw_gatom_clone j ga).
Proof.
destruct ga as [[pred args] Ha]. simpl.
destruct (bool_des_rew (pred == f)) as [Hpred|Hpred];rewrite Hpred;[|apply Ha].
unfold wf_gatom. simpl.
unfold wf_gatom in Ha. simpl in Ha.
have H := @sremove_size _ args. 
rewrite (eqP Ha) (eqP Hpred) in H.
have Hb := (H j).
destruct (nth_error_case args j) as [Hnone|[c [Hc1 Hc2]]].
- rewrite Hnone. apply Ha.
- rewrite Hc2. 
  have Ht := (eqP (forallP parity c)).
  rewrite Hb in Ht. inversion Ht as [Htb].
  by rewrite Htb.
Qed.

Definition gatom_clone (j : 'I_(arity f)) (ga : gatom) : gatom :=
  GAtom (wf_gclone j ga).

(** *** Clauses *)
Definition tail_clone (j : 'I_(arity f)) (tl : tail) : tail :=
  wmap (atom_clone j) tl.

Definition cl_clone (j : 'I_(arity f)) (cl : clause) : clause :=
  match cl with Clause h tl => Clause (atom_clone j h) (tail_clone j tl) end.


(** ** Rewriting clones *)

Lemma atom_clone_not_f (j : 'I_(arity f)) (a : atom) : 
  sym_atom a != f -> atom_clone j a = a.
Proof.
destruct a as [[h args] Hga].
unfold gatom_clone. unfold raw_gatom_clone.
move=>/= Hn. 
destruct (bool_des_rew (h == f)) as [Hhf|Hhf].
rewrite Hhf in Hn. inversion Hn.
apply/val_inj. simpl.
by rewrite Hhf.
Qed.

Lemma gatom_clone_not_f (j : 'I_(arity f)) (ga : gatom) : 
  sym_gatom ga != f -> gatom_clone j ga = ga.
Proof.
destruct ga as [[h args] Hga].
unfold gatom_clone. unfold raw_gatom_clone.
move=>/= Hn. 
destruct (bool_des_rew (h == f)) as [Hhf|Hhf].
rewrite Hhf in Hn. inversion Hn.
apply/val_inj. simpl.
by rewrite Hhf.
Qed.

Lemma gatom_clone_f (j : 'I_(arity f)) (a : atom) c (s : sub) : 
  sym_atom a = f -> 
  nth_error (arg_atom a) j = Some (Val c) ->
    gatom_clone j (gr_atom_def def s a)
  = gr_atom_def def s (atom_clone j a).
Proof.
destruct a as [[h args] Ha].
unfold gatom_clone. unfold raw_gatom_clone.
move=>/= Hsym Hnth. apply/val_inj.
simpl. rewrite Hsym eq_refl.
clear Ha. move:j Hnth.
induction args as [|[v|d] tlargs Hrec];move=>[[|j] Hj] //= Hnth;
by rewrite (nth_error_map (gr_term_def def s) Hnth) Hnth;
  unfold gr_raw_atom_def; simpl; apply/f_equal2; [reflexivity|rewrite sremove_map].
Qed.

Lemma is_clone_ga_f (ga : gatom) :
   sym_gatom ga = f 
-> is_clone_ga (gatom_clone ind ga).
Proof.
move=>Hp.
destruct (nth_error_case (arg_gatom ga) ind) as [Hnone|[c [Hc1 Hc2]]].
- exfalso. have Hf := @oob_nth_error _ (arg_gatom ga). 
  destruct ga as [ga Hga]. rewrite (eqP Hga) Hp in Hf.
  apply (Hf ind Hnone).
- apply/existsP. exists c.
  destruct ga as [[g args] Hga]. simpl. simpl in Hp.
  by rewrite Hp eq_refl Hc2.
Qed.

Lemma clone_oob (j : 'I_(arity f)) (a : atom) : 
  nth_error (arg_atom a) j = None -> (atom_clone j a) = a.
Proof.
move=>H. destruct a as [[g args] Ha]; simpl.
apply/val_inj. simpl.
destruct (bool_des_rew (g == f)) as [Hgf|Hgf];rewrite Hgf;simpl.
by rewrite H. reflexivity.
Qed.

Lemma clone_v (j : 'I_(arity f)) v (a : atom) : 
  nth_error (arg_atom a) j = Some (Var v) -> (atom_clone j a) = a.
Proof.
move=>H. destruct a as [[g args] Ha]; simpl.
apply/val_inj. simpl.
destruct (bool_des_rew (g == f)) as [Hgf|Hgf];rewrite Hgf;simpl.
by rewrite H. reflexivity.
Qed.

Lemma pred_clone_c (j : 'I_(arity f)) c (a : atom) :
   nth_error (arg_atom a) j = Some (Val c)
-> sym_atom a = f
-> sym_atom (atom_clone j a) = pclone c.
Proof.
destruct a as [[g args] Ha].
move=>/= Hnth Hsym.
by rewrite Hsym eq_refl Hnth.
Qed.

(** ** Building the P <- P_c rules *)

(** *** Arguments *)

(** [X_1, X_2, ..., X_j] *)
Definition gen_vars_j (j : 'I_n.+1): seq term := 
 map (fun x => Var x) (map (fun x : 'I_j => @widen_ord j n (ltn_ord j) x) (dep_iota 0 j)).

(** [X_1, X_2, ..., X_(arity f)] *)
Definition gen_vars : seq term :=
  gen_vars_j (Ordinal arity_vars).

(* [X_1, X_2, ..., X_(k-1), X_(k+1), ..., X_(j)]  *)
Definition gen_vars_rem_j (j : 'I_n.+1) (k : 'I_n) : seq term :=
  rem (Var k) (gen_vars_j j).

(* [X_1, X_2, ..., X_(j-1), X_(j+1), ..., X_(arity f)]  *)
Definition gen_vars_rem (j : 'I_(arity f))  : seq term :=
  gen_vars_rem_j (Ordinal arity_vars) (@widen_ord (arity f) n arity_vars j).

(* [X_1, X_2,... X_(ind-1), c, X_(ind+1), ..., X_(arity f)] *)
Definition gen_vars_c_f (j : 'I_(arity f))  (c : syntax.constant) := 
  set_nth (Val c) gen_vars j (Val c).

Lemma ind_in_gen_vars_j (j : 'I_n.+1) (k : 'I_n) : 
  k < j ->
  Var k \in gen_vars_j j.
Proof.
move=>H.
apply/mapP. exists k;auto.
apply/mapP. exists (Ordinal H);auto.
rewrite mem_pmap. 
apply/mapP. exists (val k).
rewrite mem_iota. apply/andP;split.
auto. apply H. by rewrite insubT.
by apply/val_inj. 
Qed.

Lemma ind_in_gen_vars (j : 'I_(arity f)) : 
  Var (widen_ord (m:=n) arity_vars j) \in gen_vars.
Proof.
apply/ind_in_gen_vars_j. 
by destruct j.
Qed.

Lemma size_gen_vars_j (j : 'I_n.+1) :
  size (gen_vars_j j) = j.
Proof.
by rewrite !size_map (@size_dep_iota 0 j).
Qed.

Lemma size_gen_vars : size gen_vars = arity f.
Proof.
by rewrite size_gen_vars_j.
Qed.

Lemma gen_vars_j_find (j : 'I_n.+1) (k : 'I_n) :
   k < j
-> find (eq_op^~ (Var k)) (gen_vars_j j) = k.
Proof.
rewrite !find_map.
unfold preim.
unfold widen_ord. simpl.
rewrite (find_val (dep_iota 0 j) [pred x | x == val k]) dep_iotaE.
apply find_iota.
Qed.

Lemma gen_vars_j_uniq (j : 'I_n.+1) : uniq (gen_vars_j j).
Proof.
rewrite map_inj_in_uniq. rewrite map_inj_in_uniq.
apply/dep_iota_uniq.
move=>x y Hx Hy [H].
destruct x as [x Hxx];
destruct y as [y Hyy].
simpl in H. apply/val_inj/H.
by move=>x y Hx Hy [->].
Qed. 

Lemma gen_vars_rem_uniq (j : 'I_(arity f)) : uniq (gen_vars_rem j).
Proof.
apply/rem_uniq/gen_vars_j_uniq.
Qed.

Lemma gen_vars_j_all_v (j : 'I_n.+1) :
  [forall t in gen_vars_j j, exists v, t == Var v].
Proof.
apply/forallP=>t. apply/implyP. unfold gen_vars.
move=>/mapP [v Hv1 Hv2]. apply/existsP. exists v. apply/eqP/Hv2.
Qed.

Lemma gen_vars_rem_all_v (j : 'I_(arity f)) :
  [forall t in gen_vars_rem j, exists v, t == Var v].
Proof.
apply/forallP=>t. apply/implyP. unfold gen_vars_rem. 
unfold gen_vars_rem_j.
rewrite rem_filter.
rewrite mem_filter. move=>/andP [H1 H2].
apply (implyP (forallP (gen_vars_j_all_v _) t) H2).
apply gen_vars_j_uniq.
Qed.

(** *** Atoms *)

(* raw f(X_1, X_2,... X_(j-1), c, X_(j+1), ..., X_(arity f)) *)
Definition raw_gen_c_f (j : 'I_(arity f))  (c : syntax.constant) : raw_atom :=
  RawAtom f (gen_vars_c_f j c).

Lemma raw_gen_f_c_wf (j : 'I_(arity f)) (c : syntax.constant) : 
  wf_atom (raw_gen_c_f j c).
Proof.
unfold wf_atom.
rewrite size_set_nth size_gen_vars.
apply/eqP/maxn_idPr. by destruct ind.
Qed.

(* f(X_1, X_2,... X_(j-1), c, X_(j+1), ..., X_(arity f)) *)
Definition gen_f_c (j : 'I_(arity f))  (c : syntax.constant) : atom := 
  Atom (raw_gen_f_c_wf j c). 

(* raw f_c(X_1, X_2,... X_(j-1), X_(j+1), ..., X_(arity f)) *)
Definition raw_gen_f_c (j : 'I_(arity f))  (c : syntax.constant) : raw_atom :=
  RawAtom (pclone c) (gen_vars_rem j).

(* f_c(X_1, X_2,... X_(ind-1), X_(ind+1), ..., X_(arity f)) *)
Lemma raw_gen_c_f_c_wf (j : 'I_(arity f))  (c : syntax.constant) : 
  wf_atom (raw_gen_f_c j c). 
Proof.
unfold wf_atom.
simpl. unfold gen_vars_rem. 
rewrite size_rem.
by rewrite size_gen_vars (eqP (forallP parity c)).
apply ind_in_gen_vars. 
Qed.

(* f_c(X_1, X_2,... X_(j-1), X_(j+1), ..., X_(arity f)) *)
Definition gen_c_f_c (j : 'I_(arity f))  (c : syntax.constant) : atom := 
  Atom (raw_gen_c_f_c_wf j c).

(** *** Clauses *)
Lemma gen_c_f_c_size (j : 'I_(arity f))  (c : syntax.constant) : 
 size [:: gen_c_f_c j c] <= bn.
Proof.
apply/leq_trans/leqnn/bn_not_zero.
Qed.

Definition c_to_gen (j : 'I_(arity f)) (c : syntax.constant) :=
  Clause (gen_f_c ind c) (seq_to_wlist_uncut (gen_c_f_c_size j c)).

(** ** Projected program *)
Definition proj_prog := 
  (map (cl_clone ind) p) ++ [seq c_to_gen ind c | c in ind_vals].

Lemma clone_in (cl : clause) : 
  cl \in p ->  cl_clone ind cl \in proj_prog.
Proof.
move=>H. rewrite mem_cat. apply/orP;left.
apply/mapP. by exists cl.
Qed.

(** ** Extracting substitutions for P <- P_c rules *)

(** Builds a substitution that matches the variables of args
    to the values of gargs *)
Fixpoint extract_sub_seq_c (args : seq term) (gargs : seq syntax.constant) 
                           (s : sub) : sub :=
  match gargs with
    [::] => s
  | x::l => 
      match args with
        [::] => s | Val x'::l' => (extract_sub_seq_c l' l s)
      | Var x'::l' => add (extract_sub_seq_c l' l s) x' x end end. 

Lemma v_in_extract_c (args : seq term) (gargs : seq syntax.constant) 
                     (s : sub) (v : 'I_n) :
   size args <= size gargs
-> v \in \big[setU (T:=ordinal_finType n)/set0]_(t <- args) term_vars t 
-> v \in dom (extract_sub_seq_c args gargs s).
Proof.
move:gargs s.
induction args as [|[h|h] args Hrec];move=>[|hg gargs] s //= Hsize 
/bigcup_seqP [t Htin /andP [Ht Htriv]].
by rewrite in_nil in Htin.
by rewrite in_nil in Htin.
rewrite in_cons in Htin. 
destruct (orP Htin) as [Hth|Htargs].
rewrite (eqP Hth) in Ht. rewrite (set1P Ht).
by rewrite in_set ffunE eq_refl.
assert (Htb : v \in \big[setU (T:=ordinal_finType n)/set0]_(t <- args) term_vars t).
apply/bigcup_seqP. exists t. apply Htargs. apply/andP;split;auto.
destruct (bool_des_rew (v == h)) as [Hrew|Hrew]. 
by rewrite in_set ffunE Hrew.
rewrite in_set ffunE Hrew.
have Hr := (Hrec gargs s Hsize Htb). rewrite in_set in Hr. apply Hr.
rewrite in_cons in Htin. 
destruct (orP Htin) as [Hth|Htargs].
by rewrite (eqP Hth) in_set0 in Ht.
assert (Htb : v \in \big[setU (T:=ordinal_finType n)/set0]_(t <- args) term_vars t).
apply/bigcup_seqP. exists t. apply Htargs. apply/andP;split;auto.
apply (Hrec gargs s Hsize Htb).
Qed.

Lemma in_extract_c_v (args : seq term) (gargs : seq syntax.constant) 
                     (v : 'I_n) :
   size args <= size gargs
-> (extract_sub_seq_c args gargs emptysub) v
-> Var v \in args.
Proof.
move:gargs.
induction args as [|[h|h] args Hrec];move=>[|hg gargs] //= Hsize Heq;
try (by rewrite ffunE in Heq).
- rewrite ffunE in Heq.
  destruct (bool_des_rew (v == h)) as [Hvh|Hvh].
  rewrite (eqP Hvh). apply mem_head.
  rewrite Hvh in Heq. apply mem_body.
  apply (@Hrec gargs Hsize Heq).
- apply mem_body.
  apply (@Hrec gargs Hsize Heq).
Qed.

Definition extract_sub_ga (a : atom) (ga : gatom) :=
  extract_sub_seq_c (arg_atom a) (arg_gatom ga) emptysub.

Lemma v_in_extract (a : atom) (ga : gatom) :
   arity (sym_atom a) <= arity (sym_gatom ga)
-> atom_vars a \subset dom (extract_sub_ga a ga).
Proof.
destruct a  as [[g  args]  Ha].
destruct ga as [[gg gargs] Hga].
rewrite -(eqP Ha) -(eqP Hga).
unfold atom_vars. simpl.
move=>/= Hsize. apply/subsetP=>x Hx.
apply (v_in_extract_c emptysub Hsize Hx).
Qed.

Lemma extract_in_v (a : atom) (ga : gatom) :
   arity (sym_atom a) <= arity (sym_gatom ga)
-> dom (extract_sub_ga a ga) \subset atom_vars a .
Proof.
destruct a  as [[g  args]  Ha].
destruct ga as [[gg gargs] Hga].
rewrite -(eqP Ha) -(eqP Hga).
unfold atom_vars.
move=>/= Hsize. apply/subsetP=>x Hx.
rewrite in_set in Hx.
unfold extract_sub_ga in Hx. simpl in Hx.
apply/bigcup_seqP. exists (Var x).
apply (in_extract_c_v Hsize Hx).
apply/andP;split. by apply/set1P. trivial.
Qed.

Lemma extract_dom (a : atom) (ga : gatom) :
   arity (sym_atom a) <= arity (sym_gatom ga)
-> dom (extract_sub_ga a ga) = atom_vars a.
Proof.
move=>Hsize. apply/eqP.
rewrite eqEsubset. apply/andP;split.
apply (extract_in_v Hsize).
apply (v_in_extract Hsize).
Qed.

Lemma var_neq v vb : ((v == vb) = false) -> ((Var v == Var vb) = false).
Proof. 
destruct (bool_des_rew (v == vb)) as [H|H];
rewrite H;move=>// Hb. 
Qed.

Lemma add_seq_gr_def (s : sub) v c (lt : seq term) :
Var v \notin lt ->
[seq gr_term_def def s i0 | i0 <- lt] = [seq gr_term_def def (add s v c) i0 | i0 <- lt].
Proof.
move:s v c. 
induction lt as [|vt lt Hrec];
move=>s vc c //= Hnotin.
apply/f_equal2.
destruct vt as [vh|ch];auto.
- simpl. rewrite ffunE. 
  destruct (bool_des_rew (vh == vc)) as [Heq|Hneq].
  + unfold negb in Hnotin.
    assert (Hf : Var vc \in Var vh :: lt).
    rewrite (eqP Heq). apply/mem_head.
    rewrite Hf in Hnotin. inversion Hnotin.  
  + by rewrite Hneq.
- apply/Hrec.
  unfold negb. unfold negb in Hnotin.
  destruct (bool_des_rew (Var vc \in lt))
    as [H|H].
  + rewrite (mem_body vt H) in Hnotin.
    inversion Hnotin.
  + by rewrite H.
Qed.

Lemma extract_sub_seq_map (lt : seq term) (lc : seq syntax.constant) :
   uniq lt
-> size lt = size lc
-> [forall t in lt, exists v, t == Var v]
-> lc = [seq gr_term_def def (extract_sub_seq_c lt lc emptysub) i0 | i0 <- lt].
Proof.
move:lc. 
induction lt as [|[vh|ch] lt Hrec];
move=>[|hc lc] Huniq Hsize Hallvar //=;
apply/f_equal2.
- by rewrite ffunE eq_refl. 
- destruct (andP Huniq) as [Hu1 Hu2]. 
  rewrite -add_seq_gr_def. apply/Hrec. apply Hu2.
  by inversion Hsize. 
  apply/forallP=>t;apply/implyP=>Ht.
  apply (implyP (forallP Hallvar t)). apply/mem_body/Ht.
  apply Hu1.
- destruct (existsP (implyP (forallP Hallvar (Val ch)) (mem_head _ _)))
    as [x Hf]. have Hff := eqP Hf. inversion Hff.
- destruct (andP Huniq) as [Hu1 Hu2]. 
  apply/Hrec. apply Hu2.
  by inversion Hsize. 
  apply/forallP=>t;apply/implyP=>Ht.
  apply (implyP (forallP Hallvar t)). apply/mem_body/Ht.
Qed.

Lemma extract_sub_seq_rem_map (lt : seq term) v (lc : seq syntax.constant) (j : 'I_n) c:
j < size lt ->
size lt = size lc ->
uniq lt ->
[forall t in lt, exists vb, t == Var vb] ->
find (fun y => y == Var v) lt = j ->
nth_error lc j = Some c ->
lc = [seq gr_term_def def
        (extract_sub_seq_c (rem (Var v) lt) (sremove lc j) emptysub) i
        | i <- set_nth (Val c) lt j (Val c)].
Proof.
move:lc j c.
induction lt as [|[vh|ch] lt Hrec];
move=>[|hc lc] [[|j] Hj] c //= Hsize1 Hsize2 Huniq Hallvar Hfind Hnth.
- apply/f_equal2.
  + by inversion Hnth.
  + destruct (bool_des_rew (vh == v)) as [Hveq|Hvneq].
    - rewrite (eqP Hveq) eq_refl.
      apply/extract_sub_seq_map. by destruct (andP Huniq).
      by inversion Hsize2.
      apply/forallP=>t;apply/implyP=>Ht.
      apply (implyP (forallP Hallvar t)). apply/mem_body/Ht.
    - rewrite (var_neq Hvneq) in Hfind. inversion Hfind.
- destruct (bool_des_rew (vh == v)) as [Hvvh|Hvvh].
  + rewrite (eqP Hvvh) eq_refl in Hfind. inversion Hfind.
  + have Hneq := var_neq Hvvh.
    rewrite Hneq in Hfind. rewrite Hneq.
    apply/f_equal2.
    - by rewrite ffunE eq_refl.
    - rewrite -add_seq_gr_def.
      have Hjb := (ltn_trans (ltnSn _) Hj).
      apply/(@Hrec lc (Ordinal Hjb) c). 
      apply/(ltn_leq_trans (ltnSn _) Hsize1).
      by inversion Hsize2.
      by destruct (andP Huniq).
      apply/forallP=>t. apply/implyP=>Ht.
      apply (implyP (forallP Hallvar _)). apply/mem_body/Ht.
      inversion Hfind as [Hfb]. by rewrite Hfb.
      apply Hnth. apply/set_nth_notin. by destruct (andP Huniq).
      auto.
      by destruct (andP Huniq).
- destruct (existsP (implyP (forallP Hallvar (Val ch)) (mem_head _ _))) as [d Hf].
  have Hff := eqP Hf. inversion Hff.
Qed.

Lemma gr_term_def_seq_add_notin (l : seq term) v c (s:sub) : 
   Var v \notin l
-> [seq gr_term_def def (add s v c) i | i <- l] = [seq gr_term_def def s i | i <- l].
Proof.
induction l as [|h l Hrec];auto.
unfold negb. rewrite in_cons.
destruct (bool_des_rew ((Var v == h) || (Var v \in l))) as [H|H].
by rewrite H.
move:H. move=>/negbT. rewrite Bool.negb_orb. move=>/andP [Hvh Hvl] Htriv.
simpl. rewrite (Hrec Hvl).
destruct h as [v'|c'];auto.
simpl. rewrite ffunE. destruct (bool_des_rew (v' == v)) as [Hvv|Hvv].
rewrite (eqP Hvv) eq_refl in Hvh. inversion Hvh.
by rewrite Hvv.
Qed.

Lemma extract_gr_v (s : sub) (a1 a2 : atom) :
   sym_atom a1 = sym_atom a2 
-> [forall t in (arg_atom a1), exists v:'I_n, t == Var v]
-> uniq (arg_atom a1)
-> gr_atom_def def s a2 =
   gr_atom_def def (extract_sub_ga a1 (gr_atom_def def s a2)) a1.
Proof.
destruct a1 as [[g1 args1] Ha1];
destruct a2 as [[g2 args2] Ha2].
move=>Hsym Hvall Huniq.
apply/val_inj. simpl. unfold gr_raw_atom_def.
unfold extract_sub_ga. simpl.
simpl in Hsym.
assert (Hsize : size args1 = size args2).
by rewrite (eqP Ha1) (eqP Ha2) Hsym.
simpl in Hvall. simpl in Huniq.
clear Ha1. clear Ha2.
move:args2 Hsize s.
unfold gr_raw_atom_def.
induction args1 as [|h1 args1 Hrec];
move=>[|h2 args2] //= Hsize s.
by rewrite Hsym.
destruct (andP Huniq) as [Hu1 Hu2].
rewrite !Hsym.
apply/f_equal.
inversion Hsize as [Hsizeb].
assert (Hvallb : [forall t in args1, exists v, t == Var v]).
apply/forallP=>t. apply/implyP=>Ht.
apply (implyP (forallP Hvall t)). apply/mem_body/Ht.
have Hrecb := (Hrec Hvallb Hu2 args2 Hsizeb s).
inversion Hrecb as [[Hrect1 Hrect2]].
rewrite Hrect2. apply/f_equal2.
destruct h1 as [v|c]. simpl.
unfold odflt. unfold oapp.
by rewrite ffunE eq_refl.
destruct (existsP (implyP (forallP Hvall (Val c))(mem_head (Val c) args1)))
  as [t Ht].
have Hf := eqP Ht. inversion Hf.
destruct h1 as [v|c]. simpl.
rewrite -Hrect2. 
rewrite gr_term_def_seq_add_notin.
by rewrite -Hrect2.
apply Hu1.
by rewrite -Hrect2 -Hrect2.
Qed.

(** ** Matching cloned atoms *)

Lemma match_fold_clone (args : seq term) (gargs : seq syntax.constant) (j : nat) c s :
nth_error args j = Some (Val c) -> nth_error gargs j = Some c ->
foldl
  (fun (acc : option {ffun 'I_n -> option syntax.constant})
     (p0 : syntax.constant * term) => obind (match_term p0.1 p0.2) acc)
  (Some s) (zip gargs args) =
foldl
  (fun (acc : option {ffun 'I_n -> option syntax.constant})
     (p0 : syntax.constant * term) => obind (match_term p0.1 p0.2) acc)
  (Some s) (zip (sremove gargs j) (sremove args j)).
Proof.
move:gargs j s.
induction args as [|hargs tlargs Hrec];move=>[|hgargs tlgargs] [|j] s //=.
- move=> [->] [->]. simpl. by rewrite eq_refl.
- move=> H1 H2.
  destruct hargs as [v|d]. simpl.
  destruct (s v) as [e|]. 
  destruct (bool_des_rew (hgargs == e)) as [H|H];rewrite !H.
  by apply Hrec.
  by rewrite !foldObindNone.
  by apply Hrec. simpl.
  destruct (bool_des_rew (hgargs == d)) as [H|H];rewrite !H.
  by apply Hrec.
  by rewrite !foldObindNone.
Qed.

Lemma match_atom_clone_cnone (j : 'I_(arity f)) (s : sub) (a : atom) c (ga : gatom) :
  nth_error (arg_atom a) j = None \/
       nth_error (arg_atom a) j = Some (Val c) ->
  sym_atom a = sym_gatom ga ->
  match_atom s a ga = match_atom s (atom_clone j a) (gatom_clone j ga).
Proof.
destruct a as [[g args] Ha];
destruct ga as [[gg gargs] Hga].
move=>/= [HaHone|HaVal] Hsyms;
unfold match_atom;
unfold match_raw_atom; simpl.
destruct (bool_des_rew (size args == size gargs)) as [Hsize|Hsize];rewrite !Hsize;
destruct (nth_error_case gargs j) as [Hgnth|[d [Hgnthin Hgnth]]];rewrite !Hgnth;
try (rewrite HaHone) ; try (rewrite HaVal);
try rewrite !Bool.andb_false_r ; try rewrite !Bool.andb_true_r;
try (rewrite (ite_id (gg == f)) (ite_id (g == f)));
try rewrite !Hsize;try rewrite !Bool.andb_false_r ; try rewrite !Bool.andb_true_r;auto.
 (* sizes match / None / Some c *)
- exfalso. apply (nth_error_some_none_size Hgnth HaHone (Logic.eq_sym (eqP Hsize))).
  (* sizes match / Some Var d / Some c *)
- rewrite (ite_id (g == f)).
  destruct (bool_des_rew (gg == f)) as [Hggf|Hggf];rewrite Hggf.
    (* gg = f (= g) *)
  - rewrite Hsyms (eqP Hggf). have Hfd:= (forallP pnotf d).
    destruct (bool_des_rew (f == pclone d)) as [Hfdb|Hfdb];rewrite Hfdb.
    + rewrite (eqP Hfdb) eq_refl in Hfd. inversion Hfd.
    + by rewrite Bool.andb_false_l.
  - by rewrite Hsize Bool.andb_false_r.

rewrite !Hsyms !eq_refl !Bool.andb_true_l.
have Hc := (@arg_c_match j (Atom Ha) (GAtom Hga) s c).
simpl in Hc. destruct (Hc HaVal) as [Hcmatch|[Hgnth Hnomatch]]. clear Hc.
- rewrite !HaVal !Hcmatch.
  rewrite -Hsyms.
  destruct (bool_des_rew (g == f)) as [Hgf|Hgf];rewrite !Hgf ?eq_refl ?Bool.andb_true_l.
  + rewrite !sremove_in_size. 
    destruct (bool_des_rew (size args == size gargs)) as [Hsize|Hsize];rewrite Hsize.
    - rewrite (eqP Hsize) eq_refl. apply (match_fold_clone s HaVal Hcmatch).
    - destruct (bool_des_rew ((size args).-1 == (size gargs).-1)) as [Hsizeb|Hsizeb];rewrite Hsizeb.
      + rewrite (pred_ltn0_l _ (eqP Hsizeb)) in Hsize. 
        rewrite (ltn_predK (nth_error_in_size Hcmatch)) eq_refl in Hsize.
        inversion Hsize.
        apply/leq_ltn_trans. apply (leq0n j). apply (nth_error_in_size HaVal).
      + auto.
      apply (nth_error_in_size Hcmatch).
      apply (nth_error_in_size HaVal).
  + reflexivity.
- unfold match_atom in Hnomatch.
  unfold match_raw_atom in Hnomatch.
  simpl in Hnomatch.
  rewrite !Hsyms !eq_refl !Bool.andb_true_l in Hnomatch.
  rewrite Hnomatch.
  rewrite HaVal.
  destruct Hgnth as [Hgnth|[d [Hd Hgnth]]]; rewrite !Hgnth;
  destruct (bool_des_rew (gg == f)) as [Hggf|Hggf];rewrite Hggf ?eq_refl ?Bool.andb_true_l.
  + destruct (bool_des_rew (pclone c == gg)) as [Hgclone|Hgclone];rewrite Hgclone.
    - have Hf := forallP pnotf c.
      rewrite (eqP Hgclone) Hggf in Hf. inversion Hf.
    - by rewrite Bool.andb_false_l.
  + by rewrite Hnomatch.
  + destruct (bool_des_rew (pclone c == pclone d)) as [Hcd|Hcd];rewrite Hcd.
    - rewrite (pinj (eqP Hcd)) eq_refl in Hd. inversion Hd.
    - by rewrite Bool.andb_false_l.
  + by rewrite Hnomatch.
Qed.

Lemma match_atom_clone_v (j : 'I_(arity f)) (s : sub) (a : atom) (ga : gatom) v :
  nth_error (arg_atom a) j = Some (Var v) ->
  sym_atom a = sym_gatom ga ->
  match_atom s a ga = match_atom s (atom_clone j a) ga.
Proof.
Proof.
destruct a as [[g args] Ha];
destruct ga as [[gg gargs] Hga].
unfold match_atom;
unfold match_raw_atom; simpl.
move=>Hnth Hggg.
rewrite Hggg eq_refl Bool.andb_true_l.
rewrite !Hnth.
by destruct (bool_des_rew (size args == size gargs)) as [Hsize|Hsize];
rewrite !Hsize ite_id !eq_refl !Bool.andb_true_l Hsize.
Qed.

Lemma sym_satom_gatom (a : atom) (ga : gatom) (s : sub) : 
  satom a s = to_atom ga -> sym_atom a = sym_gatom ga.
Proof.
rewrite -(@sym_satom a s).
by move => ->.
Qed.

Lemma match_atom_all_clone_cnone (j : 'I_(arity f)) (k1 k2 : interp) (a : atom) (s : sub) (c : syntax.constant) : 
  k1 :|: [set gatom_clone j ga | ga in k1] \subset k2 ->
  nth_error (arg_atom a) j = None \/ nth_error (arg_atom a) j = Some (Val c) ->
  match_atom_all k1 a s \subset match_atom_all k2 (atom_clone j a) s.
Proof.
move=>/subsetP Hsub Hnth.
apply/subsetP;move=>x;
rewrite !in_set;move=>/imsetP [ga Hgain Heq].
have H := (match_atom_sound (Logic.eq_sym Heq)).
apply/imsetP. exists (gatom_clone j ga). 
apply/Hsub/setUP. right. apply/imsetP. by exists ga.
rewrite Heq. 
unfold opt_sub.
apply (match_atom_clone_cnone s Hnth (sym_satom_gatom H)).
Qed.

Lemma match_atom_all_clone_v (j : 'I_(arity f)) (k1 k2 : interp) (a : atom) (s : sub) v :
  k1 :|: [set gatom_clone j ga | ga in k1] \subset k2 ->
  nth_error (arg_atom a) j = Some (Var v) ->
  match_atom_all k1 a s \subset match_atom_all k2 (atom_clone j a) s.
Proof.
move=>/subsetP Hsub Hnth.
apply/subsetP;move=>x;
rewrite !in_set;move=>/imsetP [ga Hgain Heq].
have H := (match_atom_sound (Logic.eq_sym Heq)).
apply/imsetP. exists ga. 
apply/Hsub/setUP. left. apply Hgain.
rewrite Heq. 
unfold opt_sub.
apply (match_atom_clone_v s Hnth (sym_satom_gatom H)).
Qed.

Lemma pmatch_clone (j : 'I_(arity f)) (s : sub) (k1 k2 : interp) c (cl : clause) (ss : {set sub}) :
 k1 :|: [set gatom_clone j ga | ga in k1] \subset k2 -> 
nth_error (arg_atom (head_cl cl)) j = Some (Val c) ->
 s \in match_pbody (body_cl cl) k1 ss -> 
 exists2 s' : sub, s' \in match_pbody (body_cl (cl_clone j cl)) k2 ss &
  (((hsym_cl cl != f) -> gr_atom_def def s (head_cl cl) =
  gr_atom_def def s' (head_cl (cl_clone j cl))) 
/\ ((hsym_cl cl = f) -> gatom_clone j (gr_atom_def def s (head_cl cl)) =
  gr_atom_def def s' (head_cl (cl_clone j cl)))).
Proof.
move:ss s j k1 k2. destruct cl as [hcl tl]. simpl.
apply (@wlist_ind atom_finType bn
(fun l => forall (ss : {set sub}) (s : sub) (j : 'I_(arity f)) 
(k1 k2 : {set gatom}), 
k1 :|: [set gatom_clone j ga | ga in k1] \subset k2 ->
nth_error (arg_atom hcl) j = Some (Val c) ->
s \in match_pbody l k1 ss ->
exists2
  s' : {ffun 'I_n -> option syntax.constant},
  s' \in match_pbody (tail_clone j l) k2 ss &
  (hsym_cl (Clause hcl tl) != f ->
  gr_atom_def def s hcl =
  gr_atom_def def s' (atom_clone j hcl)) /\
  (hsym_cl (Clause hcl tl) = f ->
   gatom_clone j (gr_atom_def def s hcl) =
   gr_atom_def def s' (atom_clone j hcl)))).
move=>l Ps ss s j k1 k2. unfold wlist_to_seq_co. rewrite wmapK !seq_wlist_uncut_K.
unfold hsym_cl. simpl.
clear Ps. move:ss.
induction l as [|h l Hl]. 

move=>ss Hi H. exists s. auto. split;move=>Hsym.
- by rewrite atom_clone_not_f.
- by rewrite -(gatom_clone_f _ Hsym H).

move=> ss Hsym Hi /match_pbody_cons [sb Hsb H].
destruct (Hl _ Hsym Hi H) as [st Hst Hhead].

destruct (nth_error_case (arg_atom h) j) as [Hnone|[[d|d] [Hd1 Hd2]]].
- exists st. apply/match_pbody_cons. exists sb. apply Hsb.
  apply (subsetP (match_pbody_incr k2 [seq atom_clone j i | i <- l] (@match_atom_all_clone_cnone j _ _ _ _ def Hsym (or_introl Hnone))) st).
  apply Hst.
  apply Hhead.
- exists st. apply/match_pbody_cons. exists sb. apply Hsb.
  apply (subsetP (match_pbody_incr _ _ (@match_atom_all_clone_v j k1 k2 h sb d Hsym Hd2)) _ Hst).
  apply Hhead.
- exists st. apply/match_pbody_cons. exists sb. apply Hsb.
  apply (subsetP (match_pbody_incr _ _ (@match_atom_all_clone_cnone j k1 k2 h sb _ Hsym (or_intror Hd2))) _ Hst).
  apply Hhead.
Qed.

Lemma match_clone (j : 'I_(arity f)) (s : sub) (k1 k2 : interp) c (cl : clause) :
 k1 :|: [set gatom_clone j ga | ga in k1] \subset k2 -> 
nth_error (arg_atom (head_cl cl)) j = Some (Val c) ->
 s \in match_body k1 (body_cl cl) -> 
 exists2 s' : sub, s' \in match_body k2 (body_cl (cl_clone j cl)) &
  (((hsym_cl cl != f) -> gr_atom_def def s (head_cl cl) =
  gr_atom_def def s' (head_cl (cl_clone j cl))) 
/\ ((hsym_cl cl = f) -> gatom_clone j (gr_atom_def def s (head_cl cl)) =
  gr_atom_def def s' (head_cl (cl_clone j cl)))).
Proof.
rewrite !match_body_pbody;try (apply s).
apply pmatch_clone.
Qed.


Lemma pmatch_clone_not_f (j : 'I_(arity f)) (s : sub) (k1 k2 : interp) (cl : clause) (ss : {set sub}) :
(hsym_cl cl != f) ->
 k1 :|: [set gatom_clone j ga | ga in k1] \subset k2 -> 
 s \in match_pbody (body_cl cl) k1 ss -> 
 exists2 s' : sub, s' \in match_pbody (body_cl (cl_clone j cl)) k2 ss &
  gr_atom_def def s (head_cl cl) =
  gr_atom_def def s' (head_cl (cl_clone j cl)).
Proof.
move:ss s j k1 k2. destruct cl as [hcl tl]. simpl.
apply (@wlist_ind atom_finType bn
(fun l => forall (ss : {set sub}) (s : sub) (j : 'I_(arity f)) 
(k1 k2 : {set gatom}), (hsym_cl (Clause hcl l) != f) ->
k1 :|: [set gatom_clone j ga | ga in k1] \subset k2 ->
s \in match_pbody l k1 ss ->
exists2 s' : sub, s' \in match_pbody (tail_clone j l) k2 ss &
  gr_atom_def def s hcl = gr_atom_def def s' (atom_clone j hcl))).
move=>l Ps ss s j k1 k2. unfold wlist_to_seq_co. rewrite wmapK !seq_wlist_uncut_K.
unfold hsym_cl. simpl.
clear Ps. move:ss.
induction l as [|h l Hl]. 

move=>ss Hsym Hi H. exists s. auto.
by rewrite atom_clone_not_f.

move=> ss Hsym Hi /match_pbody_cons [sb Hsb H].
destruct (Hl _ Hsym Hi H) as [st Hst Hhead].

destruct (nth_error_case (arg_atom h) j) as [Hnone|[[d|d] [Hd1 Hd2]]].
- exists st. apply/match_pbody_cons. exists sb. apply Hsb.
  apply (subsetP (match_pbody_incr _ _ (@match_atom_all_clone_cnone j k1 k2 h sb def Hi (or_introl Hnone))) _ Hst).
  by rewrite Hhead atom_clone_not_f.
- exists st. apply/match_pbody_cons. exists sb. apply Hsb.
  apply (subsetP (match_pbody_incr _ _ (@match_atom_all_clone_v j k1 k2 h sb d Hi Hd2)) _ Hst).
  by rewrite Hhead atom_clone_not_f.  (* ind's arg of h is Some (Val d) *)
- exists st. apply/match_pbody_cons. exists sb. apply Hsb.
  apply (subsetP (match_pbody_incr _ _ (@match_atom_all_clone_cnone j k1 k2 h sb _ Hi (or_intror Hd2))) _ Hst).
  by rewrite Hhead atom_clone_not_f.
Qed.

Lemma match_clone_not_f (j : 'I_(arity f)) (s : sub) (k1 k2: interp) (cl : clause) :
 (hsym_cl cl != f) ->
 k1 :|: [set gatom_clone j ga | ga in k1] \subset k2 ->
 s \in match_body k1 (body_cl cl) -> 
 exists2 s' : sub, s' \in match_body k2 (body_cl (cl_clone j cl)) &
  gr_atom_def def s (head_cl cl) =
  gr_atom_def def s' (head_cl (cl_clone j cl)).
Proof.
rewrite !match_body_pbody;try (apply s).
apply pmatch_clone_not_f.
Qed.

Lemma atom_vars_clone_c (a : atom) (j : 'I_(arity f)) c :
   nth_error (arg_atom a) j = Some (Val c)
-> atom_vars a = atom_vars (atom_clone j a).
Proof.
move=>Hnth.
apply/eqP;rewrite eqEsubset. apply/andP;split;
apply/subsetP=>x /bigcup_seqP [y H1 /andP [H2 _]];
apply/bigcup_seqP;exists y;try by apply/andP;split.
- destruct a as [[g args] Ha];simpl.
  destruct (bool_des_rew (g == f)) as [Hgf|Hgf];
  rewrite Hgf;auto.
  rewrite Hnth. simpl. simpl in Hnth. rewrite -(nth_error_sremove Hnth).
  apply H1.
  destruct y. move=>Hf. inversion Hf.
  by rewrite in_set0 in H2.
- destruct a as [[g args] Ha];simpl.
  destruct (bool_des_rew (g == f)) as [Hgf|Hgf];
  unfold atom_clone in H1; unfold raw_atom_clone in H1;
  simpl in H1; rewrite Hgf in H1.
  + rewrite Hnth in H1. simpl in H1.
    simpl in Hnth. rewrite (nth_error_sremove Hnth). apply H1.
    destruct y. move=>Hf. inversion Hf.
    by rewrite in_set0 in H2.
  + apply H1. 
Qed.

Lemma clone_bmatch (j : 'I_(arity f)) (s : sub) (k1 k2 : interp) (cl : clause) :
   [forall x in k2, ~~ is_clone_ga x]
-> k1 \subset k2 :|: [set gatom_clone j ga | ga in k2 & sym_gatom ga == f]
-> s \in match_body k1 (body_cl (cl_clone j cl))
-> cl \in p
-> exists2 s' : sub, bmatch def k2 cl s' & ((s \sub s') &&
  (gr_atom_def def s (head_cl cl) == gr_atom_def def s' (head_cl cl))).
Proof.
move=> Hk2notcloned Hsub /(match_body_bmatch def) H /Hclp_not_cloned. move:H.
destruct cl as [hcl tl]. simpl.
apply (@wlist_ind atom_finType bn
(fun l => 
bmatch def k1 (Clause (atom_clone j hcl) (tail_clone j l)) s ->
[forall x in wlist_to_seq_co l, ~~ is_clone_pred (sym_atom x)] ->
exists2 s' : {ffun 'I_n -> option syntax.constant},
  bmatch def k2 (Clause hcl l) s' & (s \sub s') && (gr_atom_def def s hcl == gr_atom_def def s' hcl))).
move=>l Ps/=. unfold bmatch. unfold cl_vars. simpl. 
unfold wlist_to_seq_co. rewrite !wmapK !seq_wlist_uncut_K.
clear Ps.
destruct (bool_des_rew (tail_vars [seq atom_clone j i | i <- l] \subset dom s)) as [Hdom|Hdom];
try by rewrite Hdom.
rewrite Hdom Bool.andb_true_l.
move:s Hdom.
induction l as [|h l Hrec].
- move=>s H1 H2. exists s.
  by rewrite tail_vars_nil sub0set.
  apply/andP;split;auto.
- move=> s Hdom /andP [Hinh Hintl] Htlnotcloned /=.
  assert (Htlrec : [forall x in l, ~~ is_clone_pred (sym_atom x)] ).
  apply/forallP=>x. apply/implyP=>Hx. apply (implyP (forallP Htlnotcloned _) (mem_body _ Hx)).
  destruct (Hrec s (subset_trans (tail_vars_sub_cons _ _) Hdom) Hintl Htlrec)
        as [sb Hsb1 Hsbb]. destruct (andP Hsbb) as [Hsb2 Hsbeq]. clear Hsbb.
      destruct (bool_des_rew (tail_vars l \subset dom sb)) as [Hdomb|Hdomb];
      try by rewrite Hdomb in Hsb1. rewrite Hdomb in Hsb1.
  destruct (bool_des_rew (sym_atom h == f)) as [Hgf|Hgf].
  + destruct (nth_error_case (arg_atom h) j) as [Hnone|[[v|c] [Hvcin Hvceq]]].
    - exfalso. 
      have Hf := @oob_nth_error _ (arg_atom h). 
      destruct h as [h Hh]. unfold wf_atom in Hh. rewrite (eqP Hh) (eqP Hgf) in Hf.
      apply (Hf j Hnone).
    - exists sb;auto.
      rewrite tail_vars_consUP. rewrite tail_vars_consUP in Hdom.
      destruct (subUsetP Hdom) as [Hdoml Hdomr].
      assert (Hdomt : tail_vars [:: h] :|: tail_vars l \subset dom sb).
      + apply/subUsetP;split.
        rewrite (clone_v Hvceq) in Hdoml.
        apply/subset_trans. apply/Hdoml. apply/sub_dom/Hsb2.
        apply/Hdomb.
      apply/and3P;split;[apply Hdomt| | ].
      + rewrite (clone_v Hvceq) in Hinh.
        destruct (setUP (subsetP Hsub _ Hinh)) as [Hin|Hin].
        rewrite (clone_v Hvceq) tail_vars_1 in Hdoml.
        rewrite -(atom_vars_sub_gr def Hdoml Hsb2). apply Hin.
        destruct (imsetP Hin) as [gab Hgab1 Hgab2].
        rewrite in_set in Hgab1.
        destruct (andP Hgab1) as [Hgab3 Hgabpred]. clear Hgab1.
        assert (Hf : exists c, sym_gatom (gatom_clone j gab) = pclone c).
        destruct gab as [[gp gargs] Hgab].
        unfold gatom_clone. unfold raw_gatom_clone. simpl in *.
        destruct (nth_error_case gargs j) as [Hnone|[c [Hc1 Hc2]]].
        exfalso. have Hf := @oob_nth_error _ gargs.
        unfold wf_gatom in Hgab. simpl in Hgab. rewrite (eqP Hgab) (eqP Hgabpred) in Hf.
        apply/(Hf j)/Hnone.
        exists c. by rewrite Hgabpred Hc2. 
        simpl in Hgab2. 
        destruct Hf as [c Hc].
        assert (Hf : pclone c = f).
        by rewrite -Hc -Hgab2 -(eqP Hgf).
        have Hff := forallP pnotf c. rewrite Hf eq_refl in Hff. inversion Hff.
      + apply Hsb1.
      apply/andP;split;auto.
    - exists sb;auto.
      rewrite tail_vars_consUP. rewrite tail_vars_consUP in Hdom.
      destruct (subUsetP Hdom) as [Hdoml Hdomr].
      assert (Hdomt : tail_vars [:: h] :|: tail_vars l \subset dom sb).
      + apply/subUsetP;split.
        rewrite tail_vars_1. 
        apply/subset_trans.
        rewrite tail_vars_1 -(atom_vars_clone_c Hvceq) in Hdoml. apply Hdoml.
        apply/sub_dom/Hsb2. apply/Hdomb.
      apply/and3P;split;[apply Hdomt| | ].
      + destruct (setUP (subsetP Hsub _ Hinh)) as [Hin|Hin].
        - have Hf := implyP (forallP Hk2notcloned _) Hin.
          unfold negb in Hf. unfold is_clone_ga in Hf.
          simpl in Hf. 
          by rewrite (pred_clone_c Hvceq (eqP Hgf)) is_clone_clone_pred in Hf.
        - destruct (imsetP Hin) as [gab Hgab1 Hgab2].
          rewrite in_set in Hgab1.
          destruct (andP Hgab1) as [Hgab3 Hgabpred]. clear Hgab1.
          assert (Heq : gr_atom (to_gr def sb) h = gab).
          assert (Hebq : val (gr_atom (to_gr def s) (atom_clone j h)) = val (gatom_clone j gab)).
          by rewrite Hgab2. rewrite tail_vars_1 in Hdoml.
          rewrite (atom_vars_sub_gr def Hdoml Hsb2) in Hebq.
          destruct h as [[g args] Hh];destruct gab as [[gg gargs] Hgh]. move:Hebq.
          unfold gr_atom. unfold gr_raw_atom. simpl. simpl in Hgf.
          rewrite Hgf Hvceq. simpl in Hgabpred.
          rewrite Hgabpred. 
          destruct (nth_error_case gargs j) as [Hnone|[d [Hd1 Hd2]]].
          have Hf1 := nth_error_notin_size Hnone.
          assert (Hf2 :size gargs < arity f). apply/leq_ltn_trans. apply Hf1. by destruct j.
          unfold wf_gatom in Hgh. simpl in Hgh. rewrite (eqP Hgh) (eqP Hgabpred) ltnn in Hf2. 
          inversion Hf2.
          rewrite Hd2.
          move=>[Hcdeq Hargseq].
          apply/val_inj. simpl. apply/f_equal2.
          by rewrite (eqP Hgabpred) (eqP Hgf).
          rewrite -sremove_map in Hargseq.
          apply/(nth_error_sremove_eq _ Hargseq).
          rewrite Hd2.
          rewrite -(pinj Hcdeq).
          assert (Hceq : c = gr_term (to_gr def sb) (Val c)). auto.
          rewrite Hceq.
          apply (@nth_error_map _ _ (gr_term (to_gr def sb)) args j). apply Hvceq.
          by rewrite Heq.
      + apply Hsb1.
      apply/andP;split;auto.
  + assert (Hsymb : sym_atom h != f). by rewrite Hgf.
    exists sb;auto.
    rewrite tail_vars_consUP. rewrite tail_vars_consUP in Hdom.
    destruct (subUsetP Hdom) as [Hdoml Hdomr].
    assert (Hdomt : tail_vars [:: h] :|: tail_vars l \subset dom sb).
    + apply/subUsetP;split.
      rewrite (atom_clone_not_f j Hsymb) in Hdoml.
      apply/subset_trans. apply/Hdoml. apply/sub_dom/Hsb2.
      apply/Hdomb.
    apply/and3P;split;[apply Hdomt| | ].
    + rewrite (atom_clone_not_f j Hsymb) in Hinh.
      destruct (setUP (subsetP Hsub _ Hinh)) as [Hin|Hin].
      - rewrite (atom_clone_not_f j Hsymb) tail_vars_1 in Hdoml.
        rewrite -(atom_vars_sub_gr def Hdoml Hsb2). apply Hin.
      - destruct (imsetP Hin) as [gab Hgab1 Hgab2]. clear Hin.
        rewrite in_set in Hgab1. destruct (andP Hgab1) as [Hgabin Hgabpred]. clear Hgab1.
        have Hf := implyP (forallP Htlnotcloned h) (mem_head h _).
      assert (Hff : exists c, sym_gatom (gatom_clone j gab) = pclone c).
      destruct gab as [[gp gargs] Hgab].
      unfold gatom_clone. unfold raw_gatom_clone. simpl in *.
      destruct (nth_error_case gargs j) as [Hnone|[c [Hc1 Hc2]]].
      exfalso. have Hff := @oob_nth_error _ gargs.
      unfold wf_gatom in Hgab. simpl in Hgab. rewrite (eqP Hgab) (eqP Hgabpred) in Hff.
      apply/(Hff j)/Hnone.
      exists c. by rewrite Hgabpred Hc2.
      destruct Hff as [c Hc]. rewrite negb_exists in Hf.
      have Hfff := forallP Hf c. 
      assert (Hsym : sym_gatom (gr_atom (to_gr def s) h) = pclone c).
      by rewrite Hgab2 Hc.
      assert (Hsymt : sym_atom h = pclone c).
      by rewrite -Hsym.
      rewrite Hsymt eq_refl in Hfff. inversion Hfff.
    + apply Hsb1.
    apply/andP;split;auto.
Qed.

(** *** Using the P <- P_c rules *)

Lemma ga_a_ex_sym_eq (j : 'I_(arity f))  c (a : atom) (k : interp) s :
 nth_error (arg_atom a) j = Some (Val c)
-> sym_atom a = f
-> (gr_atom_def def s (atom_clone j a)) \in k
-> exists2 s', s' \in match_body k (body_cl (c_to_gen j c))
 & val (gr_atom_def def s a) = val (gr_atom_def def s' (gen_f_c j c)).
Proof.
move=>H1 H2 H3. 
unfold c_to_gen. 
assert (Hmatch : bmatch def k (c_to_gen j c) (extract_sub_ga (gen_c_f_c j c) (gr_atom_def def s (atom_clone j a)))).
unfold bmatch. 
assert (Hsub : cl_vars (c_to_gen j c) \subset
 dom (extract_sub_ga (gen_c_f_c j c) (gr_atom_def def s (atom_clone j a)))).
unfold c_to_gen. unfold cl_vars. simpl. unfold wlist_to_seq_co. 
rewrite seq_wlist_uncut_K. unfold tail_vars.
apply/subsetP=>x /bigcup_seqP [ato H4 H5].
assert (Harit : arity (sym_atom (gen_c_f_c j c)) <=
       arity (sym_gatom (gr_atom_def def s (atom_clone j a)))).
simpl. destruct a as [[]]. simpl. simpl in H2. rewrite H2 eq_refl.
simpl in H1. by rewrite H1.
apply (subsetP (v_in_extract Harit)).
rewrite mem_seq1 in H4. rewrite (eqP H4) in H5.
by destruct (andP H5).
rewrite Hsub.
simpl. unfold wlist_to_seq_co. rewrite seq_wlist_uncut_K.
simpl. apply/andP;split;auto.
assert (Hgaeq : gr_atom_def def s (atom_clone j a) = gr_atom
  (to_gr def
     (extract_sub_ga (gen_c_f_c j c) (gr_atom_def def s (atom_clone j a))))
  (gen_c_f_c j c)).
rewrite gr_atom_defE.
apply/extract_gr_v. simpl. unfold raw_atom_clone. destruct a as [[]]. simpl.
simpl in H2. simpl in H1. by rewrite H2 eq_refl H1.
simpl. unfold raw_atom_clone. destruct a as [[]]. simpl.
simpl in H2. simpl in H1. 
apply/gen_vars_rem_all_v.
apply/gen_vars_rem_uniq.
rewrite -Hgaeq. apply H3.
destruct (bmatch_match_body Hmatch) as [r Hr1 Hr2].
exists r.
apply Hr1.
unfold gen_f_c. simpl.
destruct a as [[g args] Hga]. simpl. simpl in H2.
rewrite H2. unfold raw_gen_c_f.
assert (Har : arity (sym_atom (gen_c_f_c j c)) <=
       arity (sym_gatom
            (gr_atom_def def s (atom_clone j (Atom (ua:=RawAtom g args) Hga))))).
simpl. by rewrite H2 eq_refl H1.
have Hdom_extract := (extract_dom Har).
move: Hdom_extract Hr2. 
unfold atom_clone ;simpl.
unfold gr_atom_def; simpl.
unfold extract_sub_ga; simpl.
rewrite H2 eq_refl H1. simpl.
move=>Hdom_extract Hr2.
unfold gr_raw_atom_def. simpl. apply/f_equal.
unfold gen_vars_c_f.
have Hdom1 := (match_vars_seteq Hr1).
unfold c_to_gen in Hdom1. unfold wlist_to_seq_co in Hdom1. 
simpl in Hdom1. rewrite seq_wlist_uncut_K in Hdom1.
unfold gen_c_f_c in Hdom1.
rewrite tail_vars_1 in Hdom1. 
rewrite Hdom1 in Hdom_extract.
rewrite (subU_eq (Logic.eq_sym Hdom_extract) Hr2) -sremove_map.
simpl in *.
unfold gen_vars_rem. unfold gen_vars. unfold gen_vars_rem_j.
assert (Hj : j < n). destruct j as [j Hj]. apply/ltn_leq_trans. apply/Hj. apply arity_vars.
rewrite -(@extract_sub_seq_rem_map (gen_vars_j (Ordinal (n:=n.+1) (m:=arity f) arity_vars)) _ [seq gr_term_def def s i | i <- args]
  (Ordinal Hj) c _ _ (gen_vars_j_uniq _)); auto.
rewrite size_gen_vars_j. by destruct j.
rewrite size_map. 
unfold wf_atom in Hga. simpl in Hga.
by rewrite (eqP Hga) H2 size_gen_vars_j.
apply/gen_vars_j_all_v.
apply/gen_vars_j_find. simpl. by destruct j.
by rewrite (@nth_error_map _ _ (gr_term_def def s) args j _ H1).
Qed.

(** If we deduced s(f_c(t1,..,t(ind-1),t(ind+1),...,tn)),
    we can fire f(...,c,...) <-- f_c(....)
    to deduce s(f(t1,...,t(ind-1),c,t(ind+1),...,tn)) *)
Lemma deducing_c_to_gen (s : sub) (a : atom) (c : syntax.constant) (k: interp) :
   sym_atom a = f
-> gr_atom_def def s (atom_clone ind a) \in k
-> nth_error (arg_atom a) ind = Some (Val c)
-> gr_atom_def def s a
    \in cons_clause def (c_to_gen ind c) k.
Proof.
move=>/= Hhead Hsem Hc.
apply/imsetP.
unfold c_to_gen. simpl.
assert (Hsym: sym_gatom (gr_atom_def def s (atom_clone ind a)) = pclone c).
simpl. unfold raw_atom_clone. destruct a as [[]]. simpl in Hhead. simpl.
by rewrite Hhead eq_refl Hc.
destruct (@ga_a_ex_sym_eq ind c a _ _ Hc Hhead Hsem) as [s' Hsb1 Hsb2].
exists s'. apply/(subset_to_in Hsb1)/match_body_incr. auto.
simpl in Hsb2. apply/val_inj. simpl.
by rewrite Hsb2.
Qed.


(** ** Adequacy *)

(** *** Completeness *)

Lemma proj_completeness_u (m : nat) : 
  sem p def m i :|: [set gatom_clone ind ga | ga in sem p def m i] 
    \subset sem proj_prog def m.*2 i.
Proof.
induction m as [|m Hm];apply/subsetP;move=> x /setUP [Hxinit|Hxinit].
- apply Hxinit.
- destruct (imsetP Hxinit) as [ga Hga1 Hga2]. rewrite Hga2.
  have Hf := (eqP (implyP (forallP isafe _) Hga1)).
  destruct (bool_des_rew (sym_gatom ga == f)) as [Hgaf|Hgaf].
  + rewrite (eqP Hgaf) ftype in Hf. inversion Hf.
  + rewrite gatom_clone_not_f. apply Hga1. by rewrite Hgaf.
(* regular deduced *)
- have Hsemb := Hxinit.
  destruct (setUP Hxinit) as [Hxindeduced | Hxrec] ; clear Hxinit ; apply/setUP ; [left | right].
  (* x previously deduced *)
  + apply/(subset_to_in _ (sem_m_incr proj_prog def _ i)). apply ((subsetP Hm) x).
    by apply/setUP;left.
  (* x was just deduced  via clause ccl *)
  + move:Hxrec. 
    move=> /bigcup_seqP [ccl Hclp /andP [/imsetP [s Hsmatch Hhead] _]].
    rewrite Hhead. rewrite Hhead in Hsemb. clear Hhead.
    apply/bigcup_seqP.
    destruct (bool_des_rew ((hsym_cl ccl) == f)) as [Hclf|Hclnf].
      (* ccl headed by f *)
      (* we are going to need the deduction of the clone
         and then of the actual fact, this time
         using the c_to_gen rule *)
    - destruct (existsP (implyP (implyP (forallP always_cons_in_vals _) Hclp) Hclf))
        as [c Hc]. destruct (andP Hc) as [Hc1 Hc2]. clear Hc.
      exists (c_to_gen ind c).
      + rewrite mem_cat. apply/orP;right.
        apply/mapP. exists c. rewrite mem_enum. apply Hc1.
        reflexivity.
      + assert (Hr1 : gr_atom_def def s (head_cl (cl_clone ind ccl)) 
                      \in sem proj_prog def m.*2.+1 i).
        - apply/setUP. right. apply/bigcup_seqP.
          exists (cl_clone ind ccl). apply/clone_in/Hclp.
          apply/andP;split;auto. apply/imsetP.
          destruct (match_clone Hm (eqP Hc2) Hsmatch) as [s' Hsb1 [Hsb2 Hsb3]].
          exists s'. apply Hsb1.
          destruct ccl. simpl. rewrite -Hsb3. 
          by rewrite (gatom_clone_f _ (eqP Hclf) (eqP Hc2)).
          apply/eqP/Hclf.
        apply/andP;split;auto. fold double_rec.
        unfold cl_clone in Hr1. destruct ccl as [hccl tlccl].
        simpl head_cl in Hr1. simpl in Hclf. simpl.
        apply (@deducing_c_to_gen s hccl _ _ (eqP Hclf) Hr1 (eqP Hc2)).
      (* ccl not headed by f *)
    - exists (cl_clone ind ccl).
      + rewrite mem_cat. apply/orP;left.
        apply/mapP. exists ccl. apply Hclp.
        reflexivity.
      + apply/andP ; split ; trivial.
        assert (Hdedsub : (sem p def m i) :|: [set gatom_clone ind ga | ga in sem p def m i] 
            \subset (sem proj_prog def m.*2 i)).
        apply/subsetP ; move => y Hy.
        apply ((subsetP Hm) y Hy).
        apply/imsetP. 
        assert (Hb : hsym_cl ccl != f). by rewrite Hclnf.
        fold double_rec.
        apply/(@match_clone_not_f ind s _ _ ccl Hb _ Hsmatch).
        unfold sem in Hdedsub. unfold iter in Hdedsub.
        apply/subset_trans. apply Hdedsub. apply sem_m_incr.
(* clone deduced [wip] *)
- (* have Hsemb := Hxinit. *)
  destruct (imsetP Hxinit) as [ga Hgaded ->].
  have Hsemb := Hgaded.
  destruct (setUP Hgaded) as [Hxindeduced | Hxrec] ; clear Hxinit ; apply/setUP ; [left | right].
  (* x previously deduced *)
  + apply/(subset_to_in _ (sem_m_incr proj_prog def _ i)). apply ((subsetP Hm) _).
    apply/setUP;right. apply/imsetP. by exists ga.
  (* x was just deduced  via clause ccl *)
  + move:Hxrec. 
    move=> /bigcup_seqP [ccl Hclp /andP [/imsetP [s Hsmatch Hhead] _]].
    apply/bigcup_seqP.
    exists (cl_clone ind ccl).
    - rewrite mem_cat. apply/orP. left.
      apply/mapP. exists ccl. apply Hclp.
      reflexivity.
    - apply/andP;split;auto.
      rewrite Hhead.
      apply/imsetP. 
    destruct (bool_des_rew ((hsym_cl ccl) == f)) as [Hclf|Hclnf].
      (* ccl headed by f *)
      (* we are going to need the deduction of the clone
         and then of the actual fact, this time
         using the c_to_gen rule *)
    - destruct (existsP (implyP (implyP (forallP always_cons_in_vals _) Hclp) Hclf))
        as [c Hc]. destruct (andP Hc) as [Hc1 Hc2]. clear Hc.
      destruct (match_clone Hm (eqP Hc2) Hsmatch) as [s' Hsb1 [Hsb2 Hsb3]].
      exists s'. 
      apply/(subsetP (match_body_incr (cl_clone ind ccl) _))/Hsb1/sem_m_incr.
      destruct ccl. simpl. rewrite -Hsb3. 
      by rewrite (gatom_clone_f _ (eqP Hclf) (eqP Hc2)).
      apply/eqP/Hclf.
    - assert (Hdedsub : (sem p def m i) :|: [set gatom_clone ind ga | ga in sem p def m i] 
            \subset (sem proj_prog def m.*2 i)).
        apply/subsetP ; move => y Hy.
        apply ((subsetP Hm) y Hy).
        apply/imsetP. 
        assert (Hb : hsym_cl ccl != f). by rewrite Hclnf.
        fold double_rec.
        apply/imsetP.
        destruct (@match_clone_not_f ind s _ (sem proj_prog def m.*2 i) ccl Hb Hdedsub Hsmatch)
          as [s' Hmatch' Hgreq].
        exists s'.
        apply/(subsetP (match_body_incr (cl_clone ind ccl) _))/Hmatch'/sem_m_incr.
        destruct ccl. simpl. by rewrite -Hgreq gatom_clone_not_f.
Qed.

Theorem proj_completeness (m : nat) : 
  sem p def m i \subset sem proj_prog def m.*2 i.
Proof.
apply/subsetP=>x Hx.
apply (subsetP (proj_completeness_u m)).
by apply/setUP;left.
Qed.

(** *** Soundness *)

Lemma gr_atom_def_clone_eq (j : 'I_(arity f)) a s sb :
   gr_atom_def def s (atom_clone j a) = gr_atom_def def sb (atom_clone j a)
-> gr_atom_def def s a = gr_atom_def def sb a.
Proof.
destruct (bool_des_rew (sym_atom a == f)) as [Hf|Hf].
- destruct (nth_error_case (arg_atom a) j) as [Hnone|[[v|c] [Hvc1 Hvc2]]].
  by rewrite !(clone_oob Hnone).
  by rewrite !(clone_v Hvc2).
  destruct a as [[g args] Ha]. clear Hvc1. move:j c Hvc2.
  unfold atom_clone. simpl in Hf. unfold raw_atom_clone. simpl.
  unfold gr_atom_def. simpl.
  induction args as [|ha args Hrec];
  move=>[[|j] Hj] c //=.
  + move=>[->] [Heq]. apply/val_inj. simpl. 
    rewrite Hf in Heq. unfold gr_raw_atom_def.
    apply/f_equal. simpl. apply/f_equal. apply Heq.
  + move=>Hnth [Heq].
    apply/val_inj. unfold gr_raw_atom_def. simpl.
    apply/f_equal. simpl.
    rewrite Hf Hnth in Heq. inversion Heq as [[Heq1 Heq2]].
    apply/f_equal. 
    rewrite -(@sremove_map _ _ args j (gr_term_def def sb)) in Heq2.
    rewrite -(@sremove_map _ _ args j (gr_term_def def s)) in Heq2.
    apply/(nth_error_sremove_eq _ Heq2).
    assert (Hc : nth_error [seq gr_term_def def sb i | i <- args] j = Some c).
    assert (Hcb : c = gr_term_def def sb (Val c) ). auto.
    rewrite Hcb. apply/nth_error_map/Hnth. rewrite Hc.
    assert (Hcb : c = gr_term_def def s (Val c) ). auto.
    rewrite Hcb. apply/nth_error_map/Hnth.  
- assert (Hff : (sym_atom a != f)). by rewrite Hf.
  by rewrite !(atom_clone_not_f j Hff).
Qed.

Lemma proj_soundness_u (m : nat) : 
  sem proj_prog def m i \subset 
  sem p def m i :|: [set gatom_clone ind ga | ga in sem p def m i & sym_gatom ga == f].
Proof.
induction m as [|m Hm];apply/subsetP;move=> x /=.
- move=>Hx. by apply/setUP;left. 
- move=>Hded. destruct (setUP Hded) as [Hxinit|Hxinit].
  + destruct(setUP (subsetP Hm _ Hxinit)) as [Hrec|Hrec].
    apply/setUP;left. by apply/setUP;left.
    destruct (imsetP Hrec) as [ga Hga ->].
    rewrite in_set in Hga. destruct (andP Hga) as [Hga1 Hga2].
    apply/setUP;right. apply/imsetP. exists ga. 
    rewrite in_set;apply/andP;split.
    by apply/setUP;left. apply Hga2.
    reflexivity.
  + move:Hxinit. 
    move=> /bigcup_seqP [ccl Hclp /andP [/imsetP [s Hsmatch Hhead] _]].
    rewrite Hhead. rewrite Hhead in Hded. clear Hhead.
    rewrite mem_cat in Hclp. destruct (orP Hclp) as [Hclone|Hclpp].
    - destruct (mapP Hclone) as [clb Hclb1 Hclb2].

      rewrite Hclb2 in Hsmatch.
      destruct (clone_bmatch (original_sem_no_clone m) Hm Hsmatch Hclb1)
        as [sb Hsb1 Hsb2]. destruct (andP Hsb2) as [Hsb3 Hsb4]. clear Hsb2.
      destruct (bool_des_rew ((hsym_cl clb) == f)) as [Hclf|Hclnf].
      + destruct (existsP (implyP (implyP (forallP always_cons_in_vals _) Hclb1) Hclf))
        as [c Hc]. destruct (andP Hc) as [Hc1 Hc2]. clear Hc.
        apply/setUP;right. apply/imsetP. rewrite Hclb2.
        exists (gr_atom_def def s (head_cl clb)).
        - rewrite in_set;apply/andP;split.
          + apply/setUP;right. apply/bigcup_seqP.
            exists clb. apply Hclb1.
            apply/andP;split;auto.
            apply/imsetP. destruct (bmatch_match_body Hsb1) as [st Hst1 Hst2].
            exists st. apply Hst1.
            destruct clb as [a tl]. simpl. simpl in Hsb4.
            unfold hsym_cl in Hclf. simpl in Hclf. simpl in Hc2.
            rewrite (eqP Hsb4). 
            apply/Logic.eq_sym/(atom_vars_sub_gr_def def _ Hst2).
            apply/subset_trans. apply/(allP psafe _ Hclb1). apply/match_vars_subset/Hst1.
          + apply Hclf.
        - apply/val_inj. simpl. rewrite Hclf. 
          rewrite (nth_error_map (gr_term_def def s) (eqP Hc2)).
          unfold cl_clone. destruct clb as [[[g args] Hh] tl]. simpl. simpl in Hc2.
          by rewrite Hclf (eqP Hc2) sremove_map.
      + apply/setUP;left. apply/setUP;right. apply/bigcup_seqP.
        exists clb. apply Hclb1. apply/andP;split;auto.
        apply/imsetP. destruct (bmatch_match_body Hsb1) as [st Hst1 Hst2].
        exists st. apply Hst1. rewrite Hclb2. unfold cl_clone. destruct clb as [h tl].
        simpl. rewrite atom_clone_not_f. rewrite (eqP Hsb4). simpl.
        apply/Logic.eq_sym/(atom_vars_sub_gr_def def _ Hst2).
        apply/subset_trans. apply/(allP psafe _ Hclb1). apply/match_vars_subset/Hst1.
        unfold hsym_cl in Hclnf. simpl in Hclnf. by rewrite Hclnf.
    - destruct (mapP Hclpp) as [c Henum ->].
      have Hb := (match_body_bmatch def Hsmatch).
      unfold bmatch in Hb. 
      destruct (bool_des_rew (cl_vars (c_to_gen ind c) \subset dom s))
        as [Hdom|Hdom]; try by rewrite Hdom in Hb.
      rewrite Hdom in Hb.
      simpl in Hb. unfold wlist_to_seq_co in Hb. rewrite seq_wlist_uncut_K in Hb.
      simpl in Hb. destruct (andP Hb) as [Hbb Htriv]. clear Hb. clear Htriv.
      destruct (setUP ((subsetP Hm) _ Hbb)) as [Hf|Hf].
      + have Hff := implyP (forallP (original_sem_no_clone m) _) Hf.
        assert (Hfff : is_clone_ga (gr_atom (to_gr def s) (gen_c_f_c ind c))).
        apply/existsP. by exists c.
        by rewrite Hfff in Hff.
      + destruct (imsetP Hf) as [ga Hga1 Hga2]. 
        rewrite in_set in Hga1. destruct (andP Hga1) as [Hga3 Hga4].
        apply/setUP;left.
        apply/setUP;left. simpl.
        rewrite gr_atom_defE in Hga2.
        assert (Heq : ga = gr_atom_def def s (gen_f_c ind c)).
        move:Hga2. unfold gr_atom. unfold gen_c_f_c.
        unfold raw_gen_f_c. unfold gen_f_c. simpl. unfold gatom_clone.
        unfold raw_gatom_clone. destruct ga as [[g args] Hg]. simpl.
        simpl in Hga4.
        move=>[Heq]. rewrite Hga4 in Heq.
        destruct (nth_error_case args ind) as [Hnone|[d [Hd1 Hd2]]].
        rewrite Hnone in Heq. inversion Heq as [Hpf].
        have Hff := forallP pnotf c. by rewrite Hpf (eqP Hga4) eq_refl in Hff.
        rewrite Hd2 in Heq. inversion Heq as [[Hpeq Haeq]].
        have Hcd := pinj Hpeq. apply/val_inj.
        simpl. unfold raw_gen_c_f. unfold gr_raw_atom_def. simpl.
        rewrite (eqP Hga4). apply/f_equal.
        unfold gen_vars_c_f. simpl. rewrite Hcd.
        unfold gen_vars_rem in Haeq.
        unfold gen_vars_rem_j in Haeq. simpl in Haeq.
        apply/(@nth_error_sremove_eq _ _ _ ind).
        apply/Logic.eq_sym. assert (Hd : d = gr_term_def def s (Val d)). auto.
        rewrite Hd2 Hd. apply/nth_error_map/nth_error_set_nth.
        rewrite -Haeq. rewrite sremove_map. apply/f_equal/Logic.eq_sym. 
        rewrite sremove_nth. apply/sremove_rem.
        apply/gen_vars_j_find. simpl. auto. by rewrite size_gen_vars.
        by rewrite size_gen_vars. by rewrite -Heq.
Qed.

Theorem proj_soundness (m : nat) : 
  [set x in sem proj_prog def m i | ~~ is_clone_ga x ] \subset sem p def m i.
Proof.
apply/subsetP=>x. rewrite in_set.
move=>/andP [Hxsem Hnotcloned]. 
destruct (setUP (subsetP (proj_soundness_u m) _ Hxsem)) as [H|H];auto.
destruct (imsetP H) as [ga H1 H2].
rewrite in_set in H1. destruct (andP H1) as [H3 H4]. clear H1.
assert (Hf : is_clone_ga x).
rewrite H2. apply/is_clone_ga_f/(eqP H4).
by rewrite Hf in Hnotcloned.
Qed.

End Projection.

