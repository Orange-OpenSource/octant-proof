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
Require Import monotonicity.
Require Import soundness.
Require Import dTypes.
Require Import ddTypes.

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset bigop finfun.

Require Import bigop_aux.
Require Import utils.
Require Import finseqs.

Require Import Coq.Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Typing rules *)
Section rules.

(** ** Computing of occurrences of variables in terms, atoms, clauses *)
(** Given a list of pair with a bounded number as first element gives back the list with the
   numbers incremented *)
Definition shift1 {k : nat} {A : finType} (l : {set ('I_k * A)%type}) : {set ('I_k.+1 * A)%type} :=
  [set ((Ordinal (ord_shift x.1)), x.2) | x in l].

(** For a given list of terms [l] gives back the set of indices of terms of l that are a variable *)
Definition occsInTermList (v : 'I_n) (l : seq term) : {set 'I_max_ar} :=
  [set i : 'I_max_ar | nth_error l i == Some (Var v)].

(** Gives back the indexes of the variables in an atom *)
Definition occsInAtom (a : atom) (v : 'I_n) : {set 'I_max_ar} :=
[set x | x in (@occsInTermList v (arg_atom a))].

(** Accessing the term in atom [a] at an index from [occsInAtom a] will indeed give back a
  variable *)
Lemma occsInAtomV occ a v : occ \in occsInAtom a v -> nth_error (arg_atom a) occ = Some (Var v).
Proof.
move => /imsetP [ind Hindin Hineq].
rewrite Hineq.
rewrite in_set in Hindin. by apply/eqP.
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

(** ** The rules *)
(**
  [predTyping p v ct f j typ] states that the argument [j] of
  predicate [f] has type [typ] for
  a given occurrence
  - [p] the program where typing occurs
  - [v] not used directly
  - [ctxt] a context to avoid (a set of term occurrences)
  - [f] symbol type of the atom carrying the [v] occurrence
  - [j] position in the arguments
  - [typ] the type found

  - [pt_base] the base case for extentional predicates
  - [pt_rec] the case for IDB predicates using [progPredTyping]

 [varTyping p ctxt v typ] states that variable [v] has type [t]
  - [p] the program where typing occurs
  - [ctxt] a context to avoid (a set of term occurrences)
  - [v] variable being typed
  - [typ] the type found

  - [vt] the only case accumulates.

 [progPredTyping p v ctxt p' f j typ] computes the types for
 argument [j] of predicate [f] in the program reduced to [p'].
 This predicate is used to accumulate types of [f] from the various
 clauses defining it.
  - [p] the program where the typing occurs
  - [v] not used
  - [ctxt] a context to avoid (a set of term occurrences)
  - [p'] the partial program considered
  - [f] symbol type of the atom carrying the [v] occurrence
  - [j] position in the arguments
  - [ltyp] the relevant types found so far

  - [ppt_base] starting with an empty set of clause: empty list of types
  - [ppt_rec_yes] adding a new clause whose head symbol is [f]
  - [ppt_rec_no] adding a new clause whose head symbol is not [f]

 [occsToTypes p v ct occs ltyps] gives the types of all the occurrences
 [occs] (that are occurrences of [v])
   - [p] the program where the typing occurs
   - [v] not used
   - [ctxt] a context to avoid (a set of term occurrences)
   - [occs] occurrences of [v] avoiding [ctxt]
   - [ltyps] the sequence of types of the occurrences.
*)
(** the vs in rules other than varTyping
   seem useless but are used in the induction principle *)
Inductive predTyping : forall p v (ctxt : (tocs p)) (f : symtype), 'I_max_ar -> (DDtype ctxt) -> Prop :=
  (*| pt_triv : forall p v (ct : tocs p) f j, @predTyping p v ct f j (mk_DDtype (@TrivDDtype p ct))*)
  | pt_base : forall p v (ct : tocs p) f j, (predtype f = Edb) -> @predTyping p v ct f j (mk_DDtype (@tInitDDtype p ct))
  | pt_rec : forall p v (ct : tocs p) pred (j : 'I_max_ar) typs,
              predtype pred = Idb ->
              @progPredTyping p v ct p pred j typs ->
              @predTyping p v ct pred j (fold_type_alg DtDisj typs DEmpty)
with
 varTyping : forall p (ctxt : tocs p), 'I_n -> (DDtype ctxt) -> Prop :=
  (*| v_triv : forall p (ct : tocs p) v, @varTyping p ct v (mk_DDtype (@TrivDDtype p ct))*)
  | vt : forall p (ct : tocs p) (tot : 'I_(bn*max_ar).+1) v occsTypes,
                              (* getting rid of stuff that has already been typed *)
            @OccsToTypes p v ct (seq_to_enotin (occsInProgram p v) ct) occsTypes ->
            @varTyping p ct v (fold_type_alg DtConj occsTypes (mk_DDtype (@TrivDDtype p ct)))
with
  (*  full prog -> context -> intermediate prog -> pred -> ind -> intermediate types *)
  progPredTyping : forall p v (ctxt : tocs p) (ip : program) (f : symtype) (ind : 'I_max_ar), seq (DDtype ctxt) -> Prop :=
  | ppt_base :    forall fp v ct pred j, @progPredTyping fp v ct [::] pred j [::]
  | ppt_rec_no :  forall p v (ctxt : tocs p) ip pred new_cl j typs,
                  @progPredTyping p v ctxt ip pred j typs ->
                  (pred <> (hsym_cl new_cl)) ->
                  @progPredTyping p v ctxt (new_cl :: ip) pred j typs
  | ppt_rec_yes : forall p v (ctxt : tocs p) ip new_cl j typs ntyp v',
                  @progPredTyping p v ctxt ip (hsym_cl new_cl) j typs ->
                  (nth_error (arg_atom (head_cl new_cl)) j) == Some (Var v') ->
                  @varTyping p ctxt v' ntyp ->
                  @progPredTyping p v ctxt (new_cl :: ip) (hsym_cl new_cl) j (ntyp :: typs)
with
  OccsToTypes : forall p (v : 'I_n) (ctxt : tocs p), {set (enotin ctxt)} -> seq (DDtype ctxt) -> Prop :=
    (* When typing an empty set of occurrences, returns an empty list of types *)
  | colt_base : forall p v (ct : tocs p), @OccsToTypes p v ct (seq_to_enotin set0 ct) [::]
    (* The set l has (recursively) been typed as the list typs. Adding occurrence tocc to the set
       triggers a call to predTyping, with tocc added to the context *)
  | colt_rec :  forall p v ct tocc l typs (dt : DDtype (ct :|: [set (elnotin tocc)])) pato rul_ind body_ind aind,
                @OccsToTypes p v ct l typs ->
                (elnotin tocc) = (T_occ rul_ind body_ind aind) ->
                p_at (val tocc) = Some pato ->
                @predTyping p v (ct :|: [set (elnotin tocc)]) pato aind dt ->
                @OccsToTypes p v ct ([set tocc] :|: l) ((@DtInsert p ct (elnotin tocc) dt (Helnotin tocc) (@ddtextract p ct (val tocc) dt))::typs).

Scheme varTyping_mrec := Induction for varTyping Sort Prop
  with occsToTypes_mrec := Induction for OccsToTypes Sort Prop
  with predTyping_mrec := Induction for predTyping Sort Prop
  with progPredTyping_mrec := Induction for progPredTyping Sort Prop.

(** computing the disjunction of types found by [progPredTyping] does
   not yield a type [tInit] *)
Lemma progPred_not_init {p'} v {ctxt : tocs p'} f j (typs: seq (DDtype ctxt))
(Hppt : progPredTyping v p' f j typs) : val (fold_type_alg DtDisj typs DEmpty) <> tInit p'.
Proof.
apply (@progPredTyping_mrec
  (fun p' (ctxt' : tocs p') v' (t : DDtype ctxt') (Hvt : varTyping v' t) => val t <> tInit p')
  (fun p' v' (ctxt' : tocs p') (l : {set (enotin ctxt')}) (l0 : seq (DDtype ctxt')) (Hott : OccsToTypes v' l l0)
       => all_prop (fun t => t <> tInit p') (map val l0))
  (fun p' v' (ctxt' : tocs p') f (o : 'I_max_ar) (d : (DDtype ctxt')) (Hpt : predTyping v' f o d)
     (* val d <> tInit p' -> forall tocc, P (insert tocc d) (et éventuellement P d en sus) *)
    => predtype f = Idb -> val d <> tInit p')
  (fun p' v' (ctxt' : tocs p') ip' f (ind : 'I_max_ar) (l : seq (DDtype ctxt')) (Hppt : progPredTyping v' ip' f ind l)
      => val (fold_type_alg DtDisj l DEmpty) <> tInit p')) with (f7 := f) (ind := j) (ip := p') (v := v) ; try (move => //).
- move => pb ct' occs v' occsTypes Hott Htatall. apply/notInitSeq/Htatall.
- move => /= pb v' ct' tocc l typs' dt ato rind bind aind Hott Hall Htocc Hatat Hpt Hdtnotinit ; split.
  apply tInsert_not_init.
- apply Hall.
- move => pb v' ct' f' vb Hpt1 Hpt2. by rewrite Hpt1 in Hpt2.
- intros. move=>[/eqP Hf].
  rewrite eq_sym -subset0 in Hf. have Hfb := subsetP Hf [set unil]. rewrite in_set0 in Hfb.
  assert false. by apply/Hfb/set1P. auto.
- move => pb v' ct' ip ncl j' typs0 [[|ntyp] Hntyp] vb Hpptb Hfoldninit Hnth Hvt Hntypninit.
  simpl. auto. simpl. destruct ((fold_type_alg DtDisj typs0)) as [d Hd]. simpl in *.
  destruct d as [|d]. auto. unfold tInit. move => Hfalse. inversion Hfalse as [Hffalse].
  move:Hffalse. move => /eqP. rewrite eqEsubset. move => /andP [/subsetP Hs1 /subsetP Hs2].
  destruct (setUP (Hs2 [set unil] (set11 [set unil]))) as [Huntyp | Hud].
  + apply/Hntypninit/f_equal/eqP. rewrite eqEsubset. apply/andP ; split ; apply/subsetP ; move => y Hy.
    - apply/Hs1/setUP ; left ; apply Hy.
    - move:Hy. move=>/set1P Hy. by rewrite Hy.
  + apply/Hfoldninit/f_equal/eqP. rewrite eqEsubset. apply/andP ; split ; apply/subsetP ; move => y Hy.
    - apply/Hs1/setUP ; right ; apply Hy.
    - move:Hy. move=>/set1P Hy. by rewrite Hy.
Qed.

(** ** Occurrences in types refer to variables *)
(** [all_tat] checks that all the occurrence appearing in a type are
  pointing to variables. *)
Definition all_tat {p'} (t : Dtype p') :=
   forall ct, ct \in dt_get_dcb t -> forall br, br \in pred_of_set ct
-> all (fun x : t_occ p' => [exists v', t_at x == Some (Var v')]) br.

(** True of the trivial type *)
Lemma all_tat_triv {p'} {ctxt : tocs p'} :
  all_tat (mk_DDtype (TrivDDtype (p:=p') ctxt)).
Proof.
move=>ct. by rewrite in_set.
Qed.

(** Trop of the init type *)
Lemma all_tat_init {p'} {ctxt : tocs p'} :
  all_tat (mk_DDtype (tInitDDtype (p:=p') ctxt)).
Proof.
by move=>ct /set1P -> br /set1P ->.
Qed.

(** True when building the conjunction of a list of types verifying the property *)
Lemma all_tat_conj {p'} {ctxt : tocs p'} (l : seq (DDtype ctxt)) :
all_prop all_tat (map val l) -> all_tat (fold_type_alg DtConj l (mk_DDtype (@TrivDDtype _ ctxt))).
Proof.
induction l as [|[[|h]] l Hl];simpl.
move=>H. apply (@all_tat_triv p' ctxt).
move=>[H1 H2] ct /=.
unfold dt_get_dcb. destruct (fold_type_alg DtConj l) as [[|]].
by rewrite in_set0. move=>/= Hd br Hbr.
unfold all_tat in Hl. simpl in Hl. apply Hl with (ct := ct).
apply H2. apply Hd. apply Hbr.
move=>[H1 H2]. destruct (fold_type_alg DtConj l) as [[|]]. apply H1.
move=>x /imset2P [a b Hain Hbin ->] br /setUP[Hnew|Hrec].
apply (H1 a Hain br Hnew).
apply (Hl H2 b Hbin br Hrec).
Qed.

(** True when building the disjunction of a list of types verifying the property *)
Lemma all_tat_disj {p'} {ctxt : tocs p'} (l : seq (DDtype ctxt)) :
all_prop all_tat (map val l) -> all_tat (fold_type_alg DtDisj l DEmpty).
Proof.
induction l as [|[[|h]] l Hl].
move=>H ct. by rewrite in_set0.
move=> [Hh Htl]. apply (@all_tat_triv _ ctxt).
move=> [Hh Htl] x.
simpl. destruct (fold_type_alg DtDisj l) as [[|]].
by rewrite in_set0.
move=>/setUP[Hg|Hd].
apply (Hh x Hg).
apply (Hl Htl x Hd).
Qed.

(** varTyping builds a type verifing [all_tat] *)
Lemma typing_tat {p'} {ctxt : tocs p'} (v : 'I_n) (t : DDtype ctxt) (Hvt : varTyping v t):
  all_tat t.
Proof.
apply (@varTyping_mrec
  (fun p' (ctxt' : tocs p') v' (t : DDtype ctxt') (Hvt : varTyping v' t)
      => all_tat t)
  (fun p' v' (ctxt' : tocs p') (l : {set (enotin ctxt')}) (l0 : seq (DDtype ctxt')) (Hott : OccsToTypes v' l l0)
       => [forall x in l, (t_at (val x)) == Some (Var v')]
          -> all_prop all_tat (map val l0))
  (fun p' v' (ctxt' : tocs p') f (o : 'I_max_ar) (d : (DDtype ctxt')) (Hpt : predTyping v' f o d)
     (* val d <> tInit p' -> forall tocc, P (insert tocc d) (et éventuellement P d en sus) *)
    => all_tat d)
  (fun p' v' (ctxt' : tocs p') ip' f (ind : 'I_max_ar) (l : seq (DDtype ctxt')) (Hppt : progPredTyping v' ip' f ind l)
      => all_prop all_tat (map val l))) with (o := v);move=>//.
(*- intros. apply all_tat_triv.*)
- move=>pb ctb jb vb ob Hob H. apply/all_tat_conj/H.
  apply/forallP=>x. apply/implyP=>Hx. apply/eqP.
  apply occsInProgramV.
  destruct (imsetP (mem_pset_set Hx)). unfold insub in H1.
  destruct idP in H1. inversion H1. apply H0.
  inversion H1.
- move=>pb vb ctb tocc l typs dd ato rind bind aind H1 H2 H3 H4 H5 H6 H7.
  split.
  unfold all_tat. destruct dd as [[|]].
  move=>x. by rewrite in_set0.
  move=>ct /imsetP [[x Hx] Hxin ->] br /imsetP [[y Hy] Hyin ->].
  apply/andP;split. apply/existsP. exists vb.
  apply (implyP (forallP H7 _)). by apply/setUP;left;apply/set1P.
  apply/allP. move=>z Hzin. simpl in *.
  apply (allP (H6 x Hx y Hy) _ Hzin).
  apply H2. apply/forallP=>x. apply/implyP=>Hx.
  apply (implyP (forallP H7 _)). apply/setUP;right;apply Hx.
(*- intros. apply all_tat_triv.*)
- intros. apply all_tat_init.
- intros. by apply all_tat_disj.
Qed.

(** [all_tat] is increasing wrt. its type argument *)
Lemma all_tat_incr {p'} (t1 t2 : Dtype p') :
  all_tat t1 -> subtype t1 t2 -> all_tat t2.
Proof.
move=>Htat Hsub.
induction Hsub as [d1 d2 Hdsub|].
move=>x Hx.
destruct (dsub_subset_rev Hdsub Hx)
  as [d [Hd1 Hd2]].
move=>br Hbr.
apply (Htat d Hd1 br (subset_to_in Hbr (csub_subset Hd2))).
move=>x. by rewrite in_set0.
Qed.

(** The variable mentionned in the type at the head of the branch is 
   [v] *)
Lemma typing_v_head {p'} {ctxt : tocs p'} (v : 'I_n) (t : DDtype ctxt) (Hvt : varTyping v t):
 [forall ct in dt_get_dcb (dt t),
    [forall br in pred_of_set ct,
      [forall tocc, (nth_error br 0 == Some tocc) ==> (t_at tocc == Some (Var v))]]].
Proof.
induction Hvt.
(*apply/forallP=>x. apply/implyP. by rewrite in_set0.*)
assert (Hoccs: [forall tocc in (seq_to_enotin (occsInProgram p v) ct), (t_at (val tocc)) == (Some (Var v))]).
apply/forallP=>o. apply/implyP=>Ho. apply/eqP. apply occsInProgramV.
destruct (imsetP (mem_pset_set Ho)) as [xocc Hxoccin Hxeq].
unfold insub in Hxeq. destruct idP in Hxeq ; inversion Hxeq.
apply Hxoccin.
induction H.
apply/forallP=>x. apply/implyP. by rewrite in_set0.
apply/forallP=>x. apply/implyP. simpl.
assert (Htoccsb : [forall tocc in l, t_at (val tocc) == Some (Var v)]).
apply/forallP=>tb. apply/implyP=>Htb. apply (implyP (forallP Hoccs _)).
apply/setUP;right;apply Htb.
unfold tConj. destruct dt as [[|]].

apply (implyP (forallP (IHOccsToTypes Htoccsb) x)).
simpl. destruct (fold_type_alg DtConj typs) as [[|]]. simpl.
move=>/imsetP [y Hyin ->]. apply/forallP=>br.
apply/implyP=>/imsetP [z Hzin ->]. simpl.
apply/forallP=>tb. apply/implyP=>/eqP=>[[<-]].
apply (implyP (forallP Hoccs _)). by apply/setUP;left;apply/set1P.
move=>/imset2P [y z /imsetP [t Ht ->] Hzin ->].
apply/forallP=>br. apply/implyP=>/setUP [|].
move=>/imsetP [b Hb ->]. simpl.
apply/forallP=>tb. apply/implyP=>/eqP=>[[<-]].
apply (implyP (forallP Hoccs _)). by apply/setUP;left;apply/set1P.
move=>Hbrin.
apply (implyP (forallP (implyP (forallP (IHOccsToTypes Htoccsb) z) Hzin) _) Hbrin).
Qed.

(** Optional variable from optional term. *)
Definition term_to_var (t : option term) : option 'I_n.
destruct t as [[|]|]. apply (Some o). apply None. apply None.
Defined.

(** The size of the type list in [progPredTyping v ip pred j typs] is
   the size of the clauses with head clause symbol [pred] and such
   that the [j]eth term of the head is a variable (this is the role
    of pmap) *)
Lemma ppt_sizes {p} (ctxt : tocs p) v ip pred j (typs : seq (DDtype (p:=p) ctxt))
 (H : progPredTyping v ip pred j typs) :
     size (pmap (fun x : clause => term_to_var (nth_error (arg_atom (head_cl x)) j))
     [seq cl <- ip | hsym_cl cl == pred]) = size typs.
Proof.
induction H;auto.
simpl. destruct (bool_des_rew (hsym_cl new_cl == pred)) as [Hf|Hf].
rewrite (eqP Hf) in H0. exfalso. by apply H0.
rewrite Hf.
apply IHprogPredTyping.
simpl. rewrite eq_refl. simpl. unfold oapp. rewrite (eqP H0).
simpl. by rewrite IHprogPredTyping.
Qed.

End rules.

Structure var_type (p : program) (v : 'I_n): Type :=
  {var_typ : @Dtype p ; var_min_typ :> @DDtype p set0 ; 
   var_subtyping : subtype (val var_min_typ) var_typ  ;
   var_typing : varTyping v var_min_typ}.

Structure pred_ind_type (p : program) (v : 'I_n) (pred : symtype) (ind : 'I_max_ar): Type :=
  {pred_typ : @Dtype p ; pred_min_typ :> @DDtype p set0 ; 
   pred_subtyping : subtype (val pred_min_typ) pred_typ  ;
   pred_typing : predTyping v pred ind pred_min_typ}.

