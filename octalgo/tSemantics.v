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

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset bigop finfun.

Require Import bigop_aux.
Require Import utils.
Require Import finseqs.
Require Import fintrees.

Require Import Coq.Program.Equality.
Require Import Sumbool.

Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (s r : sub) (d def : syntax.constant) (t : term) (a : atom)
               (ga : gatom) (tl : list atom) (cl : clause) (i : interp).

Section tSemantics.

Variable p : program.
(** * Trace semantics *)
(** ** Rule grounding *)
Section rul_gr.

(** rule grounding: a pair of a clause and a substitution *)
Inductive rul_gr :=
  | RS : clause -> sub -> rul_gr.

(** Conversion to and from pair so that we have a cancellable *)
Definition rul_gr_rep l := match l with
  | RS c g => (c, g) end.

Definition rul_gr_pre l := match l with
  | (c, g) => RS c g end.

Lemma rul_gr_repK : cancel rul_gr_rep rul_gr_pre.
Proof. by case. Qed.

(** [rul_gr] is an eq type *)
Definition rul_gr_eqMixin :=
CanEqMixin rul_gr_repK.

Canonical rul_gr_eqType := Eval hnf in EqType rul_gr rul_gr_eqMixin.

(** [rul_gr] is a choice type *)
Definition rul_gr_choiceMixin :=
CanChoiceMixin rul_gr_repK.

Canonical rul_gr_choiceType := Eval hnf in ChoiceType rul_gr rul_gr_choiceMixin.

(** [rul_gr] is a count type *)
Definition rul_gr_countMixin :=
(@CanCountMixin (prod_countType clause_countType sub)
  rul_gr _ _ rul_gr_repK).

Canonical rul_gr_countType := Eval hnf in CountType rul_gr rul_gr_countMixin.

(** [rul_gr] is a finite type *)
Definition rul_gr_finMixin :=
(@CanFinMixin rul_gr_countType
  (prod_finType clause_finType sub)
  _ _ rul_gr_repK).

Canonical rul_gr_finType := Eval hnf in FinType rul_gr rul_gr_finMixin.

End rul_gr.

(** ** Semantic trees (traces) *)
Section trace_sem_trees.

Variable gat_def : gatom.

(** A semantic tree is a tree with bounded width [bn] (the maximal size of
  the body of clause),
- nodes  are in [rul_gr] ie. pairs of clause and substitution
- leaves are ground atoms (from the interpretation). *)
Definition trace_sem_trees := (@WUtree_sf rul_gr_finType gatom_finType bn gat_def).

(** force typing *)
Definition my_tst_sub x (H : wu_pred x) : trace_sem_trees := WU_sf_sub H.

(** Get the head node label (ie. the last clause and substitution) *)
Definition tst_node_head (t : trace_sem_trees) := match (val t) with
  | ABLeaf _ => None
  | ABNode h _ => Some h end.

(** Deduced term: either the fact or the head atom of the last clause grounded by the substitution. *)
Definition ded def (t : trace_sem_trees) := match (val t) with
  | ABLeaf f => f
  | ABNode (RS (Clause h _) s) _ => gr_atom_def def s h end.

(** translate a set of traces in an interpretation *)
Definition sem_tree_to_inter def (ts : {set trace_sem_trees}) : interp :=  [set ded def x | x in ts].

(** Checks that the deduction from the traces is equal to ghe atoms grounded by the supplied substitution.
  This is what is the relation existing begween the children of a trace node and the body of the clause associated to that node *)
Definition ded_sub_equal (def : syntax.constant) (lx : seq trace_sem_trees) (s : sub) (ats : seq atom)  :=
  (map (ded def) lx) == (map (gr_atom_def def s) ats).

(** Computes the traces representing the consequence of a clause
  from the traces representing the current interpretation *)
Definition cons_clause_t def (cl : clause) (k : {set trace_sem_trees}) : {set trace_sem_trees} :=
  let b := (body_cl cl) in
  let subs := match_body (sem_tree_to_inter def k) b in
  pset [set (wutree_option_fst (@wu_pcons_seq rul_gr_finType gatom_finType bn gat_def (RS cl s) lx))
                                         | lx : (size b).-tuple trace_sem_trees,
                                            s : sub in subs &
                                            (ded_sub_equal def lx s b &&
                                            all (mem k) lx)].

Set Keyed Unification.

(** A member of the consequences of the clause is an ABnode labelled by (cl, s) where s is a substitution *)
Lemma cons_clause_h def cl k (xtrace : trace_sem_trees) :
  (xtrace \in cons_clause_t def cl k) -> exists s, ABroot (val xtrace) = inl (RS cl s).
Proof.
move=> /mem_pset_set /imset2P [prevtrees s Hprevtreesin] H1.
unfold wu_pcons_seq. unfold wu_pcons_wlist.
case (sumbool_of_bool (wall (WUnotin (RS cl s)) (seq_to_wlist bn prevtrees))) => [H2|H2] H3.
- exists s. by inversion H3 as [H4].
- inversion H3.
Qed.
(** ** Trace semantics definition *)
(** Initialize the trace semantic from a standard interpretation of the
   EDB by creating leaf trees.*)
Definition base_sem_t (i : interp) : {set trace_sem_trees} :=
  [set my_tst_sub (wu_pred_leaf x) | x in i].

(** the forward chain step for the trace semantics. *)
Definition fwd_chain_t def (k : {set trace_sem_trees}) : {set trace_sem_trees} :=
  k :|: \bigcup_(cl <- p) cons_clause_t def cl k.

(** interp_t is the equivalent of interp for the trace semantics *)
Notation interp_t := {set trace_sem_trees}.

(** The m iterate of the semantics *)
Definition sem_t (def : syntax.constant) (m : nat) (i : interp) :=
  iter m (fwd_chain_t def) (base_sem_t i).

(** The leaf trees in the semantics are the ground atoms of the initial
   interpretation *)
Lemma sem_t_leaf def i ga Htra m : {| wht := ABLeaf rul_gr_finType ga; Hwht := Htra |}
              \in sem_t def m i -> ga \in i.
Proof.
induction m as [|m Hm].
by move=>/imsetP [gab Hgabin [->]].
move=>/setUP [H|H].
apply/Hm/H.
destruct (bigcup_seqP _ _ _ _ _ _ H) as [gab Hgabin Hgabeq].
destruct (andP Hgabeq) as [H1 H2].
destruct (cons_clause_h H1) as [s Hf].
inversion Hf.
Qed.

(** The result of fwd_chain contains its argument *)
Lemma fwd_chain_t_inc (it : interp_t) def : it \subset fwd_chain_t def it.
Proof. exact: subsetUl. Qed.

(** technical lemma rephrasing the above one*)
Lemma fwd_chain_t_inc_single (t : trace_sem_trees) (it : interp_t) def : (t \in it) -> t \in fwd_chain_t def it.
Proof.
move => Hin ; assert (it \subset fwd_chain_t def it). apply fwd_chain_t_inc.
apply subset_to_in with (s1 :=it) ; [apply Hin | apply H].
Qed.
(** and the same for [fwd_chain] *)
Lemma fwd_chain_inc_single ga i def : (ga \in i) -> ga \in fwd_chain def p i.
Proof.
move => H.
unfold fwd_chain.
apply/setUP.
left ; apply H.
Qed.

(**  Simple reinterpretation of definition of [ded_sub_equal] *)
Lemma ded_sub_equal_equal_to_def l tval def s : (ded_sub_equal def tval s l) = ([seq ded def i | i <- tval] == [seq gr_atom_def def s i | i <- l]).
Proof.
by destruct tval ; destruct l.
Qed.

(** Trivial technical lemma but inversion was too agressive in the following proof*)
Lemma simple_cons_eq_inversion {T : Type} (a b : T) (l ll : seq T) : (a::l = b::ll) -> (a = b /\ l = ll).
Proof.
move => H.
by inversion H.
Qed.

(** If applying s on a list l gives a list of ground atom, then using [s] as a grounding and
applying it to l will also give this list
of ground atoms. *)
Lemma stail_eq_to_gr_atom_eq (l : seq atom) (def : syntax.constant) (s : sub) (gtl : seq gatom) (H : stail l s = [seq to_atom ga | ga <- gtl]) :
  [seq gr_atom (to_gr def s) a | a <- l] = gtl.
Proof.
move:gtl H.
induction l.
- by destruct gtl.
- destruct gtl as [|g0 gtl].
  + move => //.
  + move => /= H.
    destruct (simple_cons_eq_inversion H) as [Heqh Heqtl].
    assert (H0 : gr_atom_def def s a = g0).
    - apply/gr_atom_defP/Heqh.
      rewrite <- (gr_atom_defE def s a) in H0.
      by rewrite H0 ((IHl _ Heqtl)).
Qed.

(** If applying the substitution gives ground atoms, we have [ded_sub_equal] without explicit
grounding on the list of atoms [l] *)
Lemma ded_gr_equal_stail l (gtailrec : (size l).-tuple trace_sem_trees) def s gtl :
  ([seq ded def i | i <- gtailrec] = gtl) -> (stail l s = [seq to_atom ga | ga <- gtl]) -> ded_sub_equal def gtailrec s l.
Proof.
unfold ded_sub_equal.
move =>-> /stail_eq_to_gr_atom_eq H.
rewrite -(H def);apply/eqP. clear gtailrec. clear H.
induction l as [|h l Hl];auto. simpl.
apply/f_equal2.
simpl. by rewrite (gr_atom_defE def s).
apply Hl.
Qed.

(** There is no new leaf in the consequence of a
    clause *)
Lemma no_deduced_leaf (x : gatom_finType) (def : syntax.constant) (k : {set trace_sem_trees})
(Habs : wutree_fin (wu_leaf x) \in \bigcup_cl cons_clause_t def cl k) : False.
Proof.
destruct (bigcupP Habs) as [cl Htriv Hin].
destruct ((imset2P (mem_pset_set Hin))) as [decs sub Hindecs Hsubin Heq].
unfold wu_pcons_seq in Heq.
unfold wu_pcons_wlist in Heq.
destruct Sumbool.sumbool_of_bool in Heq ; inversion Heq.
Qed.

Lemma cons_clause_t_desc def (deduced : {set [finType of trace_sem_trees]}) (h : rul_gr_finType) (l : seq (@ABtree rul_gr_finType gatom_finType))
      (t : trace_sem_trees) (Hin : val t \in l)
      (Hwup : @wu_pred _ _ bn (ABNode h l)) : (my_tst_sub Hwup
           \in \big[setU (T:=[finType of trace_sem_trees])/set0]_cl
                  cons_clause_t def cl deduced) -> t \in deduced.
Proof.
move => /(@bigcupP [finType of trace_sem_trees] clause_finType _ _ _) Hcons.
unfold mem.
destruct Hcons as [acl Htriv Hhlin].
unfold mem in Hhlin.
destruct (@imset2P (tuple_finType (size (body_cl acl)) [finType of trace_sem_trees]) _ _ _ _ _ _ (mem_pset_set Hhlin)) as [lx s Hlxin H Heq].
unfold wu_pcons_seq in Heq. unfold wu_pcons_wlist in Heq.
destruct Sumbool.sumbool_of_bool as [Hclnotin | Hclin] in Heq.
- inversion Heq as [[Hheq Hleq]]. rewrite seq_wlistK in Hleq.
  + rewrite in_set in H. destruct (andP H) as [Hsmatch Hb]. destruct (andP Hb) as [Hdedeq Hall].
    unfold all in Hall.
    apply (allP Hall).
    destruct t as [t Ht].
    destruct (all_prop_in (@sub_val_map _ _ trace_sem_trees l lx Hleq) Hin) as [tval Hinbis].
    simpl in Hinbis. unfold WU_sf_sub in Hinbis.
    assert (Hproofseq : tval = Ht). apply eq_irrelevance.
    rewrite <- Hproofseq.
    unfold mem. unfold in_mem. simpl. destruct lx as [lx Hlx].
    simpl. simpl in Hinbis.
    clear Hwup Hhlin Hlxin Hclnotin Heq Hheq Hleq H Hsmatch Hb Hdedeq Hall Hlx.
    (* quite ugly, but avoids dependent types shenanigan *)
    (* my guess would be that some properties of canonicals do not
       automatically lift to seqs *)
    induction lx.
    - by simpl in Hinbis.
    - simpl. simpl in IHlx. simpl in Hinbis. destruct (orP Hinbis) as [Hta | Htl].
      + rewrite (eqP Hta). by apply/orP ; left.
      + apply/orP ; right ; apply/IHlx/Htl.
  + destruct lx as [lx Hlx].
    simpl ; rewrite (eqP Hlx). apply wlist_to_seq_size.
- inversion Heq.
Qed.

(** If a tree is in a given step of the trace semantic, so are all its subtrees. *)
Lemma trace_sem_prev_trees nb_iter def init :
   forall (t1 t2 : trace_sem_trees), t2 \in (sem_t def nb_iter init)
-> subtree (val t1) (val t2) -> t1 \in (sem_t def nb_iter init).
Proof.
induction nb_iter as [|nb_iter Hit].
- move => t1 t2 Ht2sem Hsub.
  destruct (imsetP Ht2sem) as [t2_atom Ht2_ain Ht2_eq].
  rewrite Ht2_eq in Hsub.
  simpl in Hsub.
  apply/imsetP.
  exists t2_atom.
  + apply Ht2_ain.
  + apply/eqP.
    by rewrite <- (@inj_eq [finType of trace_sem_trees] (@ABtree_eqType _ _) _ val_inj).
- move => t1 t2 Ht2sem Hsub.
  unfold fwd_chain_t.
  unfold fwd_chain_t in Ht2sem.
  destruct (setUP Ht2sem) as [Ht2old | Ht2new].
  + (* t2 was already in deduced, using induction hyp *)
    apply/setUP ; left.
    apply (Hit t1 t2 Ht2old Hsub).
  + (* t2 was just deduced. 2 cases : t1 = t2 or t1 stricly smaller *)
    destruct t2 as [t2 Ht2wu].
    destruct t2.
    - (* leaf in cons_clause_t: absurd *)
      exfalso.
      apply no_deduced_leaf with (x := s) (def := def) (k := (sem_t def nb_iter init)).
      assert (Heq : Wht Ht2wu == (wu_leaf s)).
      + by rewrite <- inj_eq with (f := val) ; [ | apply val_inj].
      rewrite <- (eqP Heq). apply (@bigcup_type_seq _ _ (fun cl => cons_clause_t def cl (sem_t def nb_iter init)) _ p Ht2new).
    - (* we can now compute subtree *)
      destruct (orP Hsub) as [Ht1t2abeq | Ht1ssubt2].
      + (* t1 = t2 *)
        assert (Ht1t2eq : t1 == Wht Ht2wu).
        (* tain, faut vraiment une tactique pour ça ... *)
        destruct t1 as [t1 Ht1].
        rewrite <- (@inj_eq _ (@ABtree_eqType _ _) val val_inj).
        simpl. simpl. simpl in Ht1t2abeq. by rewrite (eqP Ht1t2abeq).
        by rewrite (eqP Ht1t2eq).
      + (* t1 strict subtree of t2 *)
        apply/setUP ; left.
        fold (@subtree rul_gr_finType gatom_finType) in Ht1ssubt2.
        destruct (hasP Ht1ssubt2) as [desc Hdescl Hsubdesc].
        pose Hwupredl := wu_pred_descs Ht2wu.
        pose Hwupredpred := allP Hwupredl _ Hdescl.
        pose Hwupredinded := @cons_clause_t_desc def (sem_t def nb_iter init) s l (Wht Hwupredpred) Hdescl Ht2wu.
        apply/(Hit t1 (Wht Hwupredpred)). apply (Hwupredinded (bigcup_type_seq Ht2new)). apply Hsubdesc.
Qed.

(** If a tree is in a given step of the trace semantic, its strict
 subtrees are in the previous step. *)
Lemma trace_sem_prev_trees_m1 nb_iter def init :
   forall (t1 t2 : trace_sem_trees), t2 \in (sem_t def nb_iter init)
-> strict_subtree (val t1) (val t2) -> t1 \in (sem_t def nb_iter.-1 init).
Proof.
induction nb_iter as [|nb_iter Hit].
- by move => t1 t2 /imsetP [ga Hgain ->] /=.
- move => t1 t2 Hsemt Hss. pose Hsemt_cop := Hsemt. clearbody Hsemt_cop.
  pose Hss_cop := Hss. clearbody Hss_cop. move:Hss. move:Hsemt.
  move=> /setUP [Hrec|]. move=>Hsub.
  destruct nb_iter;simpl. destruct (imsetP Hrec) as [ga Hga Heq]. apply/imsetP.
  exists ga;auto. rewrite Heq in Hsub. inversion Hsub.
  apply/setUP;left. by apply Hit with (t2 := t2).

  move=>/bigcup_seqP [cl Hclin /andP [/imsetP [t]]]. rewrite mem_pmap.
  move=>/mapP [to /mapP [too]]. rewrite mem_enum.
  move=>/imset2P [descs sb Hdescsin]. rewrite in_set.
  move=>/andP [Hsbmatch /andP [Hded Hall] -> ->].
  unfold wu_pcons_seq. unfold wu_pcons_wlist.
  destruct Sumbool.sumbool_of_bool;move=>// [->] Ht2eq.
  rewrite Ht2eq. rewrite Ht2eq in Hsemt_cop.
  move=>Htriv /=. rewrite seq_wlistK. move=>/hasP [t15 H15in Hsub].
  assert (Hwu : @wu_pred _ _ bn t15).
  apply (@wu_pred_sub _ _ _ _ (val t2)). rewrite Ht2eq. apply/orP;right. apply/hasP.
  exists t15. rewrite seq_wlistK. apply H15in. destruct descs. rewrite (eqP i).
  apply wlist_to_seq_size. destruct t15. auto. by apply/orP;left.
  rewrite Ht2eq. simpl. apply (wu_merge
                  (wu_cons_uniq (x:=RS cl sb) (tl:=wlist_to_seq (seq_to_wlist bn descs)) (wall_to_all e))
                  (ABwidth_cons (RS cl sb) (tl:=[seq wht i | i <- wlist_to_seq (seq_to_wlist bn descs)])
                     (size_map_leq (wlist_to_seq_size (seq_to_wlist bn descs)))
                     (wu_list_width (wlist_to_seq (seq_to_wlist bn descs))))).
  destruct (mapP H15in) as [t15d H15din H15teq]. clear H15in. destruct descs as [descs Hdescs].
   simpl in Hall. simpl in H15din. destruct t1 as [t1 Ht1]. simpl in *.
  destruct t15.
  assert (Ht1eq : {| wht := t1; Hwht := Ht1 |} = {|wht := (ABLeaf rul_gr_eqType g); Hwht := wu_pred_leaf g|}).
  apply/val_inj. simpl in Hsub. simpl. by rewrite (eqP Hsub).
  rewrite Ht1eq. destruct t15d as [t15d H15d].
  assert (Ht1eqb : {| wht := ABLeaf rul_gr_eqType g; Hwht := wu_pred_leaf g |}  = {| wht := t15d; Hwht := H15d |}).
  apply/val_inj. simpl. by rewrite H15teq. rewrite Ht1eqb.
  apply (allP Hall {| wht := t15d; Hwht := H15d |} H15din).
  destruct (orP Hsub) as [Heq|Hsss].
  assert (Ht1eq : {| wht := t1; Hwht := Ht1 |} = t15d).
  apply/val_inj. simpl in Hsub. simpl. by rewrite (eqP Heq).
  rewrite Ht1eq. destruct t15d as [t15d H15d].
  apply (allP Hall {| wht := t15d; Hwht := H15d |} H15din).
  destruct (hasP Hsss) as [trt Htrtin Htsub]. clear Hsss.
  assert (Htrt: @wu_pred _ _ bn trt).
  destruct t15d as [t15d Ht15d].
  apply wu_pred_sub with (t4 := t15d). simpl in H15teq. rewrite -H15teq.
  apply/orP. right. apply/hasP. exists trt;auto. apply subtree_refl.
  apply Ht15d.
  pose Hprev := (allP Hall t15d H15din). clearbody Hprev.
  apply (trace_sem_prev_trees Hprev). simpl. rewrite -H15teq.
  simpl. apply/orP;right. apply/hasP. exists trt. apply Htrtin.
  apply Htsub. destruct descs as [azer Ht]. simpl. rewrite (eqP Ht).
  apply wlist_to_seq_size.
Qed.

(** ** Completeness of the trace semantic.
  For each atom in the regular semantic, there is a tree in the
  trace semantic that can be interpreted (it deduces) the atom *)
Lemma trace_sem_completeness nb_iter def i :
  prog_safe p -> [forall x in (sem p def nb_iter i), exists y in (sem_t def nb_iter i), ded def y == x].
Proof.
induction nb_iter as [|nb_iter Hit] ;
move=> Hsafe ; apply/forallP ; move => x ; apply/implyP ; move => Hin ; apply/existsP.
- by exists (wu_leaf x) ; apply/andP ; split ; [apply mem_imset | ].
- destruct (setUP Hin).
  + destruct (existsP (implyP (forallP (Hit Hsafe) x) H)) as [x0 Hx0].
    exists x0 ; apply/andP ; split ; [apply (fwd_chain_t_inc_single _ (bool_to_prop_l Hx0)) | apply (bool_to_prop_r Hx0)].
  + rewrite bigcup_seq in H.
    clear Hin.
    destruct (bigcupP H) as [cl Hin Hxsub].
    destruct (imsetP Hxsub) as [s Hsded Hstail].
    destruct (match_tl_sound Hsded) as [gtl Htailseq Hall].
    destruct cl as [h l].
    simpl in Hstail ; simpl in Htailseq ; simpl in Hsded.
    assert (Hgtailrec : exists gtailrec : (size l).-tuple trace_sem_trees,
        map (ded def) gtailrec = gtl /\ all (mem (sem_t def nb_iter i)) gtailrec).
    + pose Hb := (stail_eq_to_gr_atom_eq def Htailseq).
      rewrite <- Hb.
      clear Hin Hsded Hxsub.
      move : l Hstail Htailseq Hb.
      move => l. apply (@wlist_ind _ bn) with (u := l). clear l.
      induction gtl.
      - move => s0 Ps Hstail Htailseq Hb.
        destruct s0.
        + unfold seq_to_wlist_uncut. rewrite seq_to_bnil. by exists [tuple].
        + unfold wlist_to_seq_co in Hb. rewrite seq_wlist_uncut_K in Hb.
          inversion Hb.
      - move => s0 Ps Hstail Htailseq Hb.
        destruct s0 ; unfold wlist_to_seq_co in Hb ; rewrite seq_wlist_uncut_K in Hb.
        + inversion Hb.
        + inversion Hb.
          destruct (existsP (implyP (forallP (Hit Hsafe) a) (bool_to_prop_l Hall))) as [abis Habis].
          unfold wlist_to_seq_co in Htailseq ; rewrite seq_wlist_uncut_K in Htailseq.
          unfold wlist_to_seq_co ; rewrite seq_wlist_uncut_K.
          assert (Ps1 : size s1 <= bn). apply leq_trans with (n := (size s1).+1). auto. apply Ps.
          assert (Hegtl : exists gtailrec : (size (seq_to_wlist_uncut Ps1)).-tuple trace_sem_trees,
                          [seq ded def i | i <- gtailrec] = [seq gr_atom (to_gr def s) a | a <- seq_to_wlist_uncut Ps1]
                              /\ all (mem (sem_t def nb_iter i)) gtailrec).
          - assert (Hstails1 : stail (seq_to_wlist_uncut Ps1) s = [seq to_atom ga | ga <- gtl]).
            unfold wlist_to_seq_co ; rewrite seq_wlist_uncut_K. apply (simple_cons_eq_inversion Htailseq).
            assert (H8bis : ([seq gr_atom (to_gr def s) a | a <- seq_to_wlist_uncut Ps1] = gtl)).
            unfold wlist_to_seq_co ; rewrite seq_wlist_uncut_K. auto.
            apply (IHgtl (bool_to_prop_r Hall) s1 Ps1 Hstail Hstails1 H8bis).

          unfold wlist_to_seq_co in Hegtl ; rewrite seq_wlist_uncut_K in Hegtl.
          destruct Hegtl as [gtailrec [Hgtlrecded Hgtlrcall]].
          by exists [tuple of (abis :: gtailrec)] ; split ; simpl ;
             [rewrite Hgtlrecded (eqP (bool_to_prop_r Habis)) ; inversion Hb
            | apply/andP ; split ; [apply (bool_to_prop_l Habis) |apply Hgtlrcall]].
    inversion Hgtailrec as [gtailrec [Hdedprev Hindeduced0]].
    (*pose cl := {| ssval := Clause h l; ssvalP := Hclpclause |}.*)
    pose cl := Clause h l.
    pose tl := (seq_to_wlist bn gtailrec).
    destruct (Sumbool.sumbool_of_bool (@wall trace_sem_trees bn (WUnotin (RS cl s)) tl)) as [Hprev | Hnotprev_wlist].
    + exists (@wu_cons_wlist _ _ bn gat_def (RS cl s) tl Hprev).
      apply/andP ; split.
      - apply/setUP ; right ; rewrite bigcup_seq ; apply/bigcupP.
        exists cl.
        - apply Hin.
        - unfold fwd_chain_t ; unfold cons_clause_t ; unfold wu_pcons_seq ; unfold wu_pcons_wlist.
          apply/mem_set_pset/imset2P.
          apply Imset2spec with (x1 := gtailrec) (x2 := s).
          + auto.
          + apply/setIdP ; split.
            - apply subset_to_in with (s1 := match_body (sem p def nb_iter i) (body_cl (Clause h l))).
              + auto.
              + apply match_body_incr ; apply/subsetP ; move => y Hy.
                destruct (existsP (implyP (forallP (Hit Hsafe) y) Hy)) as [xy Hxy].
                apply/imsetP.
                exists xy.
                - apply (bool_to_prop_l Hxy).
                - apply/eqP. rewrite eq_sym. apply (bool_to_prop_r Hxy).
            - apply/andP ; split.
              + by apply ded_gr_equal_stail with (gtl := gtl).
              + apply Hindeduced0.
            (* Very unelegant... *)
          + destruct Sumbool.sumbool_of_bool as [Hprevbis | Hprevcontr].
            - by rewrite (eq_irrelevance Hprev Hprevbis).
            - by rewrite Hprev in Hprevcontr.
      - by rewrite Hstail ; apply/eqP.
    + rewrite wall_allK in Hnotprev_wlist.
      assert (Hnot_prev : ~~ @all trace_sem_trees (WUnotin (RS cl s)) (wlist_to_seq tl)).
      - by rewrite Hnotprev_wlist.
      clear Hnotprev_wlist.
      rewrite <- has_predC in Hnot_prev.
      (* The tree in tl (previous traces) that was built upon the needed one *)
      destruct (hasP Hnot_prev) as [tsup Htsupintl Hclinsupnegneg].
      unfold mem in Htsupintl.
      unfold WUnotin in Hclinsupnegneg. unfold ABnotin in Hclinsupnegneg.
      pose Hclinsup := negPn Hclinsupnegneg.
      destruct (ABin_extract Hclinsup) as [prevocc Hposub Hporooteq].
      destruct tsup as [tsup Hwutsup].
      pose Hwupo := wu_pred_sub Hposub Hwutsup.
      exists (Wht Hwupo). apply/andP ; split.
      - apply/setUP ; left. apply trace_sem_prev_trees with (t2 := (Wht Hwutsup)).
        + apply (allP Hindeduced0).
          unfold tl in Htsupintl.
          rewrite seq_wlist_uncut_K in Htsupintl.
          - unfold mem. unfold mem in Htsupintl. unfold trace_sem_trees.
            simpl. simpl in Htsupintl. unfold in_mem in Htsupintl. simpl in Htsupintl.
            unfold in_mem ; simpl.
            destruct gtailrec as [gtailrec Htlr].
            simpl. simpl in Htsupintl. simpl in tl.
            clear Hgtailrec Hdedprev Hindeduced0 Hnot_prev Hclinsupnegneg Hclinsup Hwupo Hposub Hporooteq Htlr.
            (* cf. cons_clause_t_desc *)
            induction gtailrec.
            + by simpl in Htsupintl.
            + simpl in Htsupintl ; simpl ; simpl in IHgtailrec.
              destruct (orP Htsupintl) as [Htsupa | Htsupl].
              - by rewrite (eqP Htsupa) ; apply/orP ; left.
              - apply/orP ; right ; apply/IHgtailrec/Htsupl.
          - destruct gtailrec as [gtlrec Hgtlrec]. rewrite (eqP Hgtlrec). apply wlist_to_seq_size.
        + apply Hposub.
      - rewrite Hstail.
        dependent destruction prevocc ; inversion Hporooteq.
        inversion Hporooteq. unfold ded. simpl. by rewrite H1.
Qed.

(** ** Soundness of the trace semantics *)
(** technical lemma *)
Lemma type_preserving_inversion (A B C : finType) (f2 : A -> B -> C)
(D1 : mem_pred A) (D2 : A -> mem_pred B)
: forall y : C, imset2_spec f2 D1 D2 y-> (exists x1 : A, exists x2 : B, (in_mem x1 D1 /\ in_mem x2 (D2 x1) /\ (y = f2 x1 x2))).
Proof.
move => y im2spec.
inversion im2spec.
exists x1.
exists x2.
move => //.
Qed.

(** technical lemma: unification failed with normal setIdP *)
Lemma setIdP_bool_to_prop {T : finType} (pA pB : pred T) : forall x, x \in [set y | pA y & pB y] -> ((pA x) /\ (pB x)).
Proof.
move => x Hx.
apply/setIdP/Hx.
Qed.

(** For all trace in the m step of the trace semantic, its deduced atom is
  in the m step of the regular semantics *)
Lemma trace_sem_soundness nb_iter def i:
  prog_safe p -> [forall t in (sem_t def nb_iter i), ded def t \in (sem p def nb_iter i)].
Proof.
move=> Hsafe.
induction nb_iter as [|nb_iter Hit];
apply/forallP ; move => t ; apply/implyP ; move => Hin.
- destruct (imsetP Hin) as [x Hxi Hxeq].
  by destruct t ; rewrite Hxeq.
- destruct (setUP Hin) as [Hprev | Hjded].
  + by apply/fwd_chain_inc_single/((implyP (forallP Hit t))).
  + apply subset_to_in with (s1 := \bigcup_(cl <- p) cons_clause def cl (sem p def nb_iter i)).
    - rewrite bigcup_seq.
      rewrite bigcup_seq in Hjded.
      destruct (bigcupP Hjded) as [pcl Hxpcl Hpclcons].
      clear Hjded.
      apply/bigcupP.
      exists pcl.
      + apply Hxpcl.
      + destruct (type_preserving_inversion (imset2P (mem_pset_set Hpclcons))) as [ls [s [Htriv [Hsubmatch Ht]]]].
        destruct (setIdP_bool_to_prop Hsubmatch) as [Hsmatch Hdedall].
        apply/imsetP.
        exists s.
        - apply subset_to_in with (s1 := match_body (sem_tree_to_inter def (sem_t def nb_iter i)) (body_cl pcl)).
          + apply Hsmatch.
          + apply/match_body_incr/subsetP.
            move => ga Hga.
            unfold sem_tree_to_inter in Hga.
            destruct (imsetP Hga) as [pre_ga Hpre_ga_ded H_ga_ded].
            rewrite H_ga_ded.
            by apply (implyP (forallP Hit pre_ga)).
        - unfold wu_pcons_seq in Ht. unfold wu_pcons_wlist in Ht. destruct Sumbool.sumbool_of_bool as [Heq | Habs] in Ht.
          + inversion Ht as [Hrt]. unfold ded. simpl. by destruct pcl.
            destruct pcl as [ppcl]. by destruct ppcl.
    - apply subsetUr.
Qed.

(** If we have a node in the trace semantics with [(cl, s)] as root, then there is an interpretation where the body of [cl] matches
producing [s]. *)
Lemma trace_sem_head_match def cl s l m i Htr :
   prog_safe p
-> {| wht := ABNode (RS cl s) l; Hwht := Htr |} \in sem_t def m i
-> [exists i' : interp, ((s \in match_body i' (body_cl cl)))].
Proof.
move:cl s l i Htr.
induction m as [|m Hm].
move=>/= cl s l i Htr psafe /imsetP [ga Hgain [Hgaeq]].
inversion Hgaeq.
move=> /= cl s l i Htr psafe.
unfold fwd_chain_t.
move=>/setUP [Hrec|Hnew].
by apply (@Hm cl s l i Htr).
destruct (bigcup_seqP _ _ _ _ _ _ Hnew)
  as [clb Hclbin Hclbcons]. clear Hnew.
destruct (andP Hclbcons) as [Hclbconsb Htriv]. clear Hclbcons. clear Htriv.
move:Hclbconsb. move=> /mem_pset_set /imset2P [prev_trees sb Hprevsin Hsub Htreeeq].
move:Hsub. rewrite in_set. move=>/andP [Hmatch /andP [Hprev Hininterp]].
unfold wu_pcons_seq in Htreeeq. unfold wu_pcons_wlist in Htreeeq.
destruct Sumbool.sumbool_of_bool in Htreeeq; [|inversion Htreeeq].
inversion Htreeeq as [[Hcleq Hseq Hleq]].
apply/existsP. exists (sem_tree_to_inter def (sem_t def m i)). apply Hmatch.
Qed.

(** technical lemma *)
Lemma sterm_ga_eq def s aa aga :
   [seq sterm s x | x <- aa ] = [seq Val x | x <- aga]
-> aga = [seq gr_term_def def s i | i <- aa].
Proof.
move=>H. apply Logic.eq_sym. rewrite -(@map_id _ aga). move:H.
apply map_square_eq. move=>x y. apply gr_term_defP.
Qed.

(** technical lemma *)
Lemma stail_ded_eq cl s gtl def :
stail (body_cl cl) s = [seq to_atom ga | ga <- gtl]
-> [seq gr_atom_def def s i | i <- body_cl cl] = 
   [seq ded def i | i <- [seq my_tst_sub (x:=ABLeaf rul_gr x) (wu_pred_leaf x) | x <- gtl]].
Proof.
rewrite -map_comp.
apply map_square_eq.
move=>x y /gr_atom_defP H. by rewrite (H def).
Qed.

(** technical lemma *)
Lemma all_mem_edb_tst gtl (i : interp) :
  all (mem i) gtl ->
 all (mem [set my_tst_sub (x:=ABLeaf rul_gr x) (wu_pred_leaf x) | x in i])
  [seq my_tst_sub (x:=ABLeaf rul_gr_finType x) (wu_pred_leaf x) | x <- gtl].
Proof.
move=>/allP H. apply/allP=>x /mapP [ga Hga ->].
apply/imsetP. exists ga. apply/H/Hga.
reflexivity.
Qed.

(** Let [p] be safe, forall clause [cl] of [p],
   and substitution [s] result of matching [cl]
against the standard semantics of [p] at step
[m], then there is a trace [t] in the (m+1)
trace-semantics of [p] whose head is [(cl,s)] *)
Lemma trace_sem_completeness_b def m i: prog_safe p ->
[forall cl:clause in p, [forall s:sub in match_body (sem p def m i) (body_cl cl),
  [exists t in sem_t def m.+1 i, (tst_node_head t) == Some (RS cl s)]]].
Proof.
move=>Hpsafe.
induction m as [|m Hm].
- apply/forallP=>cl. apply/implyP=>Hclin. apply/forallP=>s. apply/implyP=>/= Hsmatch.
  destruct (match_tl_sound Hsmatch) as [gtl Hgtleq Hallgtlin].
  pose sgtl := map (fun x => my_tst_sub (x:=ABLeaf rul_gr_finType x) (wu_pred_leaf x)) gtl.
  assert (Hsize : size sgtl = size (body_cl cl)).
  + unfold sgtl. rewrite size_map.  unfold stail in Hgtleq.
    rewrite -(@size_map _ _ (fun x => satom x s)) -(@size_map _ _ to_atom). by apply/f_equal.
  destruct (Sumbool.sumbool_of_bool (wall (WUnotin (RS cl s)) (seq_to_wlist bn sgtl)))
    as [Hnotprevin|Hprevin].
  + apply/existsP.
    exists (@wu_cons_wlist _ _ bn gat_def (RS cl s) (seq_to_wlist bn sgtl) Hnotprevin).
    apply/andP;split.
    unfold fwd_chain_t. apply/setUP;right. apply/bigcup_seqP.
    exists cl. apply/Hclin. apply/andP;split;auto.
    unfold base_sem_t.
    apply/mem_set_pset/imset2P. rewrite -Hsize.
    exists (in_tuple sgtl) s;auto.
    rewrite in_set. apply/andP;split. simpl.
    assert (Hieq : (sem_tree_to_inter def [set my_tst_sub (x:=ABLeaf rul_gr x) (wu_pred_leaf x) | x in i]) = i).
    - unfold sem_tree_to_inter. apply/eqP. rewrite eqEsubset;apply/andP;split;apply/subsetP.
      + move=>y /imsetP [z] /imsetP [ga Hgain ->] ->. apply Hgain.
      + move=>y Hyin. apply/imsetP. exists (my_tst_sub (x:=ABLeaf rul_gr y) (wu_pred_leaf y)).
        apply/imsetP. exists y. apply Hyin. auto. auto.
    by rewrite Hieq.
    apply/andP;split. unfold ded_sub_equal. unfold sgtl. 
    apply/eqP/Logic.eq_sym/stail_ded_eq/Hgtleq.
    simpl. apply/all_mem_edb_tst/Hallgtlin. unfold wu_pcons_seq. unfold wu_pcons_wlist.
    destruct (Sumbool.sumbool_of_bool)
      as [Ht|Hf]; [|by exfalso; rewrite Hf in Hnotprevin].
    by apply/f_equal/f_equal/val_inj. auto.
  + rewrite wall_allK seq_wlist_uncut_K in Hprevin.
    assert (Hnot_prev : ~~ @all trace_sem_trees (WUnotin (RS cl s)) (in_tuple sgtl)).
    - by rewrite Hprevin.
    clear Hprevin.
    rewrite <- has_predC in Hnot_prev.
    destruct (hasP Hnot_prev) as [tsup Htsupintl Hclinsupnegneg]. clear Hnot_prev.
    unfold WUnotin in Hclinsupnegneg. unfold ABnotin in Hclinsupnegneg. unfold predC in Hclinsupnegneg.
    simpl in Hclinsupnegneg. rewrite Bool.negb_involutive in Hclinsupnegneg.
    unfold ABin in Hclinsupnegneg.
    destruct (ABin_extract Hclinsupnegneg) as [ptr Hsub Hroot].
    unfold sgtl in Htsupintl.
    destruct (mapP Htsupintl) as [ga Hgain Htsupeq].
    rewrite Htsupeq in Hsub. simpl in Hsub.
    destruct ptr. inversion Hroot. move: Hsub =>/eqP //.
  + destruct cl as [h tl]. simpl. unfold tail in tl. rewrite Hsize.
    apply wlist_to_seq_size.
- apply/forallP=>cl. apply/implyP=>Hclin. apply/forallP=>s. apply/implyP=>/= Hsmatch.
  unfold fwd_chain in Hsmatch.
  destruct (match_tl_sound Hsmatch) as [gtl Hgtleq Hallgtlin].
  assert (Hall : all (fun ga=> [exists tr:trace_sem_trees ,
                        (tr \in sem_t def m.+1 i) && (ded def tr == ga)]) gtl).
  apply/allP. move=>ga Hga. destruct (setUP (allP Hallgtlin ga Hga)) as [Hgain|Hgain].
  + destruct (existsP (implyP (forallP (trace_sem_completeness m def i Hpsafe) ga) Hgain))
      as [tr Htr]. destruct (andP Htr) as [H1 H2]. clear Htr.
    apply/existsP. exists tr. apply/andP;split;auto.
    by apply/setUP;left.
  + destruct (bigcup_seqP _ _ _ _ _ _ Hgain) as [clb Hclbin Hclb].
    destruct (andP Hclb) as [H1 H2]. clear H2.
    destruct (imsetP H1) as [sb Hsbin ->].
    destruct (existsP (implyP (forallP (implyP (forallP Hm clb) Hclbin) sb) Hsbin)) as [tr Htr].
    destruct (andP Htr) as [H2 H3].
    apply/existsP. exists tr. apply/andP;split;auto. move:H3. destruct tr as [[] H5]; move=>/eqP [H3].
    inversion H3. unfold ded. simpl. rewrite H3. by destruct clb.
  destruct (all_exist_seq Hall) as [trs Htrs]. destruct (andP Htrs) as [Htrsin Htrseq]. clear Htrs.
  assert (Hsizeb : size gtl = size (body_cl cl)).
  rewrite -(@size_map _ _ to_atom). rewrite -(@size_map _ _ (fun x => satom x s) (body_cl cl)). by apply/f_equal.
  assert (Hsize : size (map snd trs) = size (body_cl cl)).
  by rewrite -Hsizeb -(eqP Htrsin) !size_map.
  destruct (Sumbool.sumbool_of_bool (wall (WUnotin (RS cl s)) (seq_to_wlist bn (map snd trs))))
    as [Hnotprevin|Hprevin].
  + apply/existsP.
    exists (@wu_cons_wlist _ _ bn gat_def (RS cl s) (seq_to_wlist bn (map snd trs)) Hnotprevin).
    apply/andP;split.
    unfold fwd_chain_t. apply/setUP;right. apply/bigcup_seqP.
    exists cl. apply/Hclin. apply/andP;split;auto.
    apply/mem_set_pset/imset2P. rewrite -Hsize.
    exists (in_tuple (map snd trs)) s;auto.
    rewrite in_set. apply/andP;split. simpl.
    assert (H : (sem p def m i
                   :|: \big[setU (T:=gatom_finType)/set0]_(cl <- p) cons_clause def cl (sem p def m i))
                \subset (sem_tree_to_inter def
           (sem_t def m i
            :|: \big[setU (T:=wutree_finType)/set0]_(cl0 <- p) cons_clause_t def cl0 (sem_t def m i)))).
    apply/subsetP. move=>y /setUP [Hy|Hy];apply/imsetP.
    destruct (existsP (implyP (forallP (trace_sem_completeness m def i Hpsafe) y) Hy))
      as [tr Htr]. destruct (andP Htr) as [Htr1 Htr2].
    exists tr. apply/setUP;left;auto. by rewrite (eqP Htr2).
    destruct (bigcup_seqP _ _ _ _ _ _ Hy) as [clb Hclbin Hclb]. destruct (andP Hclb) as [Hclbb Htriv].
    destruct (imsetP Hclbb) as [sb Hsbin Hsbeq].
    destruct (existsP (implyP (forallP (implyP (forallP Hm clb) Hclbin) sb) Hsbin))
      as [tr Htr]. destruct (andP Htr) as [Htr1 Htr2].
    exists tr.  apply Htr1. rewrite Hsbeq. unfold tst_node_head in Htr2. unfold ded.
    destruct tr as [[] Htrt]; pose Hf := eqP Htr2; inversion Hf as [Hff]. simpl in *.
    rewrite Hff. by destruct clb as [hclb tlclb].
    apply (subsetP (match_body_incr cl H) s Hsmatch).
    apply/andP;split. unfold ded_sub_equal.
    clear Hm. clear Hsmatch. clear Hallgtlin. clear Hsizeb. clear Hsize. clear Hnotprevin.
    clear Hclin. move:Hgtleq.
    destruct cl as [hcl tcl]. simpl. apply (@wlist_ind _ bn) with (u := tcl).
    unfold wlist_to_seq_co. move=> l Pl. rewrite seq_wlist_uncut_K. clear tcl. clear Pl.
    move:l trs Hall Htrsin Htrseq. induction gtl as [|gh gtl Hgtl];move=>[|hl tll];move=>[|htrs tltrs] //=.
    move=>/andP [H1 H2] /andP [H31 H32] /andP [H4 H5] [H6 H7] H8.
    assert (Hrew : ded def htrs.2 = gr_atom_def def s hl). destruct htrs as [ga [[gab|[clb sb]] Htr]];
    simpl in *. destruct (andP H4) as [H9 H10]. rewrite (eqP H10).
      destruct hl as [[phl ahl] Hhl]. unfold gr_atom_def. rewrite (eqP H31).
    destruct gh as [[pga aga] Hga]. apply/val_inj. simpl in *. unfold gr_raw_atom_def.
    rewrite H6. apply/f_equal. simpl. apply/sterm_ga_eq/H7. destruct (andP H4) as [H41 H42].
    rewrite (eqP H42) (eqP H31). destruct gh as [[pgh agh] Hgh]; destruct hl as [[phl ahl] Hhl];
    apply/val_inj. simpl in *. unfold gr_raw_atom_def. simpl. rewrite H6. apply/f_equal.
    apply/sterm_ga_eq/H7.
    rewrite Hrew. apply/eqP/f_equal. apply/eqP/Hgtl;auto.
    apply/allP. move=>x Hx.
    destruct (mapP Hx) as [[v vtr] Hvtrin Hvtreq].
    destruct (andP (allP Htrseq (v, vtr) Hvtrin)) as [Hvtrsem Hvtrded].
    simpl in *. rewrite -Hvtreq in Hvtrsem. apply Hvtrsem.
    unfold wu_pcons_seq. unfold wu_pcons_wlist.
    destruct (Sumbool.sumbool_of_bool)
      as [Ht|Hf]; [|by exfalso; rewrite Hf in Hnotprevin].
    by apply/f_equal/f_equal/val_inj. auto.
  + rewrite wall_allK seq_wlist_uncut_K in Hprevin.
    assert (Hnot_prev : ~~ @all trace_sem_trees (WUnotin (RS cl s)) (in_tuple (map snd trs))).
    - by rewrite Hprevin.
    clear Hprevin.
    rewrite <- has_predC in Hnot_prev.
    destruct (hasP Hnot_prev) as [tsup Htsupintl Hclinsupnegneg]. clear Hnot_prev.
    unfold WUnotin in Hclinsupnegneg. unfold ABnotin in Hclinsupnegneg. unfold predC in Hclinsupnegneg.
    simpl in Hclinsupnegneg. rewrite Bool.negb_involutive in Hclinsupnegneg.
    destruct (ABin_extract Hclinsupnegneg) as [ptr Hsub Hroot].
    apply/existsP. destruct tsup as [tsup Htsup].
    exists {|wht := ptr ; Hwht := (wu_pred_sub Hsub Htsup)|}. apply/andP;split.
    unfold fwd_chain_t. apply/setUP;left.
    destruct (mapP Htsupintl) as [[v vtr] Hvtrin Hvtreq].
    destruct (andP (allP Htrseq (v, vtr) Hvtrin)) as [Hvtrsem Hvtrded].
    simpl in *. rewrite -Hvtreq in Hvtrsem.
    assert (Hin: {| wht := tsup; Hwht := Htsup |} \in sem_t def m.+1 i). apply Hvtrsem.
    apply (@trace_sem_prev_trees _ _ _ {| wht := ptr; Hwht := wu_pred_sub (t1:=ptr) (t2:=tsup) Hsub Htsup |}
                                       {| wht := tsup; Hwht := Htsup |} Hin). apply Hsub.
    unfold tst_node_head. simpl. by destruct ptr; inversion Hroot.
  + destruct cl as [h tl]. simpl. unfold tail in tl. rewrite Hsize.
    apply wlist_to_seq_size.
Qed.

(** All the clauses in the roots in the
   trace semantics of [p]
   are  clauses of [p] *)
Lemma tr_cl_in (tr : trace_sem_trees) def cl s m i:
   tr \in sem_t def m i
-> ABroot (val tr) = inl (RS cl s)
-> cl \in p.
Proof.
induction m as [|m Hm]. move=>/imsetP [ga Hga ->] //.
move=>/setUP [Hrec|]. by apply Hm.
move=>/bigcup_seqP [clb Hclbin /andP [/imsetP [trb Htrbin ->] Htriv]].
rewrite mem_pmap in Htrbin. move:Htrbin.
move=>/mapP [trt /mapP [trp]]. rewrite mem_enum.
move=>/imset2P [descs sb Hdescsin H1 ->] ->.
unfold wu_pcons_seq. unfold wu_pcons_wlist.
destruct Sumbool.sumbool_of_bool;
by move=>// [->] [<-].
Qed.

(** For a safe program (for the heads), and
   any trace in the semantics, if its interpretation is an EDB predicate, then
   the trace is a leaf. *)
Lemma sem_t_Edb_pred def k i (tr : trace_sem_trees) ga :
   tr \in sem_t def k i
-> prog_safe_hds p
-> ded def tr = ga
-> predtype (sym_gatom ga) = Edb
-> exists gab, wht tr = (ABLeaf rul_gr gab).
Proof.
induction k as [|k Hk].
move=>/imsetP [x Hxin ->] H1 H2 /=. by exists x.
move=>Htrin. pose Htrinb := Htrin. clearbody Htrinb. move:Htrin.
move=>/setUP [Hrec|]. apply/Hk/Hrec.
move=>/bigcup_seqP [cl Hclin /andP [/imsetP [pred]]].
rewrite mem_pmap. move=>/mapP [opred /mapP [oopred]].
rewrite mem_enum. move=>/imset2P [descs sd Hdescsin].
rewrite in_set.
move=>/andP [sdmatch /andP [Hded Hall]] -> -> Heq -> Htriv Hsafe Hdga Htyp.
move:Heq. unfold wu_pcons_seq. unfold wu_pcons_wlist.
destruct (Sumbool.sumbool_of_bool);move=>// [Heq].
destruct pred as [[xga|[clx sx] ds] Hpred].
by exists xga.
rewrite -Hdga in Htyp. unfold ded in Htyp.
pose Htypb := (allP Hsafe cl Hclin). clearbody Htypb.
destruct clx as [hclx tlclx]. simpl in Htyp.
inversion Heq as [[Hcleq Hseq Hdeq]].
destruct cl as [hcl tlcl].
inversion Hcleq as [[Hhcleq Htlcleq]].
rewrite Hhcleq in Htyp.
unfold safe_cl_hd in Htypb.
destruct hcl. simpl in *.
rewrite Htyp in Htypb. pose Hf := eqP Htypb. inversion Hf.
Qed.

(** For a safe interpretation (an EDB), and
   any trace in the semantics, if its interpretation is an IDB predicate, then
   the trace is an internal node. *)
Lemma sem_t_Idb_pred def k i (tr : trace_sem_trees) ga :
   tr \in sem_t def k i
(*-> prog_safe_hds p*)
-> safe_edb i
-> ded def tr = ga
-> predtype (sym_gatom ga) = Idb
-> exists clsb, exists descs, wht tr = (ABNode clsb descs).
Proof.
induction k as [|k Hk].
move=>/imsetP [x Hxin ->] H1 /= H2. unfold ded in H2. simpl in H2.
rewrite -H2 (eqP (implyP (forallP H1 x) Hxin)) //.
move=>Htrin. have Htrinb := Htrin. move:Htrin.
move=>/setUP [Hrec|]. apply/Hk/Hrec.
move=>/bigcup_seqP [cl Hclin /andP [/imsetP [pred]]].
rewrite mem_pmap. move=>/mapP [opred /mapP [oopred]].
rewrite mem_enum. move=>/imset2P [descs sd Hdescsin].
rewrite in_set.
move=>/andP [sdmatch /andP [Hded Hall]] -> -> Heq -> Htriv Hsafe Hdga Htyp.
move:Heq. unfold wu_pcons_seq. unfold wu_pcons_wlist.
destruct (Sumbool.sumbool_of_bool);move=>// [Heq].
destruct pred as [[xga|[clx sx] ds] Hpred].
unfold wu_cons_wlist in Heq. unfold wu_cons in Heq.
inversion Heq.
exists (RS clx sx). exists ds. auto.
Qed.

(** ** Utility lemmas relating tocc and the trace
  we find in the semantics *)
(** If we have a program with safe heads (no edb pred) and we have a trace in the semantics whose root is
 clause [cl]. If we have an occurrence, that points to a term of this clause and is on an atom that is
 an EDB predicate, then this will appear as a leaf
 in the direct children of the trace. *)
Lemma edb_in_sem_t_descs def cl s descs Hwht f (tocc : t_occ_finType p) k (i : interp) :
   {| wht := ABNode (RS cl s) descs; Hwht := Hwht |}
       \in sem_t def k i
-> prog_safe_hds p
-> nth_error p (r_ind tocc) = Some cl
-> p_at tocc = Some f
-> predtype f = Edb
-> exists ga, nth_error descs (b_ind tocc) = Some (@ABLeaf _ _ ga).
Proof.
move:cl s descs Hwht f tocc.
induction k as [|k Hk];move=>cl s descs Hwht f tocc /=.
move=>/imsetP [x] //.
move=>/setUP [Hrec|].
apply (Hk cl s descs Hwht f tocc Hrec).
move=>/bigcup_seqP [clb Hclbin /andP
        [/mem_pset_set /imset2P [db sb Hdbin Hsbin Heq] Htriv]].
rewrite in_set in Hsbin.
destruct (andP Hsbin) as [Hsbmatch H].
destruct (andP H) as [Hded Hall]. clear H. clear Hsbin. clear Htriv.
move:Heq. unfold wu_pcons_seq. unfold wu_pcons_wlist.
destruct Sumbool.sumbool_of_bool;move=>// [Hcleq Hseq ->].
rewrite seq_wlistK.
unfold ded_sub_equal in Hded. unfold p_at. unfold at_at.
move=>Hsafe ->. move=>Hnth.
destruct (nth_error_case (body_cl cl) (b_ind tocc)) as [Hnone|[ato Hato]].
by rewrite Hnone in Hnth. destruct Hato as [Hatoin Hnthb].
assert (Heqb : nth_error [seq ded def i | i <- db] (b_ind tocc)
               = Some (gr_atom_def def sb ato)).
rewrite (eqP Hded) -Hcleq -Hseq. apply/(nth_error_map)/Hnthb.
assert (Ht : exists trb, (nth_error db (b_ind tocc) = Some trb
                       /\ ded def trb = gr_atom_def def sb ato)).
apply/nth_error_preim/Heqb.
destruct Ht as [trb [Hnthrb Hdedrb]].
move=>Htyp.
pose Hpred := (allP Hall trb (nth_error_in Hnthrb)). clearbody Hpred.
assert (Hfeq : f = (sym_gatom (gr_atom_def def sb ato))).
rewrite Hnthb in Hnth. by inversion Hnth.
rewrite Hfeq in Htyp.
destruct (@sem_t_Edb_pred def k i trb (gr_atom_def def sb ato) Hpred Hsafe Hdedrb Htyp)
  as [ga Hga]. exists ga.
destruct db. simpl.
simpl in Hnthrb.
by rewrite (@nth_error_map _ _ (@wht (Finite.eqType rul_gr_finType) (Finite.eqType gatom_finType) bn) tval (b_ind tocc) _ Hnthrb) Hga.
rewrite size_tuple. apply wlist_to_seq_size.
Qed.

(** Same as above, but with an IDB predicate, in that case, the child must be an internal node and its
head symbol must be the IDB predicate found *)
Lemma idb_in_sem_t_descs def cl s descs Hwht f (tocc : t_occ_finType p) k (i : interp) :
   {| wht := ABNode (RS cl s) descs; Hwht := Hwht |}
       \in sem_t def k i
-> safe_edb i
-> nth_error p (r_ind tocc) = Some cl
-> p_at tocc = Some f
-> predtype f = Idb
-> exists clsb, exists descsb, hsym_cl (rul_gr_rep clsb).1  = f /\
    nth_error descs (b_ind tocc) = Some (@ABNode _ _ clsb descsb).
Proof.
move:cl s descs Hwht f tocc.
induction k as [|k Hk];move=>cl s descs Hwht f tocc /=.
move=>/imsetP [x] //.
move=>/setUP [Hrec|].
apply (Hk cl s descs Hwht f tocc Hrec).
move=>/bigcup_seqP [clb Hclbin /andP
        [/mem_pset_set /imset2P [db sb Hdbin Hsbin Heq] Htriv]].
rewrite in_set in Hsbin.
destruct (andP Hsbin) as [Hsbmatch H].
destruct (andP H) as [Hded Hall]. clear H. clear Hsbin. clear Htriv.
move:Heq. unfold wu_pcons_seq. unfold wu_pcons_wlist.
destruct Sumbool.sumbool_of_bool;move=>// [Hcleq Hseq ->].
rewrite seq_wlistK.
unfold ded_sub_equal in Hded. unfold p_at. unfold at_at.
move=>Hsafe ->. move=>Hnth.
destruct (nth_error_case (body_cl cl) (b_ind tocc)) as [Hnone|[ato Hato]].
by rewrite Hnone in Hnth. destruct Hato as [Hatoin Hnthb].
assert (Heqb : nth_error [seq ded def i | i <- db] (b_ind tocc)
               = Some (gr_atom_def def sb ato)).
rewrite (eqP Hded) -Hcleq -Hseq. apply/(nth_error_map)/Hnthb.
assert (Ht : exists trb, (nth_error db (b_ind tocc) = Some trb
                       /\ ded def trb = gr_atom_def def sb ato)).
apply/nth_error_preim/Heqb.
destruct Ht as [trb [Hnthrb Hdedrb]].
move=>Htyp.
pose Hpred := (allP Hall trb (nth_error_in Hnthrb)). clearbody Hpred.
assert (Hfeq : f = (sym_gatom (gr_atom_def def sb ato))).
rewrite Hnthb in Hnth. by inversion Hnth.
rewrite Hfeq in Htyp.
destruct (@sem_t_Idb_pred def k i trb (gr_atom_def def sb ato) Hpred Hsafe Hdedrb Htyp)
  as [rulgr Hdescs]. exists rulgr. destruct Hdescs as [descsb H]. exists descsb.
destruct db. simpl.
simpl in Hnthrb. split.
rewrite Hfeq. simpl. destruct trb as [[|[[[[]]]]]].
inversion H.
simpl in H. unfold ded in Hdedrb. simpl in Hdedrb. inversion H.
unfold hsym_cl. simpl in *. by inversion Hdedrb.
by rewrite (@nth_error_map _ _ (@wht (Finite.eqType rul_gr_finType) (Finite.eqType gatom_finType) bn) tval (b_ind tocc) _ Hnthrb) H.
rewrite size_tuple. apply wlist_to_seq_size.
Qed.

End trace_sem_trees.

End tSemantics.
