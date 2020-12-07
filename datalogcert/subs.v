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

(** Second part of the original file "pengine.v" with some modifications *)

Require Import syntax.

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype.
From mathcomp
Require Import tuple finset bigop finfun.

Require Import bigop_aux.
Require Import utils.
Require Import finseqs.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Substitutions.

(** * Substitutions *)
(** ** Substitutions as finitely supported partial functions *)
Definition sub := finfun_finType (ordinal_finType n) (option_finType cons_finType).

Coercion opt_sub (s : option sub) : (option_finType sub) := s.

(** empty substitution *)
Definition emptysub : sub := [ffun _ => None].

(** For each variable, either there is a constant mapped or None *)
Lemma sub_elim (s:sub) v : (exists c, s v = Some c) \/ (s v = None).
destruct (s v) as [c|]. by left; exists c. by right.
Qed.

(** Added notion of composition of substitutions: not exactly sub union as there
   is a priority on s1 *)
Definition subU (s1 s2 : sub) : sub :=
  [ffun v => if (s1 v) is Some c then Some c else s2 v].

(** empty is neutral element for subU *)
Lemma subU_0l (s : sub) : subU emptysub s = s.
Proof.
apply/ffunP =>x. rewrite !ffunE //.
Qed.

Lemma subU_0r (s : sub) : s =  subU emptysub s.
Proof.
apply/ffunP =>x. rewrite !ffunE //.
Qed.

Implicit Types (s : sub) (t : term) (a : atom) (v : 'I_n)
         (b : 'I_n * syntax.constant).

(** Variable is mapped/free by the substitution s *)
Definition mem_bound s v : bool := s v.
Definition mem_free s v : bool := s v == None.

(** Binding b belongs to s *)
Definition mem_binding s b : bool := s b.1 == Some b.2.

(** mem_binding = \in to be used as generic predicate *)
Definition eqbind_class := sub.

Coercion pred_of_eq_bind (s : eqbind_class) : pred_class := [eta mem_binding s].

Canonical mem_bind_symtype := mkPredType mem_binding.

Lemma mem_bindE s b : b \in s = (s b.1 == Some b.2). Proof. by []. Qed.

Definition inE_bis := (mem_bindE, inE).

(** ** Order on substitutions *)
(** substitution [s2] extends [s1] *)
Definition sub_st s1 s2 :=
  [forall v : 'I_n, if s1 v is Some b1 then (v, b1) \in s2 else true].

Notation "A \sub B" := (sub_st A B)
  (at level 70, no associativity) : bool_scope.

(** reflection lemma for substitution ordering *)
Lemma substP s1 s2 : reflect {subset s1 <= s2} (s1 \sub s2).
Proof.
apply/(iffP forallP)=> [H t|H v].
  by move/eqP=> t_s1; have:= H t.1; rewrite t_s1.
by case E: (s1 _) => [d|//]; apply/H; rewrite inE_bis E.
Qed.

Arguments substP [s1 s2].
Prenex Implicits substP.

(** *** Substitution Extensionality Lemma *)
Lemma substE s1 s2 :
  reflect (forall d v, s1 v = Some d -> s2 v = Some d) (s1 \sub s2).
Proof.
apply/(iffP substP)=> [H d v| H [v d]].
  by move/(_ (v,d)): H; rewrite !inE_bis => H /eqP H1; exact/eqP/H.
by rewrite !inE_bis => /eqP H1; rewrite (H d).
Qed.

(** reflexivity of substitution ordering *)
Lemma substss s : s \sub s.
Proof. exact/substP. Qed.

(** transitivity of substitution ordering *)
Lemma subst_trans s1 s2 s3 : s2 \sub s3 -> s1 \sub s2 -> s1 \sub s3.
Proof. by move=> /substP H1 /substP H2; apply/substP=> b /H2; auto. Qed.

(** any substitution extends the empty substitution *)
Lemma subst0s s : emptysub \sub s.
Proof. by apply/substP=> ?; rewrite inE_bis ffunE. Qed.

(** ** Adding an elementary binding *)
(** Extending a substitution [s] with a binding [(v,d)] *)
Definition add s v d :=
  [ffun u => if u == v then Some d else s u].

(** If [v] was free in [s], substitution extension respects ordering. *)
Lemma sub_add s v d : mem_free s v -> s \sub (add s v d).
Proof.
move/eqP=> H; apply/substP=> -[u e].
by rewrite !inE_bis !ffunE; case: ifP H => // /eqP -> ->.
Qed.

(** Value of substitution on variable added *)
Lemma addE (s : sub) (v : 'I_n) d : (add s v d) v = Some d.
Proof. by rewrite ffunE eqxx. Qed.

(** Adding a binding is idempotent *)
Lemma add_add (s : sub) v d e : (add (add s v e) v d) = add s v d.
Proof. by apply/ffunP=> u; rewrite !ffunE; case: eqP. Qed.

(** More lemmas: If s1 and s2 do not bind v, adding a binding on v on the
  composition or composing the substitution after adding v gives
  the same result *)
Lemma subU_addl v c (s1 s2 : sub) : s1 v = None -> s2 v = None
-> (add (subU s1 s2) v c) = subU (add s1 v c) s2.
Proof.
move=>H1 H2. apply/ffunP. move=> x. rewrite !ffunE.
destruct (bool_des_rew (x == v)) as [Hxv|Hxv];rewrite !Hxv;auto.
Qed.

(** If binding are on different variables we can permute the
   additions of those binding to s *)
Lemma add_com (s : sub) v1 v2 c1 c2 :
   v1 <> v2
-> add (add s v1 c1) v2 c2 = add (add s v2 c2) v1 c1.
Proof.
move=> Hneq. apply/ffunP. move=>x. unfold add. rewrite !ffunE.
destruct (bool_des_rew (x == v2)) as [Hxv2|Hxv2];rewrite Hxv2;
destruct (bool_des_rew (x == v1)) as [Hxv1|Hxv1];rewrite Hxv1;auto.
by rewrite -(eqP Hxv2) -(eqP Hxv1) in Hneq.
Qed.

(** ** Substitution on terms *)
(** Term substitution *)
Definition sterm s t : term :=
  match t with
  | Val d => Val d
  | Var v => if s v is Some d
             then Val d
             else Var v
  end.

(*
Definition term_gr s t := { gt : syntax.constant | Val gt = sterm s t }.
*)

(** Empty term substitution application *)
Lemma emptysubE t : sterm emptysub t = t.
Proof. by case: t => //= v; rewrite ffunE. Qed.

(** Substitution extension for terms *)
Lemma sterm_sub t s1 s2 d :
  s1 \sub s2 -> sterm s1 t = Val d -> sterm s2 t = Val d.
Proof.
case: t => //= v /substE H.
by case E: (s1 v) => [a1|//]; move/H: E ->.
Qed.

(** ** Substitution on atoms *)
(** Atom substitution: applying a substiution [s] to a "raw" atom [ra] *)
Definition sraw_atom ra s := RawAtom (sym_atom ra) [seq sterm s x | x <- arg_atom ra].

(** Given an atom [a] and a substitution [s], the atom resulting by instantiating
[a] with [s] is well-formed *)
Lemma satom_proof a s : wf_atom (sraw_atom a s).
Proof. by case: a => ra pf; rewrite /wf_atom /= size_map. Qed.

(** Instantiation function that, for a given atom [a], takes a substitution [s]
and returns the corresponding substituted atom *)
Definition satom a : sub -> atom := fun s => Atom (satom_proof a s).

(** Atom symbols are preserved by substitution instantiation *)
Lemma sym_satom a nu : sym_atom (satom a nu) = sym_atom a.
Proof. by []. Qed.

(** The ground atom that is the result of applying s to a if any *)
Definition atom_gr a s := { gtl : gatom | to_atom gtl = satom a s }.

(** *** Atom Substitution Extensions Lemma:
Let [s1], [s2] be two substitutions. If [s2] extends [s1] and [s1] instantiates
an atom [a] to a ground atom [ga], then [s2] also instantitates [a] to [ga]. *)
Lemma satom_sub a s1 s2 ga :
  s1 \sub s2 -> satom a s1 = to_atom ga -> satom a s2 = to_atom ga.
Proof.
case: a ga => // [[sy1 a1] pf1] [[sy2 a2] pf2] ss /= [hs harg].
apply/val_inj; congr RawAtom; rewrite //=.
elim: a1 a2 harg {pf1 pf2} => //= a1 l1 iha [|a2 l2] //= [].
by move/(sterm_sub ss)=> ->/iha<-.
Qed.

(** The variables of the result of applying [s] to [a] are included in the
    variables of [a] *)
Lemma satom_vars_subset a s : atom_vars (satom a s) \subset atom_vars a.
Proof.
destruct a as [[fa aa] Ha]. unfold atom_vars. unfold satom. simpl.
clear Ha.
induction aa as [|haa tlaa IHa];apply/subsetP;
move=> x /bigcup_seqP [t Htin Htvars].
by rewrite in_nil in Htin.
rewrite in_cons in Htin. destruct (orP Htin) as [Hth|Httl];clear Htin.
destruct haa as [hv|hc]. simpl in Hth.
destruct (sub_elim s hv) as [[c Hc]|Hc];rewrite Hc in Hth;
rewrite (eqP Hth) in Htvars;simpl in Htvars; destruct(andP Htvars) as [H1 H2].
by rewrite in_set0 in H1.
move:H1. move=> /set1P H1. rewrite H1. apply/bigcup_seqP.
exists (Var hv). apply mem_head. apply/andP;split;auto. by apply/set1P.
simpl in Hth. rewrite (eqP Hth) in Htvars. destruct (andP Htvars) as [H1 H2].
by rewrite in_set0 in H1. unfold raw_atom_vars.
rewrite big_cons. apply/setUP;right. apply (subsetP IHa x).
apply/bigcup_seqP. by exists t.
Qed.

(** Tail substitution *)
Definition stail tl s : list atom := [seq satom a s | a <- tl].

(** Lifting of a ground tail to tail *)
Definition to_tail gtl : list atom := [seq to_atom ga | ga <- gtl].

(** Grounding of atom list *)
Definition tail_gr tl s := { gtl : list gatom | to_tail gtl = stail tl s}.

(** The set of variables also decrease when we use a list of atoms. *)
Lemma stail_vars_subset tl s : (tail_vars [seq satom a s | a <- tl])
                     \subset tail_vars tl.
Proof.
induction tl as [|h tl IHtl].
rewrite tail_vars_nil. apply sub0set.
apply/subsetP. move=> x /bigcup_seqP [ato Hatoin Hatovar].
destruct (andP Hatovar) as [H1 H2].
rewrite in_cons in Hatoin. destruct (orP Hatoin) as [Hh|Htl];
clear Hatoin.
rewrite (eqP Hh) in H1.
apply/bigcup_seqP. exists h. apply/mem_head.
by apply/andP;split;[apply (subsetP (satom_vars_subset h s) x H1)|].
apply/tail_vars_cons/(subsetP IHtl)/(tailvars_trans H1 Htl).
Qed.

(** Composition of substitutions giving a ground atom *)
Lemma satomeq_subU a ga s1 s2 :
   satom (satom a s1) s2 = to_atom ga
-> satom a (subU s1 s2) = to_atom ga.
Proof.
destruct a as [[fa aa] Ha].  destruct ga as [[fga aga] Hga].
unfold satom. unfold to_atom. simpl.
move=>[[H1 H2]]. apply val_inj. simpl. clear Ha. clear Hga. rewrite H1.
move:aga H1 H2. unfold sraw_atom. unfold to_raw_atom.
induction aa as [|haa tlaa IHa];destruct aga as [|hga tlga];move=> //= H1 [[H2 H3]].
pose Hrec := (IHa tlga H1 H3).
inversion Hrec as [Hrecb]. clear Hrec. rewrite Hrecb. apply/f_equal.
move:H2. destruct haa as [vh|ch]. unfold subU. simpl.
rewrite ffunE. destruct (sub_elim s1 vh) as [[ch Hch]|Hv1none].
rewrite Hch. move=>[H2]. by rewrite H2.
rewrite Hv1none. simpl. destruct (sub_elim s2 vh) as [[ch Hch]|Hv2none].
rewrite !Hch. move=>[H2]. by rewrite H2. rewrite Hv2none. move=>//.
move=>[H2]. by rewrite H2.
Qed.

(** Same as above but generalized to a list of atoms (body of clause) *)
Lemma staileq_subU tl gtl s1 s2 :
   stail [seq satom a s1 | a <- tl] s2 = [seq to_atom ga | ga <- gtl]
-> stail tl (subU s1 s2) = [seq to_atom ga | ga <- gtl].
Proof.
move:gtl. induction tl as [|h tl IHtl];destruct gtl as [|gh gtl]; move=>//= Heq.
destruct (seq_inj Heq) as [Heqh Hegr].
by rewrite (IHtl gtl Hegr) (satomeq_subU Heqh).
Qed.

(** ** Substitution on clauses *)
Definition scl s (cl : clause) : clause :=
  match cl with
  | Clause h tl => Clause (satom h s) (wmap (fun a => satom a s) tl) end.

End Substitutions.

(** Export the notation *)
Notation "A \sub B" := (sub_st A B)
  (at level 70, no associativity) : bool_scope.

Hint Resolve substss subst0s.

(** ** Non dependent grounding using default element *)
Section NoDepGrounding.

Implicit Types (s : sub) (t : term) (a : atom) (v : 'I_n)
               (b : 'I_n * syntax.constant).

(** default element *)
Variable def : syntax.constant.

(** grounding a term [t] with a substitution [s] and the default element [def] *)
Definition gr_term_def s t : syntax.constant :=
  match t with
  | Val c => c
  | Var i => odflt def (s i)
  end.

(** We can use the above def, or first apply the definition and then
  ground using the empty substitution.*)
Lemma gr_term_def_scl_eq s t : gr_term_def s t = gr_term_def emptysub (sterm s t).
Proof.
destruct t as [v|c]. simpl. unfold odflt. unfold oapp. unfold gr_term_def.
destruct (sub_elim s v) as [[c Hc]|Hnone].
rewrite {2}Hc. by rewrite Hc. rewrite Hnone.
unfold odflt. unfold oapp. by rewrite ffunE.
auto.
Qed.

(** If, when instantiating a term [t] with a substitution [s], we obtain a constant [c],
then we obtain [c] also when grounding [t] with [s] using the default element [def]. *)
Lemma gr_term_defP c t s :
  sterm s t = Val c -> gr_term_def s t = c.
Proof. by case: t => /= [v|e [//]]; case: (s _) => // e []. Qed.

(** If t1 has less variables than t2 (reminder at most one), then
 if s applied to t2 gives a constant, so does s applied to t1 *)
Lemma gr_term_sub t1 t2 s d (t_sub : term_vars t1 \subset term_vars t2) :
  sterm s t2 = Val d -> exists e, sterm s t1 = Val e.
Proof.
case: t2 t1 t_sub => [v2|d2] [v1|d1] /subsetP /=.
+ move/(_ v1)=> /implyP; rewrite !inE eqxx /= => /eqP->.
  by case E: (s v2) => [a|] //= _; exists a.
+ by move=> _ _; exists d1.
+ by move/(_ v1)=> /implyP; rewrite !inE eqxx.
+ by move=> _ _; exists d1.
Qed.

(** *** Non dependent grounding on raw atoms *)
(** grounding a raw atom [ra] with a substitution [s] and the default element [def] *)
Definition gr_raw_atom_def s ra : raw_gatom :=
  RawGAtom (sym_atom ra) (map (gr_term_def s) (arg_atom ra)).

(** Let s1 and s2 be two substitutions. For each variable v,
   either s1 or s2 is undefined and the other coincide with s.
   Then grounding a raw atom with s2 and then s1 is the same as
   grounding with s *)
Lemma gr_raw_atom_scl_eq (s s1 s2 : sub) ra :
 (forall v, (s1 v = s v /\ s2 v = None) \/ (s2 v = s v /\ s1 v = None))
 -> gr_raw_atom_def s ra = gr_raw_atom_def s1 (sraw_atom ra s2).
Proof.
move=>Hsubs.
destruct ra as [h tl]. induction tl. auto.
unfold gr_raw_atom_def. unfold gr_raw_atom_def in IHtl.
simpl. apply/f_equal. inversion IHtl as [H].
rewrite H. destruct a as [va|ca];auto.
destruct (Hsubs va) as [[Hs1 Hs2]|[Hs2 Hs1]];simpl;
rewrite Hs2; simpl. by rewrite Hs1.
destruct (sub_elim s va) as [[c Hc]|Hn].
by rewrite !Hc. rewrite Hn. simpl. by rewrite Hs1.
Qed.

(** *** Non dependent grounding on atoms *)
(** well-formedness is preserved by non-dependent grounding *)
Lemma gr_atom_def_proof s a : wf_gatom (gr_raw_atom_def s a).
Proof. by case: a => ra pf; rewrite /wf_gatom size_map. Qed.

(** grounding an atom [a] with a substitution [s] *)
Definition gr_atom_def s a : gatom := GAtom (gr_atom_def_proof s a).

(** Let [a] be an atom and [s] a substitution. If, when instantiating [a] with [s], we obtain
the ground atom [ga], then, when grounding [a] with [s] and the default element [def], we also
obtain [ga]. *)
Lemma gr_atom_defP a s ga :
  satom a s = to_atom ga -> gr_atom_def s a = ga.
Proof.
case: a ga => [[sym1 t1] pf1] [[sym2 t2] pf2] /= [hs harg].
apply/val_inj; congr RawGAtom; rewrite //=.
by elim: t1 t2 harg {pf1 pf2} => [|x1 t1 iht1] [|x2 t2] //= [] /gr_term_defP <- /iht1<-.
Qed.

(** Let [ga] be a ground atom. If we lift it to an atom and ground it with a substitution
[s] and a default element [def], [ga] is preserved. *)
Lemma gr_atom_defK ga s : gr_atom_def s (to_atom ga) = ga.
Proof.
case: ga => //= [[sym t] pf]; apply/val_inj => /=; congr RawGAtom.
by elim: t {pf} => //= a ga ->.
Qed.

(** *** Non dependent grounding on clauses*)
Definition gr_cl_def s cl :=
  GClause (gr_atom_def s (head_cl cl)) (wmap (gr_atom_def s) (body_cl cl)).

(** *** From substitution to grounding *)
(** Using default value to lift a subst to a grounding *)
Definition to_gr s : gr := [ffun v => if s v is Some c then c else def].

(** From grounding to substitution *)
Definition to_sub (g : gr) : sub := [ffun v => Some (g v)].

(** Applied to a term, a grounding gives as the associated subst *)
Lemma to_subE t g : sterm (to_sub g) t = Val (gr_term g t).
Proof. by case: t => [i|d] //=; rewrite ffunE. Qed.

(** If s is defined on t, applying it on t gives as applying its
  associated grounding*)
Lemma to_grP t s c : sterm s t = Val c -> gr_term (to_gr s) t = c.
Proof.
move/gr_term_defP; case: t => [v|e] //=.
by case E: (s v) => [a|] <-; rewrite ffunE E.
Qed.

(** ** Domain of a substitution - modified *)
(** substitution domain: set of all variables it binds (moved) *)
Definition dom s := [set v : 'I_n | s v].

(** The domain of the empty subsitution is the empty set *)
Lemma dom_emptysub : dom emptysub = set0.
Proof.
by apply/eqP; rewrite eqEsubset; apply/andP; split;
apply/subsetP=>x ; rewrite in_set ?ffunE ?in_set0.
Qed.

(** domain of a "singleton sub" is the relevant variable - added *)
Lemma dom_singlesub v c : dom (add emptysub v c) = [set v].
Proof.
apply/eqP; rewrite eqEsubset; apply/andP; split;
apply/subsetP=>x ; rewrite in_set ?ffunE ?in_set0.
- destruct (bool_des_rew (x == v)) as [H|H]; rewrite ?H ?(eqP H);auto.
  move=>Hb. by apply/set1P.
- move=> H. by rewrite in_set ffunE H.
Qed.

(** equality of a "singleton sub" - added *)
Lemma eq_singlesub s v c : 
   dom s = [set v]
-> s v = Some c
-> s = add emptysub v c.
Proof.
move=> Hdom Heq.
apply/ffunP;move=>x;rewrite ffunE.
destruct (bool_des_rew (x == v)) as [Hxv|Hxv];rewrite Hxv.
- by rewrite (eqP Hxv) Heq.
- move:Hdom. move=>/eqP. rewrite eqEsubset. move=>/andP[/subsetP H1 H2].
  destruct (sub_elim s x) as [[d Hd]|Hnone].
  + assert (Hdom2 : x \in dom s). by rewrite in_set Hd.
    rewrite (set1P (H1 x Hdom2)) eq_refl in Hxv. inversion Hxv.
  + by rewrite Hnone ffunE.
Qed.

Lemma sub_dom (s1 s2 : sub) : 
  s1 \sub s2 -> dom s1 \subset dom s2.
-Proof.
unfold sub_st.
move=>H.
apply/subsetP=>x.
destruct (sub_elim s1 x) as [[c Hc]|Hnone].
move=>Hb. rewrite in_set.
have Ht := forallP H x. rewrite Hc mem_bindE in Ht.
by rewrite (eqP Ht).
by rewrite in_set Hnone.
Qed.

(** If [v] in the domain of [s], [v] cannot be in the result of applying [s]
   to an atom [a] *)
Lemma v_in_dom_satom v s a : v \in dom s
-> v \in atom_vars (satom a s) -> False.
Proof.
move=>Hdom.
destruct a as [[f args] Ha].
unfold atom_vars. simpl. clear Ha.
induction args as [|h tl IHl]; move=>/bigcup_seqP [t Hin Hvt].
by rewrite in_nil in Hin.
destruct (andP Hvt) as [Hvint Htriv].
rewrite in_cons in Hin. destruct (orP Hin) as [Hth|Hrec]. clear Hin.
- rewrite (eqP Hth) in Hvint. unfold term_vars in Hvint.
  unfold sterm in Hvint. unfold sterm in Hth.
  destruct h as [vb|c].
  + simpl in *. destruct (sub_elim s vb) as [[svb Hsvb]|Hsvb].
    - by rewrite Hsvb in_set0 in Hvint.
    - rewrite Hsvb in Hvint. rewrite Hsvb in Hth.
      by rewrite (set1P Hvint) in_set Hsvb in Hdom.
  + by rewrite in_set0 in Hvint.
- apply/IHl/bigcup_seqP. by exists t.
Qed.

(** If [v] in the domain of [s], [v] cannot be in the result of applying [s]
   to a list of atoms [l]. *)
Lemma v_in_dom_stail v s l: v \in dom s
-> v \in tail_vars [seq satom a s | a <- l]
-> False.
Proof.
induction l as [|h l Hl];unfold tail_vars;
move=>Hdom Hvtail;
destruct (bigcup_seqP _ _ _ _ _ _ Hvtail) as [ato Hatoin Hv].
by rewrite in_nil in Hatoin.
destruct (andP Hv) as [Hvin Htriv].
rewrite in_cons in Hatoin. destruct (orP Hatoin) as [Hsato|Hrec].
rewrite (eqP Hsato) in Hvin. apply (v_in_dom_satom Hdom Hvin).
apply Hl. apply Hdom. apply/bigcup_seqP. by exists ato.
Qed.

(** If the domain of [s] contains all the variables of [ato], then
   applying [s] as a grounding to [ato] with default value [gr] gives the
   same result as applying [s] as a regular substitution. *)
Lemma to_atom_satom_eq (s : sub) ato : atom_vars ato \subset dom s ->
  to_atom (gr_atom_def s ato) = satom ato s.
Proof.
move=>Hsub. destruct ato as [[f l] Hato].
apply/val_inj. simpl. unfold to_raw_atom. unfold sraw_atom.
simpl. apply/f_equal. unfold atom_vars in Hsub.
simpl in Hsub. clear Hato.
induction l as [|h l Hl].
auto. simpl. rewrite Hl.
assert (Hheq : Val (gr_term_def s h) = sterm s h).
unfold gr_term_def. destruct h. unfold odflt. unfold oapp.
unfold sterm.
assert (Hin : o \in raw_atom_vars (RawAtom f (Var o :: l))).
apply/bigcup_seqP. exists (Var o). apply/mem_head.
apply/andP;split. by apply/set1P. trivial.
have Hindom := (subsetP Hsub o Hin).
destruct (sub_elim s o) as [[c Hc]|Hc];rewrite !Hc;auto.
rewrite in_set Hc in Hindom. inversion Hindom.
auto.
by rewrite Hheq.
apply/subsetP=>x Hx; apply/(subsetP Hsub x)/raw_atom_vars_cons/Hx.
Qed.


(** Two substitution having the same domain and such that one is smaller than
  the other are in fact identical. *)
Lemma subU_eq (s1 s2 : sub) :
   dom s1 = dom s2
-> s1 \sub s2
-> s1 = s2.
Proof.
move=>/eqP; rewrite eqEsubset; move=> /andP [Hd1 Hd2] Hsub.
apply/ffunP. move=> x.
destruct (sub_elim s1 x) as [[c Hc]|Hnone].
rewrite Hc. pose Hsubb := forallP Hsub x. clearbody Hsubb.
rewrite Hc mem_bindE in Hsubb. by rewrite (eqP Hsubb).
destruct (sub_elim s2 x) as [[c Hc]|Hnoneb].
assert (Hin : x \in dom s2). by rewrite in_set Hc.
pose Hinb := (subsetP Hd2 x Hin). clearbody Hinb.
by rewrite in_set Hnone in Hinb.
by rewrite Hnone Hnoneb.
Qed.

(** For variables in the domain substitution and grounding coincide *)
Lemma dom_sub_grE (s : sub) (v : 'I_n) :
  v \in dom s -> s v = (to_sub (to_gr s)) v.
Proof.
rewrite in_set. move=>Hs.
unfold to_gr. rewrite ffunE.
destruct (sub_elim s v) as [[c Hc]|Hc]; rewrite Hc.
by rewrite ffunE Hc.
rewrite Hc in Hs. inversion Hs.
Qed.

(** If domain of substitution is empty, then s is the empty substitution *)
Lemma emptymin s : dom s \subset set0 -> s = emptysub.
Proof.
rewrite subset0.
move=>/eqP H. apply/ffunP=>v.
destruct (sub_elim s v) as [[c Hc]|Hc];
rewrite Hc ffunE;auto.
assert (Hf : v \in set0).
by rewrite -H in_set Hc.
by rewrite in_set0 in Hf.
Qed.

(** The domain of a set of substitution is the union of the domain of its members *)
Definition all_dom (ss : {set sub}) := \bigcup_(s in ss) dom s.

(** The domain of the set of substitution reduced to the empty substitution is empty*)
Lemma all_dom_empty : all_dom [set emptysub] = set0.
Proof.
unfold all_dom.
apply/eqP. rewrite eqEsubset;apply/andP;split;apply/subsetP;move=>x Hx.
destruct (bigcupP Hx) as [y Hyempt Hxy].
rewrite (set1P Hyempt) in Hxy. by rewrite dom_emptysub in_set0 in Hxy.
by rewrite in_set0 in Hx.
Qed.

(** ** Restriction of a substitution to a set of variables (Added) *)
Definition sub_filter (s : sub) (t : {set 'I_n}) :=
  [ffun v => if v \in t then s v else None].

(** The restriction has a smaller domain *)
Lemma sub_filter_subset_s (s : sub) (t : {set 'I_n}) :
  dom (sub_filter s t) \subset dom s.
Proof.
apply/subsetP=>x. rewrite !in_set ffunE.
by destruct (x \in t).
Qed.

(** Its domain is in fact also included in t (the restriction) *)
Lemma sub_filter_subset_t (s : sub) (t : {set 'I_n}) :
  dom (sub_filter s t) \subset t.
Proof.
apply/subsetP=>x. rewrite !in_set ffunE.
by destruct (x \in t).
Qed.

(** For v in t, if s v is defined, then so is the restriction and it
  gives the same result. *)
Lemma sub_filter_eq (s : sub) (t : {set 'I_n}) (v : 'I_n) :
  v \in t -> (sub_filter s t) v = s v.
Proof.
rewrite !ffunE. by move=> ->.
Qed.

(** Restricting a substitution to a set that contains its domain does
  not change the substitution *)
Lemma sub_sub_filter (s : sub) (sb : {set 'I_n}) :
                                     dom s \subset sb
                                  -> sub_filter s sb = s.
Proof.
move=> /subsetP Hsub. apply/ffunP. move=> x. rewrite !ffunE.
destruct (bool_des_rew (x \in sb)) as [Hxin|Hxin];rewrite Hxin;auto.
destruct (sub_elim s x) as [[c Hsx]|Hsx];rewrite Hsx;auto.
assert (Hxs : x \in dom s). by rewrite in_set Hsx.
pose Hsubb := Hsub x Hxs. clearbody Hsubb. by rewrite Hxin in Hsubb.
Qed.

(** Restricting the empty sub does not change it. *)
Lemma utemptysub (t : {set 'I_n}) : sub_filter emptysub t = emptysub.
Proof.
apply sub_sub_filter. rewrite dom_emptysub. apply sub0set.
Qed.

(** Let [t1] and [t2] disjoint, [v] in [t1], the restriction of [sp] to [t2]
is the same as the restriction of [sp] augmented with a binding for [v] to
[t2] *)
Lemma add_typed_untyped v (t1 t2 : {set 'I_n}) c sp :
  (v \in t1) -> [disjoint t1 & t2] ->
  sub_filter sp t2 = sub_filter (add sp v c) t2.
Proof.
move=>Htyped Hdisj.
apply/ffunP=>x.
destruct (bool_des_rew (x \in t1)) as [Hxtyp|Hxtyp];
destruct (bool_des_rew (x == v)) as [Hxv|Hxv];
rewrite !ffunE ?Hxtyp ?Hxv;auto;
destruct (bool_des_rew (x \in t2)) as [Hxtypb|Hxtypb];
rewrite ?Hxtypb;auto; rewrite -(eqP Hxv) in Htyped;
exfalso;apply (disjoint_in_false Htyped Hxtypb Hdisj).
Qed.

(** If [v] in [ŧ2], the restriction of [sp] augmented with a binding for [v]
  to [t2] is equal to augmenting the restriction of [sp] to [t2] with this
  same binding. *)
Lemma add_untyped_untyped v (t : {set 'I_n}) c sp :
   v \in t
-> add (sub_filter sp t) v c = (sub_filter (add sp v c) t).
Proof.
move=>Huntyped.
apply/ffunP=>x.
destruct (bool_des_rew (x \in t)) as [Hxtyp|Hxtyp];
destruct (bool_des_rew (x == v)) as [Hxv|Hxv];
rewrite !ffunE ?Hxtyp ?Hxv;auto.
by rewrite -(eqP Hxv) Hxtyp in Huntyped.
Qed.

Lemma atom_vars_sub_gr (a:atom) (s1 s2:sub) :
   atom_vars a \subset dom s1 
-> s1 \sub s2
-> gr_atom (to_gr s1) a = gr_atom (to_gr s2) a.
Proof.
move=>Hasub Hsub.
destruct a as [[g args] Ha].
apply/val_inj.
simpl. unfold gr_raw_atom.
simpl. apply/f_equal. unfold atom_vars in Hasub.
simpl in Hasub. clear Ha.
induction args as [|[v|c] args Hrec];auto.
simpl;apply/f_equal2.
rewrite !ffunE.
destruct (sub_elim s1 v) as [[c Hc]|Hnone].
have Hf := forallP Hsub v. rewrite Hc mem_bindE in Hf.
by rewrite Hc (eqP Hf).
assert (Hvin : v \in dom s1).
apply (subsetP Hasub). apply/bigcup_seqP.
exists (Var v). apply/mem_head.
apply/andP;split;auto. by apply/set1P.
rewrite in_set Hnone in Hvin. inversion Hvin.
apply/Hrec;auto. apply/subset_trans. 
apply raw_atom_vars_cons_sub. apply Hasub.
simpl. apply/f_equal.
apply/Hrec;auto. apply/subset_trans. 
apply raw_atom_vars_cons_sub. apply Hasub.
Qed.

Lemma atom_vars_sub_gr_def (a:atom) (s1 s2:sub) :
   atom_vars a \subset dom s1 
-> s1 \sub s2
-> gr_atom_def s1 a = gr_atom_def s2 a.
Proof.
move=>Hasub Hsub.
destruct a as [[g args] Ha].
apply/val_inj.
simpl. unfold gr_raw_atom_def.
simpl. apply/f_equal. unfold atom_vars in Hasub.
simpl in Hasub. clear Ha.
induction args as [|[v|c] args Hrec];auto.
simpl;apply/f_equal2. 
destruct (sub_elim s1 v) as [[c Hc]|Hnone].
have Hf := forallP Hsub v. rewrite Hc mem_bindE in Hf.
by rewrite Hc (eqP Hf).
assert (Hvin : v \in dom s1).
apply (subsetP Hasub). apply/bigcup_seqP.
exists (Var v). apply/mem_head.
apply/andP;split;auto. by apply/set1P.
rewrite in_set Hnone in Hvin. inversion Hvin.
apply/Hrec;auto. apply/subset_trans. 
apply raw_atom_vars_cons_sub. apply Hasub.
simpl. apply/f_equal.
apply/Hrec;auto. apply/subset_trans. 
apply raw_atom_vars_cons_sub. apply Hasub.
Qed.

Lemma gr_term_def_eq_in_dom s1 s2 v1 v2 :
   gr_term_def s1 (Var v1) = gr_term_def s2 (Var v2)
-> v1 \in dom s1
-> v2 \in dom s2
-> s1 v1 = s2 v2.
Proof.
rewrite !in_set. simpl. unfold odflt. unfold oapp.
destruct (sub_elim s1 v1) as [[c1 Hc1]|Hc1];
destruct (sub_elim s2 v2) as [[c2 Hc2]|Hc2];
rewrite Hc1 Hc2;move=>//.
move=>-> //.
Qed.

End NoDepGrounding.
