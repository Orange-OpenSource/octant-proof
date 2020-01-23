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

(** This is the sixth part of the original file "pengine.v" with modifications
    by Pierre-Léo Bégay. *)

Require Import syntax.
Require Import subs.
Require Import pmatch.
Require Import bSemantics.
Require Import monotonicity.

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset bigop finfun.

Require Import bigop_aux.
Require Import utils.
Require Import finseqs.

Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (s r : sub) (d def : syntax.constant) (t : term) (a : atom)
               (ga : gatom) (tl : list atom) (cl : clause) (i : interp).

(** * Soundness of the standard semantics *)
Section Soundness.

(** ** Term Matching Soundness:
Let [t] be a term, [d] a constant and [s] an arbitrary substitution.
If term matching outputs a substitution [r], extending [s] with the matching of [t] against [d], then
[r] is indeed a solution, i.e, the instantiation of [t] with [r] equals [d].*)
Lemma match_term_sound d t s r : match_term d t s = Some r -> sterm r t = Val d.
Proof.
case: t => /= [v|c]; last by case: eqP => [->|].
case E: (s _) => [e|]; last by case => <-; rewrite ffunE eqxx.
by case: eqP => //->[<-]; rewrite E.
Qed.

(** List Fold Soundness *)
(** [f] takes a substitution and may give back a substitution (option) and is increaising in that case.
If we iterate [f] over [l] starting from [u] with
[foldl], if we get a result, it is greater than
the original [u] (which could not be None).
Reminder: [obind f (Some x) = f x] and
[obind f None = None] *)
Lemma foldl_0_gen {A} u l r
     (f : A -> sub -> option sub)
     (f_pmon : forall x s r, f x s = Some r -> s \sub r)
 : foldl (fun acc p => obind (f p) acc) u l = Some r ->
   exists2 s, u = Some s & s \sub r.
Proof.
elim: l u => [|hd tl IHl] //= => [Hu | u Hfold].
  by exists r; [done | apply/substss].
case: (IHl (obind (f hd) u) Hfold) => [s Hbind Hsub].
case E : u => [s'|]; rewrite E //= in Hbind.
by exists s'; [done | apply/(subst_trans Hsub (@f_pmon hd s' s Hbind))].
Qed.

(** If iterating [match_term] over lists of atoms and ground atoms starting from [u], we obtain a substitution
r, then u was a substitution s (not None) and r greater
than s *)
Lemma foldl_0 gar ar u r :
 foldl (fun acc p => obind [eta match_term p.1 p.2] acc) u (zip gar ar) = Some r ->
 exists2 s, u = Some s & s \sub r.
Proof. by apply: foldl_0_gen => x s r0; apply: match_term_sub. Qed.

(** ** Atom Matching Soundness:
Let [a] be an atom, [ga] a ground atom and [s], an arbitrary substitution.
If atom matching outputs a substitution [r], extending [s] with the matching of [a] against [ga], then
[r] is indeed a solution, i.e, the instantiation of [a] with [r] equals [ga]. *)
Lemma match_atom_sound a ga s r :
  match_atom s a ga = Some r -> satom a r = to_atom ga.
Proof.
case: a ga => /= [[s_a arg_a] pf_a] [[s_g arg_g] pf_g] // hma.
apply/val_inj; move: hma; rewrite /match_atom /= {pf_a pf_g}.
case: eqP => Hs //; rewrite Hs; case: eqP => Harg //=.
elim: arg_a arg_g s Harg => [| a ar iha] [| g gar] //= s [Hsize] Hf.
congr RawAtom => /=.
have [s' Hs' Hsub] := foldl_0 Hf; rewrite Hs' in Hf.
have [->] := iha _ _ Hsize Hf.
by have/sterm_sub-> := (match_term_sound Hs').
Qed.

(** ** Atom Matching Substitution Lemma:
If [s2] is the result of matching an atom [a] against
a ground atom [ga], starting from an initial substitution [s1], then [s2] is the extension of [s1]. *)
Lemma match_atom_sub s1 s2 a ga :
  match_atom s1 a ga = Some s2 -> sub_st s1 s2.
Proof.
rewrite/match_atom.
case: a ga => [[s_a arg_a] pf_a] [[s_g arg_g] pf_g].
rewrite /match_raw_atom /=.
case: eqP => // Hs //=.
case: eqP => // Harg //=.
move/foldl_0=> [s' Hs' Hsub].
by injection Hs' => H; rewrite H; apply/Hsub.
Qed.

(** substitution domain: set of all variables it binds *)
Lemma match_atoms_sub s1 i a :
  [forall s2 in (match_atom_all i a s1), s1 \sub s2].
Proof.
apply/forallP. move=> x. apply/implyP.
move=>/match_atomsP [ga Hgain Hmatcheq].
by apply (@match_atom_sub _ _ a ga).
Qed.

(** For a grounding, no need of def. translation through the grounding
  or through the coresponding sub coincide. *)
Lemma to_sub_grt def t nu :
  gr_term_def def (to_sub nu) t = gr_term nu t.
Proof. by case: t=> [var | val] //=; rewrite ffunE. Qed.

(** Same as above but for atom instead of terms. *)
Lemma to_sub_gra def a nu :
  gr_atom_def def (to_sub nu) a = gr_atom nu a.
Proof.
case: a=> [[sym args] pf_a]; apply/val_inj; congr RawGAtom.
by apply/eq_map=> x; apply/to_sub_grt.
Qed.

(** If all vars of a term [t] (0 or 1) are in [s], then applying [s]
   on [t] gives a value*)
Lemma sub_dom_grt t s :
  term_vars t \subset dom s <-> exists c, sterm s t = Val c.
Proof.
case: t=> [var|val]; split ; rewrite? (sub0set, sub1set, inE) //=.
+ by case: (s var) => [c| ] => c'//=; exists c.
+ by case: (s var) => [c|] //; case=> //.
+ by exists val.
Qed.

(** Reflection view for the fact that the vars of a raw atom [ra] are
   in the domain of substitution [s] *)
Lemma sub_dom_gra (ra : raw_atom) s :
  reflect (exists gra, sraw_atom ra s = to_raw_atom gra)
          (raw_atom_vars ra \subset dom s).
Proof.
case: ra => [sym args]; apply: (iffP idP).
  elim: args => [|t arg iha]; first by exists (RawGAtom sym [::]).
  rewrite /raw_atom_vars big_cons subUset => /andP[/sub_dom_grt [c Hc] /iha] [[sy l] [->]] H.
  by exists (RawGAtom sy (c :: l)); congr RawAtom; rewrite /= Hc H.
elim: args => [| a arg iha]; first by rewrite /raw_atom_vars big_nil sub0set.
case=> [[sga [|ga gal]] // [hs hga hgal]].
rewrite /raw_atom_vars big_cons subUset iha ?andbT; first by apply/sub_dom_grt; exists ga.
by exists (RawGAtom sym gal); congr RawAtom; rewrite /= hgal.
Qed.

(** If applying [s] on [a] gives a ground atom [gra] at the level
   of raw atoms, it also gives a raw atom [ga] *)
Lemma sub_dom_raw a s :
  (exists gra : raw_gatom, sraw_atom a s = to_raw_atom gra) ->
   exists ga : gatom, satom a s = to_atom ga.
Proof.
case=> ga sha.
have pf_ga: wf_gatom ga.
  case: ga a sha => [s' arg'] [[sa aa] pfa] [h1 h2].
  rewrite /wf_gatom /= -h1.
  have -> // : size arg' = size aa.
  by move/(congr1 size): h2; rewrite !size_map.
by exists (GAtom pf_ga); apply/val_inj.
Qed.

(** Reflection view for fact that the vars of an atom [a] are
   in the domain of substitution [s] *)
Lemma sub_dom_ga (a : atom) s :
  reflect (exists ga, satom a s = to_atom ga)
          (atom_vars a \subset dom s).
Proof.
have [h|h]:= (sub_dom_gra a s).
  by left; apply: sub_dom_raw.
right; case=> [ga hga]; apply: h.
by exists ga; case: a hga => a /= pf /(congr1 val).
Qed.

Implicit Types (ss : {set sub}).

(** Starting from a substitution [ss0] and a list of atom [tl],
  builds the set of all substitutions that match the interpretation
  [i] *)

Definition match_pbody tl i ss0 := foldS (match_atom_all i) ss0 tl.

(** Reflection view on the inductive theorem associated with [match_pbody] *)
Lemma match_pbody_cons a l i r ss0 :
  reflect (exists2 s, s \in ss0 & r \in match_pbody l i (match_atom_all i a s))
          (r \in match_pbody (a :: l) i ss0).
Proof. exact: bindP. Qed.

(** Relates [match_pbody] and [pmatch.match_body] *)
Lemma match_body_pbody tl i r :
  match_body i tl = match_pbody tl i [set emptysub].
Proof. by rewrite /match_pbody /match_body. Qed.

(** If [s'] is smaller than [s] and undefined for [v], completing
  it with the binding of [v] in [s] will still give a substitution
   smaller than [s] *)
Lemma sub_st_add v d s' s :
  s' \sub s -> s v = Some d -> s' v = None -> add s' v d \sub s.
Proof.
move=> Hsub Hs Hs'; apply/forallP=> v'; rewrite /add ffunE.
case: eqP => [->| Hv]; first exact/eqP.
by move/forallP in Hsub; apply/Hsub.
Qed.

(** technical lemma. If [s] in [match_pbody (a :: ll) i sp], then
   [s] greater than [sp] *)
Lemma match_atoms_pbody s sp ll i a:
s \in match_pbody ll i (match_atom_all i a sp) -> sp \sub s.
Proof.
move:a sp. induction ll as [|lh ll];move=>a sp H.
apply (implyP (forallP (match_atoms_sub sp i a) s) H).
destruct (match_pbody_cons _ _ _ _ _ H) as [sb Hsbin Hsbmatch].
apply subst_trans with (s2 := sb).
apply IHll with (a := lh). apply Hsbmatch.
apply (implyP (forallP (match_atoms_sub sp i a) sb) Hsbin).
Qed.

(** ** Term Matching Completeness:
Given a solution [s] to term-matching [t] w.r.t [d],
for any sub-substitution [s'], there exists an [r] that is a solution
 and also better/minimal w.r.t [s] *)
Lemma match_term_complete d t s s' :
 sub_st s' s -> sterm s t = Val d ->
 exists r, match_term d t s' = Some r /\ sub_st r s.
Proof.
case: t=> /= [v|c] // => Hsub //; last first.
  by case=> [->] //; exists s'; split; [case: eqP | done].
case Hs : (s _) => [e|] //; case=> He //; rewrite -He {d He}.
case Hs': (s' _) => [e'|] //.
     by exists s'; case: eqP=> He //; last first;
     move/substE in Hsub;
     have Hsub' := (Hsub e' v Hs');
     rewrite Hs in Hsub'; injection Hsub';
     rewrite //= Hsub.
by exists (add s' v e); split; [done | apply/sub_st_add].
Qed.

(** ** Atom Matching Completeness:
Let [a] be an atom, [ga] a ground atom and [s] a substitution
that instantiates [a] to [ga]. Then, seeding the atom matching algorithm with [s'], an arbitrary restriction
of [s], outputs a better matching solution than [s], i.e, a substitution [r] that is smaller or equal to [s]. *)
Lemma match_atom_complete ga a s s' :
 sub_st s' s -> satom a s = to_atom ga ->
 exists2 r, match_atom s' a ga = Some r & sub_st r s.
Proof.
case: a ga => [[s_a arg_a] pfa] [[s_g arg_g] pfs] //= Hsub [hsym Harg].
rewrite /match_atom /= hsym eqxx /=.
have ->: size arg_a = size arg_g.
  by move/(congr1 size): Harg; rewrite !size_map.
rewrite eqxx {s_a s_g hsym pfa pfs}.
elim: arg_a arg_g s' Hsub Harg => [| h l IHl] [| gh gl] //= s' Hsub.
  by exists s'.
case; move=> Ht Hl.
have [r' [Hs'r Hr]] := match_term_complete Hsub Ht.
have [r'' H Hr_sub] := IHl _ _ Hr Hl.
by exists r''; rewrite // Hs'r.
Qed.

(** Let [a] be an atom, [ga] a ground atom and [v] a grounding. Instantiating [a] with the coercion of
[v] equals the lifting of [ga] iff the grounding of [a] with [v] equals [ga] *)
Lemma to_gr_atomP a v ga :
  satom a (to_sub v) = to_atom ga <-> gr_atom v a = ga.
Proof.
case: a ga => [[s_a arg_a] pfa] [[s_g arg_g] pfg];
split; case => hs harg; apply/val_inj => /= {pfa pfg}.
  congr RawGAtom => //=.
  elim: arg_g arg_a harg => [|ag arg_g ihag] [|aa arg_a] //.
  by rewrite /= to_subE => -[->] ha; rewrite ihag.
congr RawAtom => //=.
elim: arg_g arg_a harg => [|ag arg_g ihag] [|aa arg_a] //.
by rewrite /= to_subE => -[->] ha; rewrite ihag.
Qed.

(** Let [s'] be a substitution from init [ss0] that is smaller than
   the grounding [v] and [v] such that applying it on the body of
   clause [cl] gives atom member of interpretation [i], then the
   set of substitutions matching the body [cl] for interpretation [i]
   starting from [ss0] contains a substitution [r] smaller than [v] *)
Lemma match_ptl_complete s' ss0 i cl v :
 s' \in ss0 -> sub_st s' (to_sub v) ->
 all (mem i) (body_gcl (gr_cl v cl)) ->
 exists2 r, r \in match_pbody (body_cl cl) i ss0 &
            sub_st r (to_sub v).
Proof.
rewrite wmapcoK.
case: cl => head body //=.
elim: (wlist_to_seq_co body) s' ss0 => [| hd tl] => //= [ | IHl ] s' ss0 Hs' H_sub H_mem //.
  exists s'; [exact: Hs' | exact: H_sub].
case/andP: H_mem => [H_in H_mem].
have HH : exists2 ga, ga \in i & gr_atom v hd = ga.
  by exists (gr_atom v hd).
case: HH=> [ga Hga_in Hga].
move/to_gr_atomP in Hga.
have [r' Hr' Hr'_sub] := (@match_atom_complete ga hd (to_sub v) s' H_sub Hga).
have Hr'_all : r' \in match_atom_all i hd s'.
  by apply/match_atomsP; exists ga.
have [s Hs Hs_sub] := IHl r' (match_atom_all i hd s') Hr'_all Hr'_sub H_mem.
by exists s; [apply/match_pbody_cons; exists s' | done].
Qed.

(** Let [s'] be a substitution from init [ss0] that is smaller than
   [s]. Let [s] be such than applying [s] on a list of atom [tl]
   gives a list of ground atom [gtl] contained in [i]. Then
   matching [tl] in [i] starting from substitution [ss0] contains
   a substitution [r] smaller than [s] *)
Lemma match_ptl_sub_complete s s' ss0 i tl gtl :
 s' \in ss0 -> sub_st s' s ->
 stail tl s = [seq to_atom ga | ga <- gtl]
 -> all (mem i) gtl ->
 exists2 r, r \in match_pbody tl i ss0 &
            sub_st r s.
Proof.
move:s s' ss0 i gtl.
induction tl as [| hd tl IHtl];destruct gtl as [|hgtl tlgtl];
unfold match_pbody; move=> //= Hexs Hssub Heq Hall.
by exists s'.
destruct (seq_inj Heq) as [Hheq Htleq].
case/andP: Hall => [H_in H_mem].
destruct (@match_atom_complete hgtl hd s s' Hssub Hheq) as [sp Hspmatch Hspin].
assert (Hsp_all : sp \in match_atom_all i hd s'). by apply/match_atomsP; exists hgtl;auto.
destruct (@IHtl s sp (match_atom_all i hd s') i tlgtl Hsp_all Hspin Htleq H_mem)
  as [sr Hsr Hsr_sub].
exists sr;auto. by apply/match_pbody_cons; exists s'.
Qed.

(** If applying the grounding [v] to the body of [cl] gives ground
  atoms in [i], then matching the body of [cl] with [i]
  starting from the empty substitution contains a substitution [r]
  smaller than [v] *)
Lemma match_tl_complete i cl v :
 all (mem i) (body_gcl (gr_cl v cl)) ->
 exists2 r, r \in match_pbody (body_cl cl) i [set emptysub] &
                  sub_st r (to_sub v).
Proof.
by apply/(@match_ptl_complete emptysub); [rewrite inE| exact/subst0s].
Qed.

(** Let [ss0] be a substitution set. If [r] is in the result of extending substitutions in [ss0]
with bindings matching the [tl] atom list against the ground atoms of an interpretation [i], then
there exists a substitution [s] in [ss0] that [r] extends. *)
Lemma match_atom_all_sub tl i r ss0 :
 r \in match_pbody tl i ss0 ->
  exists2 s, s \in ss0 & sub_st s r.
Proof.
elim: tl ss0 => [| a l IHl] //=.
by rewrite /match_pbody /foldS; exists r.
rewrite /match_pbody //=.
move=> ss0. move/bindP => Hr.
case: Hr => [s Hs Hr] //.
have [s' H_in Hs'] := (IHl (match_atom_all i a s) Hr).
exists s. exact: Hs.
move/match_atomsP in H_in.
case: H_in=> [ga Hga HH].
move/esym in HH.
apply: subst_trans (match_atom_sub HH).
exact: Hs'.
Qed.

(** Let [r] in the result of extending substitutions in [ss0]
with bindings matching the [tl] atom list against the ground atoms of an interpretation [i].
Then, there exists a ground atom list [gtl], such that [gtl] is the instantiation of [t] with [r]
and all the atoms in [gtl] are in [i]. *)
Lemma match_pbody_sound tl i r ss0 :
  r \in match_pbody tl i ss0 ->
      exists2 gtl, stail tl r = [seq to_atom ga | ga <- gtl]
                   & all (mem i) gtl.
Proof.
elim: tl ss0 => [|a l IHl] /=.
  by exists [::].
move=> ss0.
case/match_pbody_cons => /= [s0 Hs0 Hrs].
have /= [gtl [H_tl H_mem]] := (IHl (match_atom_all i a s0) Hrs) => {IHl}.
have [s Hs Hsub] := match_atom_all_sub Hrs.
have/match_atomsP [ga Hga] := Hs.
exists (ga :: gtl).
rewrite H_tl //=.
move/esym in q.
move: (match_atom_sound q) => H.
have H_r := satom_sub Hsub H.
by rewrite H_r.
by rewrite /= H_mem Hga.
Qed.

(* TODO: BEGIN TO MOVE *)
(** ** Lemmas on substitutions -- added *)

(** If s is the result of matching [a] on [ga] starting with [r]
   and [v] a variable of [s] domain, then either [v] was in
   the domain of [r] or [v] was a variable of [a] *)
Lemma match_atom_dom s r a ga v : Some s = match_atom r a ga
                           -> v \in dom s
                           -> v \in atom_vars a \/ v \in dom r.
Proof.
move=>Hseq.
pose Heq:= match_atom_sound (Logic.eq_sym Hseq).
clearbody Heq.
destruct a as [[fa aa] Ha]; destruct ga as [[fga aga] Hga].
unfold satom in Heq. unfold to_atom in Heq.
inversion Heq as [[Hfeq Hargseq]]. clear Heq.
unfold match_atom in Hseq. unfold match_raw_atom in Hseq.
simpl in Hseq.
assert (Hrew:(fa == fga) && (size aa == size aga)).
 apply/andP;split.
  apply/eqP/Hfeq.
  rewrite -(size_map (sterm s)) -(size_map Val). by apply/eqP/f_equal.
rewrite Hrew in Hseq.
unfold atom_vars. simpl.
clear Ha. clear Hga.
move=> Hvindom.
move: r aa Hargseq Hrew Hseq.
induction aga as [|haga tlaga]; destruct aa as [|haa tlaa];
move=>// Hargseq Hrew Hseq.
inversion Hseq as [Hsr]. rewrite Hsr in Hvindom. by right.
inversion Hargseq as [[Hhargseq Htlargseq]].
assert (Hrewb : (fa == fga) && (size tlaa == size tlaga)).
apply/andP;split; by destruct (andP Hrew).
simpl in Hseq.
destruct haa as [haa|].
- simpl in Hhargseq. destruct (sub_elim s haa) as [[c Hc]|H].
  + rewrite Hc in Hhargseq. inversion Hhargseq as [Hceq]. simpl in Hseq.
    destruct (sub_elim r haa) as [[cb Hcb]|Hb].
    - rewrite Hcb in Hseq. destruct (@Bool.bool_dec (haga == cb) true) as [Hgagacb|Hneq].
      + rewrite Hgagacb in Hseq. destruct (IHtlaga _ tlaa Htlargseq Hrewb Hseq) as [Hraw|Hdom].
        - left. apply/raw_atom_vars_cons/Hraw.
        - by right.
      + unfold not in Hneq. assert (Hneqb: haga == cb = false). destruct (haga==cb). exfalso;apply Hneq. auto. auto.
        rewrite Hneqb foldObindNone in Hseq. inversion Hseq.
    - rewrite Hb in Hseq.
      destruct (IHtlaga _ tlaa Htlargseq Hrewb Hseq) as [Hvinraw|Hvindomadd].
      + left. apply/raw_atom_vars_cons/Hvinraw.
      + move:Hvindomadd. unfold dom. rewrite !in_set.
        unfold add. rewrite ffunE.
        destruct (@Bool.bool_dec (v == haa) true) as [Hvhaa|Hvhaaneq].
        - move=>Hf. rewrite (eqP Hvhaa). left.
          unfold raw_atom_vars. apply/bigcup_seqP. exists (Var haa).
          by rewrite in_cons;apply/orP;left. by apply/andP;split;[apply/set11|].
        - assert (Hneqb:v==haa = false). destruct(v==haa). by exfalso;apply/Hvhaaneq. auto.
          rewrite Hneqb. move=>Hf. right. apply Hf.
  + rewrite H in Hhargseq. inversion Hhargseq.
- inversion Hhargseq as [Hceq]. simpl in Hseq.
  rewrite Hceq (eq_refl haga) in Hseq.
  destruct (IHtlaga _ tlaa Htlargseq Hrewb Hseq) as [Hraw|Hdom].
  + left. apply/raw_atom_vars_cons/Hraw.
  + by right.
Qed.

(** For any [s] in the result of matching [a] on interpretation [i]
   starting with [r] and [v] a variable of [s] domain, then either [v] was in
   the domain of [r] or [v] was a variable of [a] *)
Lemma match_atom_all_dom s r i a v : s \in match_atom_all i a r
                     -> v \in dom s
                     -> v \in atom_vars a \/ v \in dom r.
Proof.
move=>/match_atomsP [ga Hgain Hgasome] Hvin.
by destruct (@match_atom_dom _ _ _ _ v Hgasome Hvin);[left|right].
Qed.

(** If [s] in the result of matching the body [tl] against [i] starting
  with [ss], then the domain of [s] is included in the union of the variables
  of [tl] and all the variables in the substitutions of [ss] *)
Lemma pmatch_subset_vars s tl i ss : s \in match_pbody tl i ss
                   -> dom s \subset ((tail_vars tl) :|: all_dom ss).
Proof.
move:s i ss.
induction tl as [|a tl].
move=>s i ss. unfold match_pbody. move => /= Hsin.
unfold tail_vars. unfold all_dom.
apply/subsetP;move=>x Hx;apply/setUP. right.
apply/bigcupP. exists s. apply Hsin. apply Hx.
move=>s i ss /match_pbody_cons [r Hred Hr].
apply/subsetP;move=>x Hx;apply/setUP.
destruct (setUP (subsetP (IHtl _ _ _ Hr) x Hx)) as [H|H].
- left. apply (tail_vars_cons _ H).
- unfold all_dom in H.
  destruct (bigcupP H) as [s0 Hs0match Hs0dom]. clear H.
  destruct (@match_atom_all_dom _ _ _ _ x Hs0match Hs0dom) as [H|H].
  left. apply/tail_vars_head/H.
  right. unfold all_dom. apply/bigcupP. by exists r.
Qed.

(** if [s] in the result of matching the body [tl] against [i], then the
  domain of [s] is included in the variables of [tl] *)
Lemma match_subset_vars s tl i : s \in match_body i tl
                -> dom s \subset tail_vars tl.
Proof.
assert (H:tail_vars tl = tail_vars tl :|: all_dom [set emptysub]).
by rewrite all_dom_empty setU0.
rewrite H. move=>Hs. apply/pmatch_subset_vars/Hs.
Qed.

(** if [s] in the result of matching the body [tl] against [i] starting from
   [ss], then there exists [s'] in [ss] smaller than [s] *)
Lemma match_pbody_sub s i tl ss : s \in match_pbody tl i ss ->
  [exists s' in ss, s' \sub s].
Proof.
move:s ss.
induction tl as [|h tl IHtl].
unfold match_pbody. move=>/= s ss H. apply/existsP. exists s.
apply/andP;auto.
move=> s ss /match_pbody_cons [sp H1 H2].
apply/existsP. exists sp. apply/andP;split;auto.
destruct (existsP (IHtl _ _ H2)) as [sp' Hsp'].
destruct (andP Hsp') as [H3 H4].
apply subst_trans with (s2 := sp');auto.
destruct (match_atomsP _ _ _ _ H3) as [ga Hgain Hgaeq].
apply (match_atom_sub (Logic.eq_sym Hgaeq)).
Qed.

(** If [s] in the matching of [a] against [i] starting from [r], then the
   variables of [a] are in the domain of [s] *)
Lemma match_atoms_vars_subset s r i a : s \in match_atom_all i a r
  -> atom_vars a \subset dom s.
Proof.
move=> /match_atomsP [ga Hgain Hgaeq].
apply/sub_dom_ga. exists ga. apply (match_atom_sound (Logic.eq_sym Hgaeq)).
Qed.

(** If [s] in the matching of body [tl] against [i] starting from set [ss],
  then the variables of the body [tl] are in the domain of [s] *)
Lemma pmatch_vars_subset s ss tl i : s \in match_pbody tl i ss
                -> tail_vars tl \subset dom s.
Proof.
move:ss. induction tl as [|h tl IHtl];move=>ss.
move=> Hmatch. unfold tail_vars. rewrite big_nil. apply sub0set.
move=> /match_pbody_cons [r Hrin Hrmatch].
apply/subsetP. move=>x /bigcup_seqP [ato Hatoin Hatomatch].
destruct (andP Hatomatch) as [Hmatch Htriv].
rewrite in_cons in Hatoin. destruct (orP Hatoin) as [Hatoh|Hatotl].

rewrite (eqP Hatoh) in Hmatch.
destruct (existsP (match_pbody_sub Hrmatch)) as [sp Hsp].
destruct (andP Hsp) as [Hspmatch Hspsub].
pose H := (subsetP (match_atoms_vars_subset Hspmatch) x Hmatch). clearbody H.
pose H2 := forallP Hspsub x. clearbody H2.
rewrite in_set in H.
destruct (sub_elim sp x) as [[c Hc]|Hc];rewrite Hc in H;auto.
rewrite Hc mem_bindE in H2. by rewrite in_set (eqP H2).

apply (subsetP (IHtl _ Hrmatch) x (tailvars_trans Hmatch Hatotl)).
Qed.

(** If [s] in the matching of body [tl] against [i],
  then the variables of the body [tl] are in the domain of [s] *)
Lemma match_vars_subset s tl i : s \in match_body i tl
                -> tail_vars tl \subset dom s.
Proof.
rewrite (match_body_pbody _ _ s) ; apply pmatch_vars_subset.
Qed.

(** Let [i] be a safe interpretation, [p] a safe program.
   Let [ga] be in the semantics of [p] starting from [i] after [m] steps and [ga]
  symbol be intensional, then there exists a clause [cl] in [p] whose head symbol is the
  head symbold of [ga], a substitution [s] for which the body of cl match with the
  (p-1) iteration of the semantics of [p] from [i] and [ga] is the result of
  applying [s] to the head of [cl]*)
Lemma ga_ded (p : program) (def : syntax.constant) (m : nat) (i : interp) ga :
  (ga \in sem p def m i) -> predtype (sym_gatom ga) = Idb -> safe_edb i -> prog_safe p ->
  exists cl, cl \in p /\ sym_gatom ga = hsym_cl cl (* redundant with last hypothesis *)
    /\ exists s, s \in match_body (sem p def m.-1 i) (body_cl cl)
      /\ to_atom ga = satom (head_cl cl) s.
Proof.
induction m as [|m Hm].
move=>Hgain Hptyp Hedb.
rewrite (eqP (implyP (forallP Hedb ga) Hgain)) in Hptyp.
inversion Hptyp.
move=>/setUP [Hnew|Hrec] Hptyp Hedb Hsafe.
destruct m as [|m].
rewrite (eqP (implyP (forallP Hedb ga) Hnew)) in Hptyp.
inversion Hptyp.
destruct (setUP Hnew) as [Hrec|Hnenw].
assert (Hgainb : ga \in sem p def m.+1 i).
apply/setUP. left. destruct m. apply Hrec. apply Hrec.
destruct (Hm Hgainb Hptyp Hedb) as [cl Hcl]. apply Hsafe.
destruct Hcl as [Hclin Hcleq].
exists cl. split. apply Hclin. destruct Hcleq as [Hsymeq Hcleqb].
split. apply Hsymeq.
destruct Hcleqb as [s Hs].
exists s.
assert (Hsmon : (sem p def m.+1.-1 i) \subset (sem p def m.+2.-1 i)).
apply sem_m_incr. destruct Hs as [Hs1 Hs2]. split.
apply/(subsetP (match_body_incr _  Hsmon) s)/Hs1. apply Hs2.
destruct (bigcup_seqP _ _ _ _ _ _ Hnenw) as [cl Hclin Hcl].
exists cl. split. apply Hclin. destruct (andP Hcl) as [H1 H2].
destruct (imsetP H1) as [s Hs Haeq]. split.
destruct ga. simpl. simpl in Haeq. unfold gr_atom_def in Haeq.
inversion Haeq as [Haeqb]. auto.
exists s.
simpl. split. apply/(subsetP (match_body_incr _ _) s)/Hs.
apply/subsetP=>x Hx. apply/setUP. left. apply Hx.
rewrite Haeq.
have Hsub := (subset_trans (allP Hsafe cl Hclin) (match_vars_subset Hs)).
apply (to_atom_satom_eq def Hsub).

destruct (bigcup_seqP _ _ _ _ _ _ Hrec) as [cl Hclin Hcl].
exists cl. split. apply Hclin. destruct (andP Hcl) as [H1 H2].
destruct (imsetP H1) as [s Hs Haeq].
split.
destruct ga. simpl. simpl in Haeq. unfold gr_atom_def in Haeq.
inversion Haeq as [Haeqb]. auto.
exists s.
simpl. split.
 apply/(subsetP (match_body_incr _ _) s)/Hs.
apply/subsetP=>x Hx. apply Hx.
rewrite Haeq.
have Hsub := (subset_trans (allP Hsafe cl Hclin) (match_vars_subset Hs)).
apply (to_atom_satom_eq def Hsub).
Qed.

(** If we apply [transub] to a clause [cl] and then take a [s] in the result
   of matching the obtained body with [i], if the domain of [transub] was
   restricted to the variables of the body of [cl], then [s] and [transub]
   have no common variable in their domain. *)
Lemma match_domsI i s transub cl : s \in match_body i (body_cl (scl transub cl))
  -> {subset (dom transub) <= tail_vars (body_cl cl)}
  -> dom s :&: dom transub = set0.
Proof.
destruct cl as [h tl].
apply (@wlist_ind atom_finType bn
(fun l => forall s, s \in match_body i (body_cl (scl transub (Clause h l))) ->
          {subset dom transub <= tail_vars (body_cl (Clause h l))} ->
dom s :&: dom transub = set0)).
move => l Pl s'.
simpl ; rewrite wmapcoK.
unfold wlist_to_seq_co ; rewrite seq_wlist_uncut_K.
clear Pl. clear tl. clear h.
rewrite !(match_body_pbody _ _ s).
move=> Hsmatch Hsub.
apply/eqP;rewrite eqEsubset;apply/andP;split;apply/subsetP;move=>x Hx.
destruct (setIP Hx) as [Hxsb Hxtransub].
pose Htailvars := subsetP (match_subset_vars Hsmatch) x Hxsb.
clearbody Htailvars.
exfalso. apply (v_in_dom_stail Hxtransub Htailvars).
by rewrite in_set0 in Hx.
Qed.

(** ** Domains and variables of elements *)
(** If applying [r] to a term [t] gives a constant, the variable of
  [t] is included in the domain [r] *)
Lemma r_dom_term d t r : sterm r t = Val d -> term_vars t \subset dom r.
Proof.
case: t => [v|c] //=; last by rewrite sub0set.
by rewrite sub1set inE; case: (r v).
Qed.

(** If applying [r] to an atom [a] gives a ground atom [ga], the variables
   of [a] are included in the domain of [r] *)
Lemma r_dom_atom a ga r : satom a r = to_atom ga -> atom_vars a \subset dom r.
Proof.
case: a ga => [[sym args] pfa] [[gsym gargs] pfg] [hs harg].
rewrite /atom_vars /= hs {pfa pfg hs}.
elim: args gargs harg => [ | a args IHa] [ | ga gargs] //=.
  by rewrite /raw_atom_vars big_nil sub0set.
by rewrite /raw_atom_vars big_cons subUset; case=> /r_dom_term -> /IHa.
Qed.

Lemma seq_inj T (x y : T) (xs ys : seq T) :
  [:: x & xs] = [:: y & ys] -> x = y /\ xs = ys.
Proof. by case. Qed.

(** If applying [r] to a list of atom [tl] gives a list of ground atom [gtl],
   the variables of [tl] are included in the domain of [r] *)
Lemma r_dom_body tl gtl r : stail tl r = [seq to_atom ga | ga <- gtl] ->
                            tail_vars tl \subset dom r.
Proof.
elim: tl gtl => [ | a arg IHa] [ | ga gargs] //=.
  by rewrite /tail_vars big_nil sub0set.
move=> hl; have [/r_dom_atom hs /IHa hha] := seq_inj hl.
by rewrite /tail_vars big_cons subUset hs hha.
Qed.

(** If [r] in the result of matching [tl] against [i], then applying
   [r] to [tl] gives a sequence of ground atoms [gtl] that are all in [i] *)
Lemma match_tl_sound tl i r :
  r \in match_body i tl ->
        exists2 gtl, stail tl r = [seq to_atom ga | ga <- gtl]
                     & all (mem i) gtl.
Proof. exact/match_pbody_sound. Qed.

(** ** Clause Consequence Soundness:
Let [cl] be a safe clause and [i] an interpretation.
If the clause consequence operator derives no new facts from [cl], then [i] is a model for [cl].*)
Lemma cons_cl_sound def cl i :
  safe_cl cl -> cons_clause def cl i \subset i -> cl_true cl i .
Proof.
move=> h_safe; rewrite /cons_clause => /subsetP h_fp v.
apply/implyP=> h_tl; apply/h_fp/imsetP=> {h_fp}.
have [r r_in_match r_sub_v] := match_tl_complete h_tl.
exists r; first by [].
case: cl h_safe h_tl r_in_match => /= hd tl h_safe h_tl r_in_match.
have [gtl Hgtl _] := match_tl_sound r_in_match.
have h_g : exists ga, satom hd r = to_atom ga.
  exact/sub_dom_ga/(subset_trans h_safe)/r_dom_body/Hgtl.
rewrite -(to_sub_gra def hd v); case: h_g => ga hga.
have h1 := (gr_atom_defP def hga).
have h_sub := satom_sub r_sub_v hga.
have h2 := (gr_atom_defP def h_sub).
by rewrite h1 h2.
Qed.

(** if [transub] domain is included in the variables of the body of a clause [cl]
and [s] in the matching of the application of [transub] to [cl] with the
interpretation [i], then the composition of [transub] and [s] is in the
matching of [cl] with [i] *)
Lemma subU_match (def : syntax.constant) s transub i cl :
   (dom transub) \subset (tail_vars (body_cl cl))
-> s \in match_body i (body_cl (scl transub cl))
-> subU transub s \in match_body i (body_cl cl).
Proof.
destruct cl as [a l].
apply (@wlist_ind atom_finType bn
(fun l => forall s,
((dom transub) \subset tail_vars (body_cl (Clause a l)))
  -> s \in match_body i (body_cl (scl transub (Clause a l))) ->
          subU transub s \in match_body i (body_cl (Clause a l)))).
move => tl Pl sb.
simpl ; rewrite wmapcoK.
unfold wlist_to_seq_co ; rewrite seq_wlist_uncut_K.
clear Pl. clear l. clear a.
move=>Hddom Hmatch.
destruct (match_tl_sound Hmatch) as [gtl Hgtleq Hgtlin].

assert (Hsbsubtlv : dom sb \subset tail_vars tl).
  apply subset_trans with (B := mem (tail_vars [seq satom a transub | a <- tl])).
  apply (match_subset_vars Hmatch). apply stail_vars_subset.

assert (Hstlb: stail [seq satom a transub | a <- tl] sb = stail tl (subU transub sb)).
  by rewrite (staileq_subU Hgtleq) Hgtleq.

rewrite Hstlb in Hgtleq.

assert (Hein : emptysub \in [set emptysub]).
  by apply/set1P.

destruct (@match_ptl_sub_complete (subU transub sb) emptysub [set emptysub] i tl gtl Hein (subst0s (subU transub sb)) Hgtleq Hgtlin)
  as [sp Hspmatch Hspsub].
rewrite (match_body_pbody _ _ sp).

pose Hsubset1 := pmatch_subset_vars Hspmatch. clearbody Hsubset1.
rewrite all_dom_empty setU0 in Hsubset1.
pose Hsubset2 := pmatch_vars_subset Hspmatch. clearbody Hsubset2.
assert (Hveq : tail_vars tl = dom sp).
  apply/eqP. rewrite eqEsubset. by apply/andP.
assert (Hdeq : tail_vars tl = dom (subU transub sb)).
  apply/eqP. rewrite eqEsubset. apply/andP;split.
  apply (r_dom_body Hgtleq).
  apply/subsetP. move=> x Hx.
  rewrite in_set in Hx. unfold subU in Hx.
  destruct (sub_elim transub x) as [[c Hc]|Hc];rewrite ffunE Hc in Hx.
  apply (subsetP Hddom). by rewrite in_set Hc.
  destruct (sub_elim sb x) as [[d Hd]|Hd]; rewrite Hd in Hx;auto.
  apply (subsetP Hsbsubtlv). by rewrite in_set Hd.

rewrite Hveq in Hdeq.
by rewrite -(subU_eq Hdeq Hspsub).
Qed.

(** ** Forward Chain Soundness:
Let [p] be a safe program and [i] an interpretation.
If [i] is the fixpoint of one iteration of forward chain, then [i] is a model for [p]. *)
Lemma fwd_chain_sound def p i :
  prog_safe p -> fwd_chain def p i = i -> prog_true p i .
Proof.
move/allP=> h_safe /setUidPl /bigcups_seqP => h_cls ?.
  by apply/allP=> ? h; apply: (cons_cl_sound (h_safe _ h)); apply: h_cls.
Qed.

(** Technical lemma: we can define a grounding of a term by applying
  a substitution [s] with a default [def], or we can complete the substitution
  to be a grounding using default [def] and apply it to [s]. In both cases, the
  result is the same *)
Lemma to_gr_sub def t s : gr_term_def def s t = gr_term (to_gr def s) t.
Proof. by case: t=> [var | val] //=; rewrite ffunE //=. Qed.

(** Same as above but on atom *)
Lemma gr_atom_defE def s a : gr_atom (to_gr def s) a = gr_atom_def def s a.
Proof.
case: a => [[s_a arg_a] pfa] //=; apply/val_inj => /=; congr RawGAtom.
elim: arg_a {pfa} => [ |t arg_a IHl] //=.
by rewrite IHl; congr cons; rewrite to_gr_sub.
Qed.

(** If applying [s] to a list of atom [tl] gives a list of ground atoms [gtl],
   and [i] contains [gtl], then [i] contains the result of applying [s] completed
   to be a grounding to [tl].
  *)
Lemma tail_mem def s tl gtl i :
 stail tl s = [seq to_atom ga | ga <- gtl] ->
 all (mem i) gtl ->
 all (mem i) [seq gr_atom (to_gr def s) x | x <- tl].
Proof.
elim: tl gtl => [ | h l] Hl gtl //= H_mem //=.
move: H_mem; case: gtl=> [ | gh gl] //.
rewrite map_cons => hss /andP[hin hmem]; have [hhd htl]:= seq_inj hss.
apply/andP; split.
  by rewrite gr_atom_defE (gr_atom_defP def hhd).
by apply/(Hl gl htl hmem).
Qed.

(** ** Clause Consequence Stability:
Let [cl] be a clause and [i] an interpretation satisfying [c].
Then, the clause consequence operator derives no new facts from [cl]. *)
Lemma cons_cl_stable def cl i : cl_true cl i -> cons_clause def cl i \subset i.
Proof.
rewrite/cl_true/cons_clause/gcl_true //= => Hclause.
rewrite sub_imset_pre.
apply/subsetP=> s /match_tl_sound [gtl Htl Hmem].
have Hcl := Hclause (to_gr def s); move/implyP in Hcl.
rewrite inE -gr_atom_defE; apply/Hcl. rewrite wmapcoK.
by apply/tail_mem; last exact: Hmem.
Qed.

(** Let [p] be a program. Any interpretation [i] that is a model of [p] is a fixpoint of one iteration of forward chain *)
Lemma fwd_chain_stable def p i : prog_true p i -> fwd_chain def p i = i.
Proof.
move=> p_true; apply/setUidPl/bigcups_seqP=> cl h_in _.
by apply/cons_cl_stable=> v; have/allP := p_true v; exact.
Qed.

(** Forward Chain reflection lemma: Given a safe program [p], an interpretation [i]
is a model of [p] iff it is a fixpoint of one iteration of forward chain. *)
Lemma fwd_chainP def p i (p_safe : prog_safe p) :
  reflect (prog_true p i) (fwd_chain def p i == i).
Proof.
apply/(iffP eqP); [exact: fwd_chain_sound | exact: fwd_chain_stable].
Qed.

(** Given a program [p] and an interpretation [i]. The symbols in the strict result (without [i]) of applying forward
chain on [p] given [i] are among the head symbols of [p]. *)
Lemma sym_pengine_subset_hsymp def p i :
  {subset sym_i ((fwd_chain def p i) :\: i) <= hsym_prog p}.
Proof.
move=> s; case/imsetP=> ga; rewrite !inE => /andP [/negbTE h].
rewrite h; case/bigcup_seqP=> cl cl_in. rewrite andbT.
by case/imsetP=> nu nu_in -> ->; apply/mapP; exists cl.
Qed.

(** ** Forward Chain Extensionality: 
If two programs [p1] and [p2] are extensionally equal, then
the output of forward chain on [p1] equals that on [p2]. *)
Lemma eq_fwd_chain def p1 p2 i :
  p1 =i p2 -> fwd_chain def p1 i = fwd_chain def p2 i.
Proof.
by move=> h; apply/setP=> ga; rewrite !inE (eq_big_idem _ _ (@setUid _) h).
Qed.

(** ** Forward Chain Decomposition: 
The result of applying forward chain on the concatenation of
programs [p1] and [p2], given an interpretation [i] equals the union of forward chain on [p1] given [i]
with forward chain on [p2] given [i]. *)
Lemma fwd_chain_cat def p1 p2 i :
  fwd_chain def (p1 ++ p2) i = fwd_chain def p1 i :|: fwd_chain def p2 i.
Proof. by apply/setP=> ga; rewrite? (big_cat, inE) orbACA orbb. Qed.


(** Let [ga] be a ground atom in the output of applying forward chain on [p], given [i].
Then, either [ga] is in [i] or its symbol among the head symbols in [p]. *)
Lemma fwd_chain_sym def pp i ga :
  (ga \in fwd_chain def pp i) ->
  (ga \in i) || (sym_gatom ga \in hsym_prog pp).
Proof.
case: (ga \in i) / boolP => [|/negbTE h] /=.
 by rewrite /fwd_chain !inE => ->.
rewrite inE h => /bigcup_seqP[cl ?].
rewrite andbT; case/imsetP=> ? ? ->.
by apply/mapP; exists cl.
Qed.

(** Let [ga] be a ground atom in the output of iterating the application of forward chain on [p],
given [i], [k] times. Then, either [ga] is in [i] or its symbol is among the head symbols in [p]. *)
Lemma iter_fwd_chain_sym def pp i ga k :
  (ga \in iter k (fwd_chain def pp) i) ->
  (ga \in i) || (sym_gatom ga \in hsym_prog pp).
Proof.
by elim: k=> [-> //|k h] /fwd_chain_sym /orP [/h|->]; rewrite ?orbT.
Qed.

(** Atom Matching Decomposition: 
Let [i1], [i2] be two interpretations,
The substitution set extending a substitution [s] with bindings matching [a]
against the union of [i1] and [i2] equals the union of the substitution set
extending [s] with bindings matching [a] against [i1] with that extending [s]
with bindings matching [a] against [i2]. *)
Lemma match_atom_allU s a i1 i2 :
  match_atom_all (i1 :|: i2) a s =
  match_atom_all i1 a s :|:
  match_atom_all i2 a s.
Proof.
apply/setP=> nu; rewrite !inE; apply/imsetP/orP.
  case=> ga; rewrite !inE; case/orP=> /mem_imset ha ->; auto.
    left. apply ha.
    right. apply ha.
by case=> /imsetP[ga] hga hnu; exists ga; rewrite ?inE ?hga ?orbT.
Qed.

(** Get the head symbols from a list of atoms *)
Definition sym_tl tl := [seq sym_atom (val x) | x <- tl].

(** Atom Matching Modularity: 
Let [i1], [i2] be two interpretations.
If the symbol of an atom [a] does not appear among those in [i2], then
extending a substitution [nu] with bindings matching [a] against the union of [i1] and [i2]
equals that of extending [nu] with bindings matching [a] against [i1]. *)
Lemma match_atom_all_strata nu a i1 i2 :
  sym_atom a \notin sym_i i2 ->
  match_atom_all (i1 :|: i2) a nu =
  match_atom_all i1 a nu.
Proof.
unfold match_atom_all. unfold opt_sub.
move=> h_dis. apply/eqP. rewrite eqEsubset.
apply/andP;split;apply/subsetP ; move => x Hx; rewrite in_set in Hx.
rewrite imsetU in Hx. destruct (setUP Hx) as [Hl|Hr].
by rewrite in_set.
assert (Hf: Some x \in [set opt_sub (match_atom nu a ga) | ga in i2] = false).
apply/imsetP=> -[ga gain /esym] /match_atom_sound /(congr1 (sym_atom \o val)) h.
by case/negP: h_dis; apply/imsetP; exists ga.
by rewrite Hf in Hr.
rewrite in_set imsetU. by apply/setUP;left.
Qed.

(** Body Matching Modularity: 
Let [tl] be an atom list and [i1], [i2] interpretations.
If the symbols in [tl] do not appear in [i2], then the result of matching [tl] against
the union of [i1] with [i2] equals the result of matching [tl] against [i1]. *)
Lemma match_body_strata tl i1 i2 :
  disjoint (mem (sym_tl tl)) (mem (sym_i i2)) ->
  match_body (i1 :|: i2) tl = match_body i1 tl.
Proof.
move=> h_dis; apply: eq_foldS => a a_in nu.
apply: match_atom_all_strata => {nu}.
rewrite disjoint_has in h_dis.
apply: contra h_dis; case/imsetP=> ga hga /= hs.
apply/hasP; exists (sym_atom a).
  by apply/mapP; exists a.
by apply/imsetP; exists ga.
Qed.

Open Scope SET.

(** ** Forward Chain Modularity: 
Let [p] be a program and [i], [ip] interpretations.
If [i] is a model for [p] and the symbols in [p] do not appear in [ip], then the
result of applying forward chain on [p], starting from the union of [i] with [ip]
adds no new facts. *)
Lemma fwd_chain_mod def pp i ip
      (h_tr : prog_true pp i)
      (h_strata : disjoint (mem (sym_prog pp)) (mem (sym_i ip))) :
  fwd_chain def pp (i :|: ip) = i :|: ip.
Proof.
have U := (fwd_chain_stable def h_tr).
rewrite /fwd_chain /cons_clause in U *.
suff E: \bigcup_(cl <- pp) ([set gr_atom_def def s (head_cl cl)
                        | s in match_body (i :|: ip) (body_cl cl)]) =
        \bigcup_(cl <- pp) ([set gr_atom_def def s (head_cl cl)
                        | s in match_body i (body_cl cl)]).
  by rewrite E -{3}U [i :|: bigop _ _ _]setUC setUAC [_ :|: i]setUC.
set f1 := bigop _ _ _.
set f2 := bigop _ _ _.
rewrite [f1]big_seq_cond [f2]big_seq_cond {f1 f2 U}.
apply: eq_bigr => cl; rewrite andbT => cl_in.
suff -> : match_body (i :|: ip) (body_cl cl) =
          match_body i (body_cl cl) by [].
apply: match_body_strata.
rewrite !disjoint_has in h_strata *.
apply: contra h_strata; case/hasP=> s hst hs.
apply/hasP; exists s; last by [].
by apply/flatten_mapP; exists cl; rewrite // inE hst orbT.
Qed.

(** Lemmas about forward chain iteration. *)
Lemma iter_fwd_chain_stable def pp i k
  (h_tr : prog_true pp i) :
  iter k (fwd_chain def pp) i = i.
Proof.
elim: k i h_tr => [|ns ihns] ci hstb //=.
by rewrite ihns // fwd_chain_stable.
Qed.

(** The iteration of [fwd_chain pp] on [i] contains [i]*)
Lemma iter_fwd_chain_subset def pp i k :
  i \subset iter k (fwd_chain def pp) i.
Proof.
elim: k => //= k ihk; rewrite (subset_trans (fwd_chain_inc i pp def)) //.
exact: fwd_chain_incr.
Qed.

(** ** Auxiliary lemmas - Added *)
(** If we start from [sp] augmented with [x -> y], then after folding [match_term]
  on [l1] and [l2] (terms and ground terms), if we succeed, [s] the result
  contains the binding [x -> y] *)

(** Starting from substitution [sp]. If [sp] binds [vat] to term [c],
   after iterating on [tlg] and [tl], the result [s] contains the same
   binding. *)
Lemma match_term_head_some s sp gat vat tlg (tl : seq term) c : Some s = foldl
      (fun (acc : option {ffun 'I_n -> option syntax.constant})
           (p : syntax.constant * term) => obind (match_term p.1 p.2) acc)
      (match_term gat (Var vat) sp) (zip tlg tl)
      -> sp vat = Some c
      -> s vat = Some c.
Proof. simpl.
move:tl s sp.
induction tlg as [|htlg tltlg];move=> [|htl tltl] s sp //=;
destruct (sub_elim sp vat) as [[spc H]|H];rewrite H;move=>//.
destruct (bool_des_rew (gat == spc)) as [Hb|Hb];rewrite Hb;move=>//.
move=>[H1] [H2]. by rewrite H1 H H2.
destruct (bool_des_rew (gat == spc)) as [Hb|Hb];rewrite Hb.
move=>[H1] [H2]. by rewrite H1 H H2.
move=>//.
destruct (bool_des_rew (gat == spc)) as [Hb|Hb];rewrite Hb.
move=>[H1] [H2]. by rewrite H1 H H2.
move=>//.
destruct (bool_des_rew (gat == spc)) as [Hb|Hb];rewrite Hb.
unfold match_term. destruct htl as [vhtl|chtl].
 (* htl = Var vhtl *)
- simpl. destruct (sub_elim sp vhtl) as [[sphtl Hsphtl]|Hsphtl];rewrite Hsphtl.
  (* sp vhtl = Some sphtl *)
  + destruct (bool_des_rew (htlg == sphtl)) as [Heq|Heq];rewrite Heq.
    (* htlg = sphtl (ground heads match) *)
    - move=>Hseq [Hspcc]. apply IHtltlg with (tl := tltl) (sp := sp).
      rewrite H Hb. apply Hseq. by rewrite -Hspcc.
    (* htlg <> sphtl (ground heads don't match) *)
    - by rewrite foldObindNone.
  (* sp vhtl = None *)
  + move=> Hseq [Hspcc].
    destruct (bool_des_rew (vat == vhtl)) as [Hvatvhtl|Hvatvhtl].
    (* vat = vhtl *)
    - rewrite -(eqP Hvatvhtl) H in Hsphtl. inversion Hsphtl.
    (* vat <> vhtl *)
    - apply IHtltlg with (tl := tltl) (sp := (add sp vhtl htlg)).
      unfold add. rewrite !ffunE Hvatvhtl H Hb.
      apply Hseq. rewrite ffunE Hvatvhtl -Hspcc. apply H.
 (* htl = Val chtl *)
- destruct (bool_des_rew (htlg == chtl)) as [Heq|Heq];rewrite Heq.
  + move=> /= Hseq [Hsvat]. apply  IHtltlg with (tl := tltl) (sp := sp).
    rewrite H Hb. apply Hseq. rewrite -Hsvat. apply H.
  + by rewrite foldObindNone.
by rewrite foldObindNone.
Qed.

Lemma fold_add_mapsto s sp x y l1 l2 : Some s =
      foldl (fun (acc : option {ffun 'I_n -> option syntax.constant})
           (p : syntax.constant * term) => obind (match_term p.1 p.2) acc)
        (Some (add sp x y))
        (zip l1 l2)
    -> s x = Some y.
Proof.
move=>Heq. destruct (foldl_0 (Logic.eq_sym Heq)) as [spp Hspp Hsppsub].
inversion Hspp as [Hsspeq]. rewrite -Hsspeq in Hsppsub.
pose Hsub:= (forallP Hsppsub x). clearbody Hsub.
rewrite addE mem_bindE in Hsub. apply/eqP/Hsub.
Qed.

(** Let [t2] be a set of vars, [t1] its complement,
  Let [x] be the substitution
  matching [a] with [ga] that extends [sp], let [s] be an extension of [x], if
  we substitute the restriction of [s] to [t1] in [a] and match the result with
  [ga] starting from [sp] restricted to [t2], then the substitution we obtain
  is [x] restricted to [t2]. In other word the binding of variables added by [s] that were
  outside [t2] do not influence the matching. *)
  (* TODO replace sub_st, try to eliminate t1 earlier. *)
Lemma only_untyped_match x s sp a ga (t1 t2 : {set 'I_n}) :
  [disjoint t1 & t2] -> [forall y, ((y \in t1) || (y \in t2))] ->
   sub_st x s -> sub_st sp s -> Some x = match_atom sp a ga
-> Some (sub_filter x t2) = match_atom (sub_filter sp t2) (satom a (sub_filter s t1)) ga.
Proof.
destruct ga as [[fga gaargs] Hga].
destruct a as [[fa aargs] Ha].
unfold match_atom.
simpl.
destruct (bool_des_rew ((fa == fga) && (size aargs == size gaargs))) as [Hrew|Hrew];
rewrite Hrew ?foldObindNone //.
assert (Hrewb : (fa == fga) && (size [seq sterm (sub_filter s t1) x0 | x0 <- aargs] == size gaargs)).
by apply/andP;split; [|rewrite size_map] ; destruct (andP Hrew).
rewrite Hrewb.
clear Ha. clear Hga.
move:gaargs Hrew Hrewb sp x.
induction aargs as [|haargs tlaargs];destruct gaargs as [|hgaargs tlgaars];
try (by move=> /andP [Hf1 Hf2]);move=>Hrew Hrewb sp x Hdisj Hcomp Hxs Hsps /=.
- by move => [->].
- unfold match_term at 2. unfold match_term at 3.
  destruct haargs as [vh|vc].
  (* haargs = Var vh *)
  + unfold sterm.
    destruct (bool_des_rew (vh \in t1)) as [Hvtyped|Hvuntyped].
    (* vh typed: it was instiated by (only_typed p s) in a *)
    - rewrite !ffunE !Hvtyped.
      destruct (sub_elim s vh) as [[svhc Hsvhc]|Hsvhc];rewrite !Hsvhc.
      (* s vh = svhc. Let's now see if it is equal to the head of ga *)
      + destruct (bool_des_rew (hgaargs == svhc)) as [Hhgsvhc|Hhgsvhc];
        rewrite Hhgsvhc.
        (* heads match, let's see if vh is new in sp *)
        - destruct (sub_elim sp vh) as [[vhc Hvhc]|Hvhc];rewrite !Hvhc.
          (* vh already captured by sp as vhc *)
          + destruct (bool_des_rew (hgaargs == vhc)) as [Hhgavhc|Hhgavhc];
            rewrite Hhgavhc.
            - apply IHtlaargs;auto.
            + by rewrite foldObindNone.
          (* sp vh = None. In x, sp is extended to capture the corresponding
             constant in ga. Since it is instianciated in satom a, it is not
             captured in the conclusion's match atom, corresponding to the
             fact that vh is typed and the computed subst is only_untyped   *)
          + move=>H.
            rewrite (@add_typed_untyped vh t1 t2 hgaargs sp Hvtyped Hdisj).
            apply IHtlaargs;auto. apply/forallP. move=>v.
            rewrite ffunE. destruct (bool_des_rew (v == vh)) as [Heq|Heq];rewrite Heq.
            rewrite mem_bindE (eqP Heq) (eqP Hhgsvhc). apply/eqP/Hsvhc.
            destruct (sub_elim sp v) as [[c Hc]|Hc];rewrite Hc.
            pose Hsub:= (forallP Hsps v). clearbody Hsub. by rewrite Hc in Hsub. auto.
        (* they don't *)
        - destruct (sub_elim sp vh) as [[vhc Hvhc]|Hvhc];rewrite !Hvhc.
          (* sp vh = vhc *)
          + destruct (bool_des_rew (hgaargs == vhc)) as [Hhvhc|Hhvhc].
            - pose Hsub := forallP Hsps vh. clearbody Hsub.
              rewrite Hvhc mem_bindE in Hsub. rewrite -(eqP Hhvhc) Hsvhc in Hsub.
              pose Hsubb := eqP Hsub. inversion Hsubb as [Heq]. by rewrite Heq eq_refl in Hhgsvhc.
            - by rewrite Hhvhc foldObindNone.
          (* sp vh = None *)
          + move=>H.
            pose Hf:= (forallP Hxs vh). clearbody Hf.
            rewrite (fold_add_mapsto H) mem_bindE Hsvhc in Hf.
            move:Hf. move=> /eqP [Hf].
            by rewrite Hf eq_refl in Hhgsvhc.
      (* s vh = None: no change *)
      + destruct (sub_elim sp vh) as [[vhc Hvhc]|Hvhc];rewrite !Hvhc.
          (* sp vh = vhc *)
        - pose Hf:= (forallP Hsps vh). clearbody Hf.
          rewrite Hvhc mem_bindE Hsvhc in Hf. inversion Hf.
          (* sp vh = None *)
        - move=>H.
          pose Hsub := forallP Hxs vh. clearbody Hsub.
          rewrite (fold_add_mapsto H) mem_bindE Hsvhc in Hsub.
          pose Hssub := eqP Hsub. inversion Hssub.
     (* vh not typed *)
    - rewrite !ffunE !Hvuntyped.
      + destruct (sub_elim sp vh) as [[vhc Hvhc]|Hvhc];rewrite !Hvhc.
        (* sp vh = vhc *)
        - rewrite ffunE Hvhc.
          destruct (bool_des_rew (vh \in t2)) as [Hvh2|Hvh2]; rewrite Hvh2.
          + destruct (bool_des_rew (hgaargs == vhc)) as [Hhgavhc|Hhgavhc];
            rewrite !Hhgavhc.
            - apply IHtlaargs;auto.
            - by rewrite foldObindNone.
          + destruct (orP (forallP Hcomp vh)) as [Hf|Hf].
            by rewrite Hf in Hvuntyped. by rewrite Hf in Hvh2.
        (* sp vh = None *)
        - rewrite ffunE Hvhc. move=>H. have Hxvh := fold_add_mapsto H. move: H.

          destruct (bool_des_rew (vh \in t2)) as [Hvh2|Hvh2]; rewrite Hvh2.
          + simpl. rewrite (add_untyped_untyped hgaargs sp Hvh2).
          apply IHtlaargs;auto. apply/forallP. move=>v.
            rewrite ffunE. destruct (bool_des_rew (v == vh)) as [Heq|Heq];rewrite Heq.
            pose Hsub := forallP Hxs vh. clearbody Hsub. by rewrite Hxvh -(eqP Heq) in Hsub.
            destruct (sub_elim sp v) as [[c Hc]|Hc];rewrite Hc;auto.
            pose Hsub := forallP Hsps v. clearbody Hsub. by rewrite Hc in Hsub.
            destruct (orP (forallP Hcomp vh)) as [Hf|Hf].
            by rewrite Hf in Hvuntyped. by rewrite Hf in Hvh2.
          (* s vh = None: contradiction with Hxs *)
  (* haargs = Val vc *)
  + destruct (bool_des_rew (hgaargs == vc)) as [Hhgavc|Hhgavc];simpl;
    rewrite !Hhgavc.
    - apply IHtlaargs;auto.
    - by rewrite foldObindNone.
Qed.

(** Let [t2] be a set of vars, [t1] its complement, [s] be a substitution matching
 the body [l] with [i] starting from [ss1].
  Let [ss1] and [ss2] be set of substitution, such that any restriction of [s]
  in [ss1] verifies that its restriction to [t2] is in [ss2].
  Then matching the body resulting from subsituting the restriction of [s]
  to [t1] in [l], on [i] starting from [ss2] contains the same restriction of
  [s] to [t2] *)
Lemma untyped_in_scl_match_pbody l i s (t1 t2 : {set 'I_n}) (ss1 ss2 : {set sub}) :
     [forall s' in ss1, (s' \sub s) ==> ((sub_filter s' t2) \in (pred_of_set ss2))]
  -> s \in match_pbody l i ss1 -> [forall y, ((y \in t1) || (y \in t2))] -> [disjoint t1 & t2]
  -> (sub_filter s t2) \in match_pbody [seq satom a (sub_filter s t1) | a <- l] i ss2.
Proof.
move: i s ss1 ss2. induction l as [|lh ll].

move => i s ss1 ss2 Hall Hsmatch Hcomp Hdisj.
unfold match_pbody in Hsmatch. simpl in Hsmatch.
by apply (implyP (implyP (forallP Hall s) Hsmatch)).

move => i s ss1 ss2 Hall /match_pbody_cons [sp Hspinss Hsmatchsp] Hcomp Hdisj.
apply/match_pbody_cons.
exists (sub_filter sp t2).
apply/(implyP (implyP (forallP Hall sp) Hspinss))/match_atoms_pbody/Hsmatchsp.

apply IHll with (ss1 := (match_atom_all i lh sp));auto.

apply/forallP. move=>s'. apply/implyP. move=>/match_atomsP [ga Hgain Hgaeq].
apply/implyP. move=>Hssub. apply/match_atomsP. exists ga. apply Hgain.
apply only_untyped_match;auto. apply/match_atoms_pbody/Hsmatchsp.
Qed.

(**  Let [t2] be a set of vars, [t1] its complement, [s] be a substitution matching
 the body of clause [cl] with [i].
  Then matching the body resulting from subsituting the restriction of [s]
  to [t1] in [cl], on [i] contains the restriction of
  [s] to [t2] *)
Lemma untyped_in_scl_match_body cl i (t1 t2 : {set 'I_n}) : forall s, s \in match_body i (body_cl cl) ->
              [disjoint t1 & t2] -> [forall y, ((y \in t1) || (y \in t2))]
      -> (sub_filter s t2) \in match_body i (body_cl (scl (sub_filter s t1) cl)).
Proof.
destruct cl as [h tl]. simpl.
apply (@wlist_ind atom_finType bn
(fun l => forall s : {ffun 'I_n -> option syntax.constant},
s \in match_body i l ->
[disjoint t1 & t2] -> [forall y, ((y \in t1) || (y \in t2))] ->
sub_filter s t2 \in match_body i (wmap (satom^~ (sub_filter s t1)) l))).
move => l Pl s.
simpl ; rewrite wmapcoK.
unfold wlist_to_seq_co ; rewrite seq_wlist_uncut_K.
clear Pl. clear tl. clear h.
rewrite !(match_body_pbody _ _ s).
move=>H1 H2 H3.
apply/(untyped_in_scl_match_pbody _ H1).
apply/forallP=>x. apply/implyP=>/set1P ->.
apply/implyP. move=>H. rewrite utemptysub. apply/set11.
apply H3. apply H2.
Qed.

(** ** Correspondence between constructive and boolean matches -- added *)
(** If [s] in the result of matching the body of [cl] with [i], then [bmatch def i cl s]
succeeds *)
Lemma match_body_bmatch def (cl : clause) i s :
  s \in match_body i (body_cl cl) -> bmatch def i cl s.
Proof.
move=>H.
unfold bmatch.
rewrite (match_vars_subset H).
move:H.
move=>/match_tl_sound [gtl Hseq Hallin].
move:cl Hseq.
destruct cl as [hcl tlcl]. simpl.
apply (@wlist_ind atom_finType bn
(fun tltl => stail tltl s = [seq to_atom ga | ga <- gtl] ->
all (mem i) (wmap (gr_atom (to_gr def s)) tltl))).
move => l Pl. unfold wlist_to_seq_co. rewrite wmapK !seq_wlist_uncut_K.
clear Pl.

move:l.
induction gtl as [|hgtl tlgtl Hrec];
move=>[|htl tltl] //= [H1 H2 H3].
destruct (andP Hallin) as [Hin1 Hin2].
apply/andP;split.
clear Hallin.
assert (Heq : satom htl s = to_atom hgtl).
destruct htl as [phtl ahtl]. apply/val_inj.
simpl in *. unfold sraw_atom. unfold to_raw_atom.
by rewrite H1 H2.
rewrite gr_atom_defE (gr_atom_defP def Heq). apply Hin1.
apply Hrec. apply Hin2. apply H3.
Qed.

(** If [bmatch def i cl s] succeeds, then there is a substitution [r] smaller than [s]
   in the result of matching the body of [cl] with [i] *)
Lemma bmatch_match_body def (cl : clause) i s:
  bmatch def i cl s ->
        exists2 r : sub,
         r \in match_body i (body_cl cl) & r \sub s.
Proof.
assert (H1 : emptysub \in [set emptysub]).
by apply/set1P. unfold bmatch.
destruct (bool_des_rew (cl_vars cl \subset dom s)) as [H2|H2];
rewrite H2;
move=>H3.
destruct (match_ptl_complete H1 (subst0s (to_sub (to_gr def s))) H3)
  as [r Hr].
exists r. apply Hr.
assert (Hdom : dom r \subset dom s).
apply/subset_trans. apply (pmatch_subset_vars Hr).
rewrite all_dom_empty setU0.
apply H2.
unfold sub_st. unfold sub_st in H.
apply/forallP=>v.
have H4 := forallP H v.
destruct (sub_elim r v) as [[c Hc]|Hc];
rewrite Hc; rewrite Hc in H4;auto.
rewrite mem_bindE. rewrite mem_bindE in H4.
rewrite -(eqP H4).
simpl.
apply/eqP/dom_sub_grE.
assert (Hv : v \in dom r).
by rewrite in_set Hc.
apply/(subset_to_in Hv Hdom).
inversion H3.
Qed.

End Soundness.
