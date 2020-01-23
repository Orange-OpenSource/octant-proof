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

(** This is the first part of the original file "pengine.v" with some modifications 
    by Pierre-Léo Bégay *)

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype.
From mathcomp
Require Import tuple finset bigop finfun.

Require Import bigop_aux.
Require Import utils.
(** Added *)
Require Import finseqs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Standard Datalog in Coq

We define the *syntax* and *model-theoretic semantics*, as well as a bottom-up fixpoint evaluation
engine, for standard Datalog. The syntactic primitives of the language are terms (constants or variables),
atoms, clauses and programs. Semantically, *interpretations* (ground atom sets) are the main building blocks.
The bottom-up engine iteratively extends an initial seed substitution into one that matches all clause body atoms to an
existing interpretations (candidate model) and provably grounds the corresponding clause head, i.e, instantiates all of
its variables. To ease the proof-engineering effort, we distinguish between ground and non-ground constructs.
As such, we define corresponding separate types, both for the language primitives and for substitutions (we call
grounding substitutions "groundings"). *)

(** maximal number of program variables *)
Parameter n : nat.

(** program signature: constants and symbols as finite types and arities as finitely-supported functions *)
Parameter constype : finType.
Parameter symtype : finType.
Parameter arity : {ffun symtype -> nat}.

(** ** Hypothesis added for the development *)
(** max size for rule bodies *)
Parameter bn : nat.

(** ** Predicate kinds *)
(** Kind of a predicate. A predicate is either extensional or intensional *)
Inductive pred_type := Edb | Idb.

(** Decidable equality on pred kind *)
Definition pred_type_eq (x y : pred_type) := match x,y with
  | Edb,Edb | Idb,Idb => true
  | _,_ => false end.

(** pred_type_eq is an equality *)
Lemma pred_type_eq_axiom : Equality.axiom pred_type_eq.
Proof.
by case ; case ; apply Bool.iff_reflect ; split.
Qed.

(** From which we derive an Equality mixin *)
Definition pred_type_eqMixin := EqMixin pred_type_eq_axiom.

Canonical pred_type_eqType := Eval hnf in EqType pred_type pred_type_eqMixin.

(** Predicate symbols have a kind *)
Parameter predtype : {ffun symtype -> pred_type}.

(** ** Constants *)
(** A constant *)
Inductive constant := C of constype.
(** Extract the value of a constant*)
Definition of_constant c := let: C c := c in c.

(** instances for the type of constants *)
Canonical cons_subType := Eval hnf in [newType for of_constant].
Canonical cons_eqType := Eval hnf in EqType _ [eqMixin of constant by <: ].
Canonical cons_choiceType := Eval hnf in ChoiceType _ [choiceMixin of constant by <:].
Canonical cons_countType := Eval hnf in CountType _ [countMixin of constant by <:].
Canonical cons_subCountType := Eval hnf in [subCountType of constant].
Canonical cons_finType := Eval hnf in FinType _ [finMixin of constant by <:].
Canonical cons_subFinType := Eval hnf in [subFinType of constant].
Canonical cons_optionFinType := option_finType cons_finType.

Coercion opt_constant (c : option constant) : (option_finType cons_finType) := c.

(** ** Ground raw atoms *)
(** "raw" ground atoms pack a symbol and an argument list of constants *)
Inductive raw_gatom := RawGAtom of symtype & seq constant.

(** extractors for the corresponding symbols and arguments of a "raw" ground atom *)
Definition sym_gatom ga := let: RawGAtom s_ga _ := ga in s_ga.
Definition arg_gatom ga := let: RawGAtom _ arg_ga := ga in arg_ga.

Lemma gatom_eta ga : ga = RawGAtom (sym_gatom ga) (arg_gatom ga).
Proof. by case: ga. Qed.

(** *** Ground Atom Instances *)
(** Ground raw atoms are a finite type *)
Section RawGAtomInstances.

(** packing and unpacking of a "raw" ground atom; needed for the canonical inference of its instances *)
Definition raw_gatom_rep l := let: RawGAtom s a := l in (s, a).
Definition raw_gatom_pre l := let: (s, a) := l in RawGAtom s a.

(** cancelation lemma for "raw" ground atoms *)
Lemma raw_gatom_repK : cancel raw_gatom_rep raw_gatom_pre.
Proof. by case. Qed.

(** "raw" ground atom instances *)
Canonical raw_gatom_eqType :=
  Eval hnf in EqType raw_gatom (CanEqMixin raw_gatom_repK).

Canonical raw_gatom_choiceType :=
  Eval hnf in ChoiceType raw_gatom (CanChoiceMixin raw_gatom_repK).

Canonical raw_gatom_countType :=
  Eval hnf in CountType raw_gatom (CanCountMixin raw_gatom_repK).

End RawGAtomInstances.

(** ** Ground Atoms:
A ground atom [gatom] packs a "raw" ground atom and a boolean well-formedness condition *)

(** ground atom well-formedness condition: argument size and symbol arity have to match *)
Definition wf_gatom ga := size (arg_gatom ga) == arity (sym_gatom ga).

(** ground atom record *)
Structure gatom : Type := GAtom {uga :> raw_gatom; _ : wf_gatom uga}.

(** ground atom instances *)
Canonical gatom_subType := Eval hnf in [subType for uga].
Canonical gatom_eqType := Eval hnf in EqType _ [eqMixin of gatom by <:].
Canonical gatom_choiceType := Eval hnf in ChoiceType _ [choiceMixin of gatom by <:].
Canonical gatom_countType := Eval hnf in CountType _ [countMixin of gatom by <:].
Canonical gatom_subCountType := Eval hnf in [subCountType of gatom].

(** Gives back the arguments of the atom as a tuple of the right length
   using the well formedness constraint *)
Definition arg_wf_gatom (a : gatom) : ((arity (sym_gatom a)).-tuple constant).
destruct a as [a Ha]. simpl.
rewrite <- (eqP Ha).
apply (in_tuple (arg_gatom a)).
Defined.

(** Given an i smaller than the arity gives back the ith argument *)
Definition nth_cons (a : gatom) (i : 'I_(arity (sym_gatom a))) : constant :=
  tnth (arg_wf_gatom a) i.

(** maximal symbol arity *)
Notation max_ar := (\max_(s in symtype) arity s).

Lemma max_ar_bound y : arity y < max_ar.+1.
Proof. exact/leq_bigmax_cond. Qed.

(** Ground atoms are a finite type (uses the max arity) *)
Section GatomFinType.

(** corresponding finite type for ground atoms, packing a symbol type and a tuple of constants
    of length bounded by the maximal symbol arity *)
Notation gatom_enc := ({x : 'I_(max_ar.+1) & (symtype * x.-tuple constant)%type}).

(** injecting a ground atom [ga] into its corresponding finite type encoding [gatom_enc] *)
Definition gatom_fenc (ga : gatom) : gatom_enc :=
  let: GAtom ga proof := ga in

  existT _ (Ordinal (max_ar_bound (sym_gatom ga))) (sym_gatom ga, Tuple proof).

(** conversely converting a ground atom finite type encoding [gatom_enc] into a ground atom [gatom] *)
Definition fenc_gatom (e : gatom_enc): option gatom.
case: e => x [s]; case: (val x == arity s) / eqP => [-> | _] [tup proof];
[exact: (Some (@GAtom (RawGAtom s tup) proof)) | exact/None].
Defined.
(** partial cancelation lemma for ground atoms *)
Lemma fenc_gatomK : pcancel gatom_fenc fenc_gatom.
Proof. by case=> [[s args] proof] /=; case: eqP => // ?; rewrite !eq_axiomK. Qed.

End GatomFinType.

(** canonical instances for ground atoms *)
Canonical gatom_finType := Eval hnf in FinType gatom (PcanFinMixin fenc_gatomK).
Canonical gatom_subFinType := [subFinType of gatom].

(** ** Ground Clauses:
A ground clause [gclause] packs a ground atom head and a body list of ground atoms *)
(** *Important:* Our definition differs from the original one to keep a bound on the size of bodies *)
Inductive gclause := GClause of gatom & wlistn_finType gatom_finType bn.

(** head and body extractors for ground clauses *)
Definition head_gcl gcl := let: GClause h b := gcl in h.
Definition body_gcl gcl := let: GClause h b := gcl in b.

(** ** Canonical instances for ground clauses (Added) *)
(** Boolean equality on clauses *)
Definition gclause_eq gcl1 gcl2 := match gcl1,gcl2 with
  | GClause h1 l1, GClause h2 l2 => (h1 == h2) && (l1 == l2) end.

Lemma gclause_eq_refl gcl : gclause_eq gcl gcl.
Proof.
case:gcl.
move => g l /=.
by apply/andP.
Qed.

(** This is indeed an equality for clauses *)
Lemma gclause_eq_inv gcl1 gcl2 : gclause_eq gcl1 gcl2 -> gcl1 = gcl2.
Proof.
case:gcl1. case: gcl2.
move => g l g2 l2 /= /andP [Heqg Heql].
by rewrite (eqP Heqg) (eqP Heql).
Qed.

Lemma gclause_eq_axiom : Equality.axiom gclause_eq.
Proof.
move => x y; apply Bool.iff_reflect.
split.
  - move => -> ; apply/gclause_eq_refl.
  - apply gclause_eq_inv.
Qed.

Definition gclause_eqMixin := EqMixin gclause_eq_axiom.

(** Definition of the equality type *)
Canonical gclause_eqType := Eval hnf in EqType _ gclause_eqMixin.

(** Projection of the clause to a pair head, body list *)
Definition gclause_rep cl := let: GClause hd bd := cl in (hd, bd).
Definition gclause_pre cl := let: (hd, bd) := cl in GClause hd bd.

Lemma gclause_repK : cancel gclause_rep gclause_pre.
Proof. by case. Qed.

Canonical gclause_choiceType := Eval hnf in ChoiceType gclause (CanChoiceMixin gclause_repK).
Canonical gclause_countType := Eval hnf in CountType gclause (CanCountMixin gclause_repK).
Canonical gclause_finType := Eval hnf in FinType gclause (CanFinMixin gclause_repK).

(** ** Interpretation *)
(** interpretations are finite sets of ground atoms *)
Notation interp := {set gatom}.

Implicit Types (i m : interp) (gcl : gclause).

(** set of all symbols of a given interpretation *)
Definition sym_i (i : interp) := [set sym_gatom (uga ga) | ga in i].

(** satisfiability of a ground clause [gcl] w.r.t a given interpretation [i]:
    if all body atoms belong to [i], the head should also belong to [i] *)
Definition gcl_true gcl i :=
  all (mem i) (body_gcl gcl) ==> (head_gcl gcl \in i).

(** ** Terms *)
(** Terms are either
    - variables, i.e, integers bound by a maximal (computable) index [n]
      - to which we assign the _finite_ ordinal type ['I_n]
    - constants to which we assign the _finite_ [constype]
*)
Inductive term : Type :=
  | Var of 'I_n
  | Val of constant.

(** Injection of constants in terms *)
Definition term_of_cons (c : constant) : term := Val c.

(** corresponding sigma type encoding for terms; needed for canonical instance inference *)
Notation termRep := ('I_n + constant)%type.

(** injecting a term [t] into its [termRep] encoding *)
Definition term_rep (t : term) : termRep :=
  match t with
  | Var i => inl i
  | Val c => inr c
  end.

(** converting a [termRep] encoding into the corresponding term type  *)
Definition term_con (r : termRep) : term :=
  match r with
  | inl i => Var i
  | inr c => Val c
  end.

(** cancelation lemma for terms *)
Lemma term_repK : cancel term_rep term_con.
Proof. by case. Qed.

(** canonical instances for terms *)
Canonical term_eqType := Eval hnf in EqType term (CanEqMixin term_repK).
Canonical term_choiceType := Eval hnf in ChoiceType term (CanChoiceMixin term_repK).

Canonical term_countType := Eval hnf in CountType term (CanCountMixin term_repK).
Canonical term_finType := Eval hnf in FinType term (CanFinMixin term_repK).

(** ** Raw atoms *)
(** Atoms are represented as records packing:
   - a base type [raw_atom]
     - which pairs a symbol with its term list argument
   - a _boolean_ well-formedness condition [wf_atom]
     - which ensures symbol arity and argument size agree *)
Inductive raw_atom : Type := RawAtom of symtype & seq term.

(** Inject raw ground atoms in raw atoms*)
Definition to_raw_atom gra :=
  RawAtom (sym_gatom gra) [seq Val x | x <- arg_gatom gra].

Section RawAtomInstances.

(** packing and unpacking of raw atoms *)
Definition raw_atom_rep l := let: RawAtom s a := l in (s, a).
Definition raw_atom_pre l := let: (s, a) := l in RawAtom s a.

(** cancelation lemma for raw atoms *)
Lemma raw_atom_repK : cancel raw_atom_rep raw_atom_pre.
Proof. by case. Qed.

(** canonical instances for raw atoms *)
Canonical raw_atom_eqType := Eval hnf in EqType raw_atom (CanEqMixin raw_atom_repK).
Canonical raw_atom_choiceType := Eval hnf in ChoiceType raw_atom (CanChoiceMixin raw_atom_repK).

(*
Canonical raw_atom_choiceType := Eval hnf in ChoiceType raw_atom
  (@CanChoiceMixin (prod_choiceType symtype (seq_choiceType term_choiceType)) _ _ _ raw_atom_repK).
*)

Canonical raw_atom_countType :=
  Eval hnf in CountType raw_atom (@CanCountMixin (prod_countType symtype (seq_countType term_finType)) _ _ _ raw_atom_repK).

End RawAtomInstances.

(** extractors for the corresponding symbols and arguments of an atom *)
Definition sym_atom a := let: RawAtom s_a _ := a in s_a.
Definition arg_atom a := let: RawAtom _ arg_a := a in arg_a.

(** ** Atoms *)
(** atom well-formedness condition: argument size and symbol arity must match *)
Definition wf_atom a := size (arg_atom a) == arity (sym_atom a).

(** ** Atoms are records packing a "raw" atom and a corresponding boolean well-formedness condition *)
Structure atom : Type := Atom {ua :> raw_atom; _ : wf_atom ua}.

(** *** A few useful lemmas and auxiliary functions *)
(** Preservation of well formedness by the translation to raw atom *)
Lemma to_atom_proof (ga : gatom) : wf_atom (to_raw_atom ga).
Proof. by case: ga => ra pf; rewrite /wf_atom /= size_map. Qed.

(** Translates ground atom to atom using lemma above *)
Definition to_atom ga := Atom (to_atom_proof ga).

(** Extract the args as a tuple from an atom *)
Definition arg_wf_atom (a : atom) : ((arity (sym_atom a)).-tuple term).
destruct a as [a Ha]. simpl.
rewrite <- (eqP Ha).
apply (in_tuple (arg_atom a)).
Defined.

(** Given an atom and i smaller than the arity, gets the ith arg *)
Definition nth_term (a : atom) (i : 'I_(arity (sym_atom a))) : term :=
  tnth (arg_wf_atom a) i.

(** Given a predicate and a ground atom having this pred, access one
   argument of this ground atom (using dependent type on arity) *)
Definition nth_cons_rew_dep pred (ga : {x : gatom | sym_gatom x == pred}) (i : 'I_(arity pred)) : constant.
destruct ga as [ga Hga].
rewrite <- (eqP Hga) in i.
apply (@nth_cons ga i).
Defined.

(** We can access the ith argument of an atom with predicate whose
  arity is greater than i *)
Lemma oob_atom_args (a : atom) (ind : 'I_(arity (sym_atom a))) : nth_error (arg_atom a) ind <> None.
Proof.
destruct a as [[f args] Hwf].
unfold wf_atom in Hwf. move:ind.
rewrite -(eqP Hwf).
apply oob_nth_error.
Qed.

(** atom instances *)
Canonical atom_subType := Eval hnf in [subType for ua].
Canonical atom_eqType := Eval hnf in EqType _ [eqMixin of atom by <: ].
Canonical atom_choiceType := Eval hnf in ChoiceType _ [choiceMixin of atom by <:].

Canonical atom_countType := Eval hnf in CountType _ [countMixin of atom by <:].

(** *** Atoms are a finite type *)
Section AtomFinType.

(** We use as represention the triple size (smaller than max_r) symbol and tuples of terms of size the first *)
Notation atom_enc := ({x : 'I_(max_ar.+1) & (symtype * x.-tuple term_finType)%type}).

(** We can inject atom in this encoding *)
Definition atom_fenc (a : atom) : atom_enc :=
  let: Atom a proof := a in
  existT _ (Ordinal (max_ar_bound (sym_atom a))) (sym_atom a, Tuple proof).

(** We can invert this encoding as long as we respect arity *)
Definition fenc_atom (e : atom_enc): option atom.
case: e => x [s]; case: (val x == arity s) / eqP => [-> | _] [tup proof];
[exact: (Some (@Atom (RawAtom s tup) proof)) | exact/None].
Defined.

(** This is a true injection *)
Lemma fenc_atomK : pcancel atom_fenc fenc_atom.
Proof. by case=> [[s args] proof] /=; case: eqP => // ?; rewrite !eq_axiomK. Qed.

End AtomFinType.
Canonical atom_finType := Eval hnf in FinType atom (PcanFinMixin fenc_atomK).
Canonical atom_subFinType := [subFinType of atom].

(** ** Clauses and programs *)
(** A list of size at most n of atoms (for the body) *)
Definition tail := wlistn_finType atom_finType bn.

(** A clause pack an atom head and a list of at most size n of atoms.
  Our definition differs from the original one *)
Inductive clause : Type := Clause of atom & tail.

Section ClauseInstances.

(** packing and unpacking of clauses *)
Definition clause_rep cl := let: Clause hd bd := cl in (hd, bd).
Definition clause_pre cl := let: (hd, bd) := cl in Clause hd bd.

(** cancelation lemma for clauses *)
Lemma clause_repK : cancel clause_rep clause_pre.
Proof. by case. Qed.

(** clause instances *)
Canonical clause_eqType := Eval hnf in EqType clause (CanEqMixin clause_repK).
Canonical clause_choiceType := Eval hnf in ChoiceType clause (CanChoiceMixin clause_repK).

(** Added instances using the bound on the size of the body *)
Canonical clause_countType := Eval hnf in CountType clause (CanCountMixin clause_repK).
Canonical clause_finType := Eval hnf in FinType clause (CanFinMixin clause_repK).

End ClauseInstances.

(** ** Programs are clause lists. *)
Definition program := seq clause.

(** extractors for the corresponding head, body and atoms of a clause *)
Definition head_cl cl := let: Clause h b := cl in h.
Definition body_cl cl := let: Clause h b := cl in b.
Definition atoms_cl cl := [:: head_cl cl & body_cl cl].

(** clause head symbols *)
Definition hsym_cl cl := sym_atom (head_cl cl).

(** all clause symbols *)
Definition sym_cl  cl := [seq sym_atom (val a) | a <- atoms_cl cl].

(** all head symbols of a program *)
Definition hsym_prog  p := [seq hsym_cl cl | cl <- p].

(** all program symbols *)
Definition sym_prog   p := flatten [seq sym_cl cl   | cl <- p].

(** all program atoms *)
Definition atoms_prog p := flatten [seq atoms_cl cl | cl <- p].

(** ** Grounding *)
Section Grounding.

(** *** Ground valuations and their application  *)

(** type of groundings: finitely-supported functions mapping variables to constants *)
Definition gr := finfun_finType (ordinal_finType n) cons_finType.

Implicit Types (g : gr) (t : term) (ra : raw_atom) (a : atom)
               (cl : clause) (hd : atom) (tl : seq atom).

(** term grounding *)
Definition gr_term g t :=
  match t with
  | Var v => g v
  | Val c => c
  end.

(** raw atom grounding *)
Definition gr_raw_atom g ra :=
  RawGAtom (sym_atom ra) [seq gr_term g x | x <- arg_atom ra].

(** the grounding of a well-formed ground atom is well-formed *)
Definition gr_atom_proof g a : wf_gatom (gr_raw_atom g a).
Proof. by case: a => s arg; rewrite /wf_gatom size_map. Qed.

(** atom grounding *)
Definition gr_atom g a := GAtom (gr_atom_proof g a).

(** Grounding on a list of atoms *)
Definition gr_tl g (tl : seq atom) :=
  map (gr_atom g) tl.

(** clause grounding *)
Definition gr_cl g cl :=
  GClause (gr_atom g (head_cl cl)) (wmap (gr_atom g) (body_cl cl)).

End Grounding.

Section Theory.

(** *** Collecting Constants *)

Section Constants.

(** Extract constant from term (as a list of at most one element) *)
Definition const_term t : seq constant :=
  if t is Val e then [:: e] else [::].

(** atom constants *)
Definition const_atom a : seq constant :=
  flatten [seq const_term x | x <- arg_atom a].

(** atom list constants *)
Definition const_tail (tl : seq atom) : seq constant :=
  flatten [seq const_atom (val x) | x <- tl].

(** clause constants *)
Definition const_cl cl : seq constant :=
  const_tail [:: head_cl cl & body_cl cl].

End Constants.

(** *** Collecting Variables *)
Section Variables.

(** term variables *)
Definition term_vars t : {set 'I_n} := if t is Var v then [set v] else set0.

(** "raw" atom variables *)
Definition raw_atom_vars (ra : raw_atom) : {set 'I_n} :=
  \bigcup_(t <- arg_atom ra) term_vars t.

(** atom variables *)
Definition atom_vars (a : atom) : {set 'I_n} := raw_atom_vars a.

(** atom list variables *)
Definition tail_vars tl : {set 'I_n} := \bigcup_(t <- tl) atom_vars t.

(** Extract variables from a clauses (as a set) *)
Definition cl_vars (cl : clause) : {set 'I_n} := tail_vars (body_cl cl).

(** if [x] in the variables of [tl], then [x] is also a var of [a:: tl] *)
Lemma tail_vars_cons x a tl : x \in tail_vars tl -> x \in tail_vars (a :: tl).
Proof.
unfold tail_vars. move=> /bigcup_seqP [ga Hga1 Hga2].
apply/bigcup_seqP. exists ga.
rewrite in_cons. apply/orP. right. apply Hga1.
apply Hga2.
Qed.

(** if [x] is a variable of [a] it is a variable of [a:: tl] *)
Lemma tail_vars_head x a tl : x \in atom_vars a -> x \in tail_vars (a :: tl).
Proof.
move=>Hx. unfold tail_vars. apply/bigcup_seqP. exists a.
rewrite in_cons. apply/orP. by left.
by apply/andP;split.
Qed.

(** If [v] is in the vars of a raw atom, adding a new term to the list of
  arguments does not change this fact (note raw atoms are untyped) *)
Lemma raw_atom_vars_cons v fa args h : v \in raw_atom_vars (RawAtom fa args)
                                -> v \in raw_atom_vars (RawAtom fa (h::args)).
Proof.
unfold raw_atom_vars. move=>/bigcup_seqP [ga Hga1 Hga2].
apply/bigcup_seqP. exists ga.
rewrite in_cons. apply/orP. by right. apply Hga2.
Qed.

(** If a var is in an atom and the atom in a body (list of atom),
   then the var is in the body *)
Lemma tailvars_trans v ato tl :
  v \in atom_vars ato -> ato \in tl -> v \in tail_vars tl.
Proof.
move=> /bigcup_seqP [t Htin Hvt] Hatoin.
apply/bigcup_seqP. exists ato. apply Hatoin.
apply/andP;split;auto.
apply/bigcup_seqP. exists t;auto.
Qed.

(** The vars of an empty body is the empty set *)
Lemma tail_vars_nil : tail_vars [::] = set0.
Proof.
apply/eqP. rewrite -subset0. apply/subsetP. move=>x /bigcup_seqP [ato Hatoin].
by rewrite in_nil in Hatoin.
Qed.

(** ** Program Safety Condition *)

(** clause safety: all head variables should appear among the body variables *)
Definition safe_cl cl :=
  atom_vars (head_cl cl) \subset tail_vars (body_cl cl).

(** program safety: all clauses should be safe *)
Definition prog_safe p := all safe_cl p.

(** *** Safety of deduced facts (in the IDB) - added *)
(** A clause has a safe head if its head predicate is of kind IDB *)
Definition safe_cl_hd cl :=
  predtype (hsym_cl cl) == Idb.

Definition prog_safe_hds p := all safe_cl_hd p.

(** An interpretation is a "safe edb" if alll its atoms have symbols
  of type edb *)
Definition safe_edb i := [forall ga in i, predtype (sym_gatom ga) == Edb].

End Variables.

(** *** No sharing of variables between clauses - added *)
(** Clauses sharing variables *)
Definition clauses_var_intersect (cl1 cl2 : clause) : bool :=
  tail_vars (body_cl cl1) :&: tail_vars (body_cl cl2) != set0.

(** Constraint on P: clauses sharing variables in a program would
   mean they are equals *)
Definition vars_not_shared (p : program) : bool :=
  [forall cl1 in p, forall cl2 in p,
    (clauses_var_intersect cl1 cl2) ==> (cl1 == cl2)].

(** If the constraint vars_not_shared is fullfilled on P and if we
   have a variable  v that is in both cl1 and cl2 clauses of P, then
   cl1 and cl2 are the same clause. *)
Lemma vns_cl_eq (p : program) (cl1 cl2 : clause) (v : 'I_n) :
  v \in (tail_vars (body_cl cl1)) -> v \in (tail_vars (body_cl cl2)) ->
  cl1 \in p -> cl2 \in p -> vars_not_shared p -> cl1 = cl2.
Proof.
move => vcl1 vcl2 Hcl1 Hcl2 vns.
unfold vars_not_shared in vns.
induction p.
- inversion Hcl1.
- rewrite in_cons in Hcl1 ; rewrite in_cons in Hcl2.
  destruct (orP Hcl1) as [Hcl1IsA | Hcl1InP] ; destruct (orP Hcl2) as [Hcl2IsA | Hcl2InP] ; clear Hcl1 ; clear Hcl2.
  + by rewrite (eqP Hcl1IsA) (eqP Hcl2IsA).
  + assert (Hcl1In : cl1 \in a::p).
    - rewrite (eqP Hcl1IsA) ; apply/mem_head.
    assert (Hcl2In : cl2 \in a::p).
    - apply/mem_body/Hcl2InP.
    assert (Hinters : clauses_var_intersect cl1 cl2).
    - apply/set0Pn. exists v. by apply/setIP ; split.
    pose Heq := (eqP (implyP (implyP (forallP (implyP ((forallP vns) cl1) Hcl1In) cl2) Hcl2In) Hinters)).
    by inversion Heq.
  + assert (Hcl1In : cl1 \in a::p).
    - apply/mem_body/Hcl1InP.
    assert (Hcl2In : cl2 \in a::p).
    - rewrite (eqP Hcl2IsA) ; apply/mem_head.
    assert (Hinters : clauses_var_intersect cl1 cl2).
    - apply/set0Pn. exists v. by apply/setIP ; split.
    pose Heq := (eqP (implyP (implyP (forallP (implyP ((forallP vns) cl1) Hcl1In) cl2) Hcl2In) Hinters)).
    by inversion Heq.
  + apply/(IHp Hcl1InP Hcl2InP)/forallP=>x.
    apply/implyP=>Hx.
    apply/forallP=>y. apply/implyP=>Hy.
    assert (Hcl1In : x \in a::p).
    - apply/mem_body/Hx.
    assert (Hcl2In : y \in a::p).
    - apply/mem_body/Hy.
    apply (implyP (forallP (implyP (forallP vns _) Hcl1In) _) Hcl2In).
Qed.

(** ** Program Satisfiability *)

(** a clause [c] is satisfied by an interpretation [i], if for all groundings [g]
its corresponding instantiation is satisfied by [i] *)
Definition cl_true cl i := forall g : gr, gcl_true (gr_cl g cl) i.

(** A program is true in i, if all grounding of its clauses are  true *)
Definition prog_true p i :=
  forall g : gr, all (fun cl => gcl_true (gr_cl g cl) i) p.


End Theory.
