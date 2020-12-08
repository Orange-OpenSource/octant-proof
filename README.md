# Overview

  - This folder contains the Coq proofs associated to the paper "Developing and certifying Datalog optimizations in Coq/MathComp". The main results are 

    + cadequacy, found at the end of octalgo/rinstance.v, corresponds to theorems 3.4 and 3.5 of the paper (adequacy of the generic transformation, which is defined in the same file)
    + proj_completeness and proj_soundness, from file octalgo/projection.v, which state the completeness and soundness of the predicate specialization (theorems 4.2 and 4.3 of the paper)
    + trace_sem_completeness and trace_sem_soundness, found in octalgo/tSemantics.v, correspond to lemmas 5.5 and 5.6 of the paper
    + no_rec_needed, found in octalgo/norec_sem.v, which is also stated in Figure 13 of the paper
    + no_rec_capt_nf, found at the end of octalgo/static.v, is the completeness of the static analysis. subs_comp_sub is mainly based on no_rec_capt, found in the same file.
    + static_extraction_adequacy, in octalgo/extract_static.v, shows that
      the partial instance with the static analysis preserves the semantics.


  - The proof was developped and tested using Coq 8.9.1, equations 1.2+8.9 and mathcomp-ssreflect 1.8.0.

  - The file _CoqProject provides a linear dependency for the files, although some elements could be permuted. 

  - On our mid-range laptop, the full compiling took a bit over one minute.


# Licenses

  - File in `third_party` is a modification of an ssreflect file (copyright Microsoft and Inria)
    performed by Formaldata. It is distributed under the Cecill-B license.
  - Files in `datalogcert` folder are a splitted and modified version of `pengine.v`
    initially developed by FormalData (Véronique Benzaken, Évelyne Contejean,
    and Stefania Dumbrava). The original development is published at
    https://framagit.org/formaldata/datalogcert. The files are distributed under
    the LGPL 3.0 license and are copyrighted CNRS and Université Paris-Sud,
    Université Paris-Saclay.
  - Files in `octalgo` folder are distributed under the LGPL 3.0 license or
    later and are copyrighted Orange.


# Commented development
Visible on-line at: https://orange-opensource.github.io/octant-proof/


# Files

- Some files were not written by us (bigop_aux, fixpoint, completeness).

- Others were originaly developed by Véronique Benzaken, Évelyne Contejean,
and Stefania Dumbrava, but modified by us (syntax, subs, pmatch, bSemantics,
monotonicity and soundness).

  + all these files are found in the third_party and datalogcert folders.

- Finally, some were fully written by us (utils, finseqs, fintrees, purge,
  occurrences, projection, rinstance, tSemantics, static, extract_static,
  norec_sem).

  + these files are stored in the octalgo folder.

- List of files

  + bigop_aux.v:                 more bigop operators and properties
  + utils.v:                     generic lemmas to ease the proofs and pset
  + finseqs.v:                   sequence fintypes
  + fintrees.v:                  tree fintypes
  + syntax.v:                    Datalog syntax 
  + subs.v:                      theory of substitutions
  + pmatch.v:                    matching, both constructive and as a predicate
  + bSemantics.v:                base and bounded Datalog semantics 
  + monotonicity.v:              lemmas about semantics monotonicity
  + soundness.v:                 soundness lemmas about the semantics
  + fixpoint.v:                  fixpoint lemmas for the completeness part
  + completeness.v:              completeness of the T_P mechanization
  + occurrences.v:               defining the different kinds of program occurrences
  + purge.v:                     transformations that delete useless clauses in a Datalog program, and their adequacy proofs
  + tSemantics.v:                trace semantics
  + static.v:                    definition and validation of the static analysis
  + rinstance.v:                 partial instance of Datalog programs
  + extract_static.v:            building substitutions for ctransfo using the static analysis
  + projection.v:                definition and validation of the predicate specialization

# Installation

We recommend using opam. Here is the result of `opam list` giving
the versions of the components we depend on:
```
# Name                 # Installed       # Synopsis
coq                    8.9.1             Formal proof management system
coq-equations          1.2.1+8.9         A function definition package for Coq
coq-mathcomp-finmap    1.4.0             Finite sets, finite maps, finitely supported
coq-mathcomp-ssreflect 1.8.0             Small Scale Reflection
```

# Assumptions 

## cadequacy

- Section Variables:

  + subs_comp : [forall cl in p, (0 < #|tail_vars (body_cl cl) :&: Rv|) ==> [forall s, bmatch def ffp cl s ==> (sub_filter s Rv \in subs)]]

  + subs : {set sub}

  + p : program

  + i : {set gatom}

  + def : syntax.constant

  + Rv : {set 'I_n}

- Axioms:

  + symtype : finType

  + n : nat

  + constype : finType

  + bn : nat

  + arity : {ffun symtype -> nat}


- subs is the provided set of substitutions, and subs_comp is the associated 
  "overapproximation" property defined in the paper.

- Rv is the set of variables to unfold. 

- p and i and the studied program and interpretation, def is a default constant.

- symtype is the (finite) set of predicates, and "arity" the arity function.

- constype is the (finite) set of constant. 

- n is the number of variables in p and bn the max length of body clauses in p.


## proj_completeness  

- Section Variables:

  + pnotf : [forall c, pclone c != f]

  + pinj : injective pclone

  + pclone : syntax.constant -> symtype

  + parity : [forall c, arity f == (arity (pclone c)).+1]

  + p : program

  + isafe : safe_edb i

  + ind : 'I_(arity f)

  + i : {set gatom}

  + ftype : predtype f = Idb

  + f : symtype

  + def : syntax.constant

  + bn_not_zero : 0 < bn

  + arity_vars : arity f < n.+1

  + always_cons : [forall cl in p, (hsym_cl cl == f) ==> [exists c, nth_error (arg_atom (head_cl cl)) ind == Some (Val c)]]

- Axioms:

  + symtype : finType

  + predtype : {ffun symtype -> pred_type}

  + n : nat

  + constype : finType

  + bn : nat

  + arity : {ffun symtype -> nat}

- pnotf, pinj, pclone and parity are used to build the new predicate names for
  the projection.

- p is the studied program and i the initial interpretation.

- isafe states that only extensional predicates are found in i.

- f and ind are the predicate and index to project over.

- ftype states that f is intensional, always_cons that, whenever f appears as
  the head of a rule, its ind^{th} argument is a constant.

- bn_not_zero and arity_vars are technical hypotheses, stating that there is at
  least an atom in the body of a rule, and that we have at least (arity f)
  variables available.


## proj_soundness  


- Section Variables:

  + psafe : prog_safe p

  + pnotf : [forall c, pclone c != f]

  + pinj : injective pclone

  + pfresh : [forall c, pclone c \notin sym_prog p]

  + pclone : syntax.constant -> symtype

  + parity : [forall c, arity f == (arity (pclone c)).+1]

  + p : program

  + ind : 'I_(arity f)

  + ifresh : ~~ [exists x in i, is_clone_ga x]

  + i : {set gatom}

  + f : symtype

  + def : syntax.constant

  + bn_not_zero : 0 < bn

  + arity_vars : arity f < n.+1

  + always_cons : [forall cl in p, (hsym_cl cl == f) ==> [exists c, nth_error (arg_atom (head_cl cl)) ind == Some (Val c)]]

- Axioms:

  + symtype : finType

  + n : nat

  + constype : finType

  + bn : nat

  + arity : {ffun symtype -> nat}

- psafe states that the studied program p is safe, i.e. any variable that
  appears in a clause's head also appears in its body.

- ifresh means that no projected predicate appears in the initial
  interpretation i -- those predicates should be "fresh"

- the other assumptions are the same as in proj_completeness


## trace_sem_completeness / trace_sem_soundness

- Section Variables:

  + p : program

  + gat_def : gatom

- Axioms:

  + symtype : finType

  + n : nat

  + FunctionalExtensionality.functional_extensionality_dep: forall (A : Type) (B : A -> Type) (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g

  + constype : finType

  + bn : nat

  + arity : {ffun symtype -> nat}

- p is a the studied program, gat_def a default ground atom (required by
  the wutree type).

- functional_extensionality_dep is imported to use dependent destruction.


## no_rec_needed

- Section Variables:

  + p : program

  + gat_def : gatom

  + dv : 'I_n

  + dt : term

  + df : symtype

- Axioms:

  + symtype : finType

  + n : nat

  + FunctionalExtensionality.functional_extensionality_dep: forall (A : Type) (B : A -> Type) (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g

  + constype : finType

  + bn : nat

  + arity : {ffun symtype -> nat}

- p is the studied program. get_def, dv, dt and df are default values, mostly
  used by the nth function.

- functional_extensionality_dep is imported by the use of the trace semantics.


## no_rec_capt_nf

- Section Variables:

  + p : program

  + gat_def : gatom

  + dv : 'I_n

  + dt : term

  + docc : t_occ p

  + df : symtype

- Axioms:

  + symtype : finType

  + predtype : {ffun symtype -> pred_type}

  + n : nat

  + FunctionalExtensionality.functional_extensionality_dep: forall (A : Type) (B : A -> Type) (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g

  + constype : finType

  + bn : nat

  + arity : {ffun symtype -> nat}

- p is the studied program.

- get_def, dv, dt, docc and df are various default values, mostly used by 
  the nth function.

- functional_extensionality_dep is imported by the use of the trace semantics.

- The hypotheses described in the paper (unicity of variables across rules, 
  all variables in rules' heads are also in the body, only intensional
  predicates as the head of rules, only extensional predicates in the initial
  interpretation) are found in the theorem itself.


## static_extraction_adequacy 

- Section Variables:

  + v : 'I_n

  + p : program

  + i : {set gatom}

  + dv : 'I_n

  + docc : t_occ p

  + dga : gatom

  + df : symtype

  + def : syntax.constant

  + Hvns : vars_not_shared p

  + Hvarinhead : only_variables_in_heads p

  + Hsafe_edb : safe_edb i

  + Hpsafehds : prog_safe_hds p

  + Hpsafe : prog_safe p

- Axioms:

  + symtype : finType

  + predtype : {ffun symtype -> pred_type}

  + n : nat

  + FunctionalExtensionality.functional_extensionality_dep: forall (A : Type) (B : A -> Type) (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g

  + constype : finType

  + bn : nat

  + arity : {ffun symtype -> nat}

- v is the analyzed variable, p the program, i the initial interpretation.

- dv, docc, dga, df and def default values for various types.

- vars_not_shared is the unicity of variables across rules,
  only_variables_in_head states that no constant can be found in the head of
  a clause, safe_edb that only extensional predicates appear in the initial 
  interpretation, prog_safe_hds that only intensional predicates appear as
  the head of clauses, and prog_safe means that any variable appearing in
  the head of a clause also appears in its body.

- functional_extensionality_dep is required by the trace semantics.

