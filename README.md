# Overview

  - This folder contains the Coq proof associated to the paper *Certifying a Datalog optimization in Coq/SSReflect*, Pierre-Léo Bégay, Pierre Crégut and Jean-François Monin. The main results are:

    + `cadequacy`, found at the end of `ctransfo.v`, corresponds to theorem
    1 of the paper (adequacy of the generic transformation, which is defined
    in the same file).
    + `subs_comp_sub`, found at the end of `depsubs_filter.v`, corresponds
    to theorem 2 of the paper (completeness of the typing system).
    `subs_comp_sub` is mainly based on `subs_comp_cl`, found in the same file.
    + the typing system is defined in `rules.v` (Inductive `predTyping`),
    while the types are in `dTypes.v` (core) and `ddTypes.v` (dependent
    overlay for the typing system).
    + `trace_sem_completeness` and `trace_sem_soundness`, found at the
    middle of `tSemantics.v`, correspond to lemmas 3 and 4 of the paper
    + files `finseqs` and `fintrees` contain new finite types described in
    section 5.1 of the paper.

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

# Assumptions

## cadequacy

`Print Assumptions cadequacy` returns:

```
Section Variables:
subs_comp : [forall cl in p,
               forall s,
               bmatch def ffp cl s ==> (sub_filter s Rv \in subs)]
subs : {set sub}
p : program
i : {set gatom}
def : syntax.constant
Rv : {set 'I_n}
Axioms:
symtype : finType
n : nat
constype : finType
bn : nat
arity : {ffun symtype -> nat}
```

`subs` is the provided set of substitutions, and `subs_comp` is the
associated "overapproximation" property defined in the paper.
`R` is the set of variables to unfold.
`p` and `i` are the studied program and interpretation,
`def` is a default constant.
`symtype` is the (finite) set of predicates, and `arity` the arity function.
`constype` is the (finite) set of constant.
`n` is the number of variables in `p` and `bn` the maximum length of
body clauses in `p`.


## c_typ_trans_adequacy
`Print Assumptions c_typ_trans_adequacy` returns:

```
Section Variables:
typing : forall v : 'I_n, var_type p v
pvars : vars_not_shared p
psafe : prog_safe p
phsafe : prog_safe_hds p
p : program
i : {set gatom}
ext_edb : safe_edb i
dv : 'I_n
dga : gatom
def : constant
Rv : {set 'I_n}
Axioms:
symtype : finType
predtype : {ffun symtype -> pred_type}
n : nat
FunctionalExtensionality.functional_extensionality_dep :
forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
(forall x : A, f x = g x) -> f = g
constype : finType
bn : nat
arity : {ffun symtype -> nat}
JMeq.JMeq_eq : forall (A : Type) (x y : A), JMeq.JMeq x y -> x = y
```

`typing` is a type inference for each variable.
The next three are the assumptions on the program (unicity of variables
across rules / all variables in rules' heads are also in the body / only
intensional predicates as the head of rules), as defined in the paper.
`ext_edb` is the assumption that only extensional predicates are found
in the initial interpretation.
`dv` and `dga` are default variables and ground (fully instantiated) atoms.
`functional_extensionality_dep` comes with equations.
`JMeq_eq` comes with Program.Equality.

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
