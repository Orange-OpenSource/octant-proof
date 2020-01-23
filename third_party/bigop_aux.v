(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* (c) Copyright 2016-2019 : FormalData                                      *)
(* Distributed under the terms of CeCILL-B.                                  *)

From mathcomp
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
From mathcomp
Require Import tuple finfun bigop finset finmap.

(* Auxiliary bigop lemmas, all of them are straightforward copies from
 * the ones in finset.v, thus finset's LICENSE applies. Not much to
 * document.
 *
 * We also define \bigcup in for fset_scope.
 *)

Section BigCupSeq.

Variables (T : finType) (I : eqType).
Implicit Types (P : pred I) (F :  I -> {set T}).

Lemma bigcup_seqP x P F l :
  reflect (exists2 i : I, i \in l & (x \in F i) && P i) (x \in \bigcup_(t <- l | P t) F t).
Proof.
rewrite big_tnth; apply/(iffP idP).
  by case/bigcupP=> i Hp Hin; exists (tnth (in_tuple l) i); rewrite ?mem_tnth ?Hin.
by case=> i /seq_tnthP[t ht] /andP[xf xp]; apply/bigcupP; exists t; rewrite -?ht.
Qed.

Lemma bigcups_seqP (U : pred T) (P : pred I) (F : I -> {set T}) (r : seq I) :
  reflect (forall i : I, i \in r -> P i -> F i \subset U)
          (\bigcup_(i <- r | P i) F i \subset U).
Proof.
apply/(iffP idP).
  by rewrite big_tnth; move/bigcupsP=> H i /seq_tnthP[idx -> hp]; exact: H.
by move=> H; rewrite big_tnth; apply/bigcupsP=> i ?; apply: H; rewrite ?mem_tnth.
Qed.

End BigCupSeq.

Open Scope fset_scope.

Notation "\bigcup_ ( i <- r | P ) F" :=
  (\big[@fsetU _/fset0]_(i <- r | P%fset) F%fset) : fset_scope.

Notation "\bigcup_ ( i <- r ) F" :=
  (\big[@fsetU _/fset0]_(i <- r) F%fset) : fset_scope.

Notation "\bigcup_ ( i | P ) F" :=
  (\big[@fsetU _/fset0]_(i | P) F%fset) : fset_scope.

Notation "\bigcup_ ( i 'in' A | P ) F" :=
  (\big[@fsetU _/fset0]_(i in A | P) F%fset) : fset_scope.

Notation "\bigcup_ ( i 'in' A ) F" :=
  (\big[@fsetU _/fset0]_(i in A) F%fset) : fset_scope.

Section FSetMonoids.

Import Monoid.
Variable (T : choiceType).

(* Not valid for setI *)
(* Canonical fsetI_monoid := Law (@fsetIA T) (@fsetTI T) (@setIT T). *)
(* Canonical fsetI_comoid := ComLaw (@fsetIC T). *)
(* Canonical fsetI_muloid := MulLaw (@fset0I T) (@fsetI0 T). *)

End FSetMonoids.

Section BigFOpsFin.

Variables (T : choiceType) (I : finType).
Implicit Types (P : pred I) (A B : {fset I}) (F :  I -> {fset T}).

End BigFOpsFin.

Section BigFOpsSeq.

Variables (T : choiceType) (I : eqType).
Implicit Types (l : seq I) (P : pred I) (U : {fset T}) (F :  I -> {fset T}).

Lemma bigfcup_seqP x F l :
  reflect (exists2 i : I, i \in l & x \in F i) (x \in \bigcup_(t <- l) F t).
Proof.
rewrite big_tnth; apply/(iffP idP).
  by case/bigfcupP=> u _ xf; exists (tnth (in_tuple l) u); rewrite ?mem_tnth.
by case=> i /seq_tnthP[t hi] xf; apply/bigfcupP; exists t; rewrite -?hi ; [apply/andP ; split | ].
Qed.

Lemma bigfcups_seqP F U l :
  reflect (forall i : I, i \in l -> F i `<=` U) (\bigcup_(i <- l) F i `<=` U).
Proof.
rewrite big_tnth; apply/(iffP idP).
  by move/bigfcupsP=> H i /seq_tnthP[t ->]; apply: H.
by move=> H; apply/bigfcupsP=> i _ _; apply: H; rewrite mem_tnth.
Qed.

End BigFOpsSeq.

Close Scope fset_scope.
