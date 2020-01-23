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

(** This is the third part of the original file "pengine.v" with some modifications
    by Pierre-Léo Bégay *)

Require Import utils.
Require Import syntax.
Require Import subs.
Require Import finseqs.

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype.
From mathcomp
Require Import tuple finset bigop finfun.

Require Import bigop_aux.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * constructive match *)
Section Match.

Implicit Types (s : sub) (t : term) (a : atom) (v : 'I_n)
         (b : 'I_n * syntax.constant) (i : interp).


(** ** match on terms *)
(** matching a term [t] against a constant [d], starting from an initial substitution [s]. *)
Definition match_term d t s : option sub :=
  match t with
  | Val e => if d == e then Some s else None
  | Var v => if s v is Some e then
             (if d == e then Some s else None)
             else Some (add s v d)
  end.

(** Let [s1], [s2] be two substitutions. If [s2] is the result of matching a term [t]
against a constant [d], starting from an initial substitution [s1], then [s2] extends [s1]. *)
Lemma match_term_sub s1 s2 t d : match_term d t s1 = Some s2 -> sub_st s1 s2.
Proof.
case: t => //= [v|e]; last first.
  by case: eqP => _ // [->].
case E: (s1 _) => /= [a|].
  by case: eqP => _ // [->].
by case=> <-; have/eqP/sub_add := E.
Qed.

(** ** Generalization to raw atoms *)
(** matching a raw atom [ra] against a ground raw atom [rga], starting from an initial substitution [s]. *)
Definition match_raw_atom s ra rga : option sub :=
  match ra, rga with
    | RawAtom s1 arg1, RawGAtom s2 arg2 =>
      if (s1 == s2) && (size arg1 == size arg2)
      then foldl (fun acc p => obind (match_term p.1 p.2) acc)
                 (Some s) (zip arg2 arg1)
      else None
  end.

(** matching an [a] against a ground atom [ga], starting from an initial substitution [s]. *)
Definition match_atom s a (ga : gatom) := match_raw_atom s a ga.

(** matching an atom [a] against all the ground atoms of an interpretation [i], starting from an
initial substitution [s] *)
Definition match_atom_all (i : interp) a s :=
  [set x | Some x \in [set opt_sub (match_atom s a ga) | ga in i]].

(** reflection lemma for atom matching *)
Lemma match_atomsP a i r s :
  reflect (exists2 ga, ga \in i & Some r = match_atom s a ga)
          (r \in match_atom_all i a s).
Proof. by rewrite inE; exact: (iffP imsetP). Qed.

(** join for the set monad *) 
Definition bindS {A B : finType} (i : {set A}) (f : A -> {set B}) : {set B} :=
  cover [set f x | x in i].

(** reflection lemma for binding *)
Lemma bindP (A B : finType) (i : {set A}) (f : A -> {set B}) (r : B) :
  reflect (exists2 s, s \in i & r \in f s) (r \in bindS i f).
Proof.
by rewrite /bindS cover_imset; exact: (iffP bigcupP); case=> s xin rin; exists s.
Qed.

(** monadic fold for the set monad: iteratively composing the result of applying a function [f],
seeded with an initial value [s0], to all elements of a list [l] *)
Fixpoint foldS {A : Type} {B : finType}
         (f : A -> B -> {set B}) (s0 : {set B}) (l : seq A) :=
  if l is [:: x & l] then bindS s0 (fun y => foldS f (f x y) l)
  else s0.

(** If functions [f] and [g] are extensionally equal, then we get the same output when binding
a set [s] with them. *)
Lemma eq_bindS (A B : finType) (f g : A -> {set B}) (s : {set A}) :
  f =1 g -> bindS s f = bindS s g.
Proof.
move=> h_f; apply/setP=> x; rewrite /bindS !cover_imset.
by apply/bigcupP/bigcupP; case=> y y_in x_in; exists y; rewrite // ?h_f // -h_f.
Qed.

(** The result of binding the union of two sets [s1] and [s2] with a function [f]
equals the result of taking the union between the binding of [s1] with [f] and
the binding of [s2] with [f] *)
Lemma bindSU (A B : finType) (f : A -> {set B}) (s1 s2 : {set A}) :
  bindS (s1 :|: s2) f = bindS s1 f :|: bindS s2 f.
Proof. by rewrite /bindS !cover_imset bigcup_setU. Qed.

(** Let [s] be a set and [f], [g] two functions. The result of taking the union
between the binding of [s] with [f] and the binding of [s] with [g] equals the 
binding of [s] with the function that returns the point-wise union of [f] and [g] application *)
Lemma bindUS (A B : finType) (f g : A -> {set B}) (s : {set A}) :
  bindS s f :|: bindS s g = bindS s (fun x => f x :|: g x ).
Proof.
rewrite /bindS !cover_imset; apply/setP=> x; rewrite !inE; apply/orP/bigcupP.
  by case=> /bigcupP[y hy hfy]; exists y; rewrite // inE hfy ?orbT.
by case=> [y hy]; rewrite inE; case/orP=> hf; [left | right]; apply/bigcupP; exists y.
Qed.

(** If [f] and [g] are extensionally equal, then the results of taking their fold over a list [l],
seeded with an initial set [s], are equal *)
Lemma eq_foldS (A : eqType) (T : finType) f g (s : {set T}) (l : seq A) :
  {in l, f =2 g} -> foldS f s l = foldS g s l.
Proof.
move=> h_f; elim: l s h_f => //= x l ihl s h_f.
have heq: (fun y : T => foldS f (f x y) l) =1
          (fun y : T => foldS g (g x y) l).
  move=> y; rewrite h_f ?inE ?eqxx ?ihl //.
  by move=> u hu k; rewrite h_f // inE hu orbT.
by rewrite (eq_bindS _ heq).
Qed.

(** The result of folding a function [f] over a list [l], starting from the union 
of sets [s1] and [s2] equals the union of folding [f] over [l] starting from [s1]
and of folding [f] over [l] starting from [s2] *)
Lemma foldSU A (T : finType) f (s1 s2 : {set T}) (l : seq A) :
  foldS f (s1 :|: s2) l = foldS f s1 l :|: foldS f s2 l.
Proof. by elim: l => //= x l ihl; rewrite bindSU. Qed.

(** matching a list of atoms [tl] agains ground atoms of an interpretation [i] *)
Definition match_body i tl : {set sub} :=
  foldS (match_atom_all i) [set emptysub] tl.

(** * boolean match - Added *)

(** A default constant that will not be really used *)
Variable def : syntax.constant.

(** [bmatch i cl s] iff for every atom [a] of [cl] body [s a]
   is i [i] *)
Definition bmatch i cl s : bool :=
  (** if s does not cover tl's variables, no *)
  (** otherwise, it's okay to cast s to gr with a random constant *)
  if (cl_vars cl \subset dom s) then
  all (mem i) (body_gcl (gr_cl (to_gr def s) cl)) else false.

End Match.
