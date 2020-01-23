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

From mathcomp
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun choice fintype tuple finset.

Require Import bigop_aux.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Various utilitary lemmas to reduce proof sizes *)

(** ** bool *)
Section boolUtils.

Lemma bool_to_prop_l (a b : bool) : (a && b) -> a.
Proof.
by move => /andP [].
Qed.

Lemma bool_to_prop_r (a b : bool) : (a && b) -> b.
Proof.
by move => /andP [].
Qed.

Lemma Eqdep_dec_bool : forall (b : bool) (p1 p2 : b = true), p1 = p2.
Proof.
  by move => b p1 p2 ; apply Eqdep_dec.eq_proofs_unicity; 
  move => x y ; destruct (Bool.bool_dec x y) ; [left | right]. 
Qed.

Lemma bool_des_rew (b : bool) : (b = true) \/ (b = false).
Proof.
by case b;[left|right].
Qed.

End boolUtils.

(** ** nat *)

Section nat.

Lemma ltn_leq_trans : forall n m p : nat, m < n -> n <= p -> m < p.
Proof.
move => n m p.
move : n m.
destruct p.
- move => n m H.
  rewrite leqn0.
  move=>/eqP H2. rewrite H2 in H; inversion H. 
- move => n m Hmn.
  rewrite leq_eqVlt.
  by move=>/orP [/eqP <- |];[|apply ltn_trans].
Qed.

(** *** Lemmas on max *)

Section max.

Lemma gtn_max_l : forall m n1 n2, (maxn n1 n2 < m) -> n1 < m.
Proof. 
move => m n1 n2 H ; rewrite gtn_max in H ; apply (bool_to_prop_l H).
Qed.

Lemma gtn_max_r : forall m n1 n2, (maxn n1 n2 < m) -> n2 < m.
Proof. 
move => m n1 n2 H ; rewrite gtn_max in H ; apply (bool_to_prop_r H).
Qed.

Lemma geq_max_l : forall m n1 n2, (maxn n1 n2 <= m) -> n1 <= m.
Proof.
move => m n1 n2 H ; rewrite geq_max in H ; apply (bool_to_prop_l H).
Qed.

Lemma geq_max_r : forall m n1 n2, (maxn n1 n2 <= m) -> n2 <= m.
Proof. 
move => m n1 n2 H ; rewrite geq_max in H ; apply (bool_to_prop_r H).
Qed.

End max.

End nat.

(** ** Finset *)

Section finset.

(** *** Iter is increasing *)
(** if f is increasing and "smaller" than g, the iterations have the same order *)
(* TODO: generalize on the type and order *)
Lemma iter_fun_incr {A : finType} (f g : {set A} -> {set A}) (i : nat) (b : {set A}) : 
   [forall x : {set A}, forall y : {set A}, (x \subset y) ==> (f x \subset f y)] 
-> [forall x, f x \subset g x] -> iter i f b \subset iter i g b.
Proof.
move=>Hf /forallP Hfg.
induction i as [|i Hi];auto. simpl.
apply/subset_trans.
apply (implyP (forallP (forallP Hf (iter i f b)) (iter i g b)) Hi).
apply Hfg.
Qed.

(** *** Disjoint *)
Lemma disjointC {A : finType} (s : {set A}) : [disjoint s & ~: s].
Proof.
by rewrite -subsets_disjoint.  
Qed. 

Lemma disjoint_in_false {A : finType} (t1 t2 : {set A}) (x : A) : 
  x \in t1 -> x \in t2 -> [disjoint t1 & t2] -> False. 
Proof.
move=>H1 H2 Hdisj. 
rewrite disjoint_subset in Hdisj. 
have Hf := (subsetP Hdisj _ H1). 
unfold mem in Hf. simpl in Hf. unfold in_mem in Hf. simpl in Hf.
unfold negb in Hf. unfold mem in H2. unfold in_mem in H2. simpl in H2. 
rewrite H2 in Hf. inversion Hf. 
Qed.

Lemma subset_to_in {A : finType} (x : A) (s1 s2 : {set A}) : x \in s1 -> s1 \subset s2 -> x \in s2.
Proof.
move=>H /subsetP H1. by apply H1.
Qed.

(** *** Equivalence partitions *)

Lemma equiv_part_set0 {T : finType} (P : rel T) :
  equivalence_partition P set0 = set0.
Proof.
apply/eqP. rewrite -subset0.
apply/subsetP=>x /imsetP [y Hf]. by rewrite in_set0 in Hf. 
Qed.

Lemma equiv_part_set_mon {T : finType} (P : rel T) (s1 s2 : {set T}) :
  s1 \subset s2 -> 
  [forall x in equivalence_partition P s1, exists y in equivalence_partition P s2,
      x \subset y].
Proof.
move=>Hsub. apply/forallP=>x; apply/implyP=>/imsetP [y Hy1 ->].
apply/existsP. exists [set z in s2 | P y z]. apply/andP;split.
apply/imsetP. exists y. apply (subset_to_in Hy1 Hsub). reflexivity.
apply/subsetP=>z. rewrite in_set. move=>/andP [H1 H2].
rewrite in_set. apply/andP;split. apply (subset_to_in H1 Hsub). apply H2.
Qed.

(** *** A set that is not a singleton {x} is empty or contains y != x *)

Lemma set0_set1_neq {A : finType} (x : A) : set0 != [set x].
Proof.
rewrite eq_sym.
by rewrite -card_gt0 cards1.
Qed.

Lemma not_set1P {A : finType} (x : A) (s : {set A}) : 
  reflect (s != [set x]) ((s == set0) || [exists y in s, y != x]).
Proof.
apply/(iffP orP).
move => [Hsset0|/existsP Hex].
- rewrite (eqP Hsset0). apply set0_set1_neq.
- destruct Hex as [y Hy]. 
  destruct (andP Hy) as [Hyin Hyxneq].
  rewrite eqEsubset negb_and. apply/orP. left.
  apply/subsetP. move => Hf. 
  rewrite (set1P (Hf y Hyin)) in Hyxneq. 
  by apply (negP Hyxneq).
move => Hneq.
destruct (set_0Vmem s) as [Hsset0|[y Hy]].
- by left ; apply/eqP. 
- right.
  rewrite -negb_forall_in.
  apply/negP. move => Hf. 
  apply/(negP Hneq). rewrite eqEsubset.
  apply/andP ; split.
  + apply/subsetP. move=>z Hz. 
    apply/set1P/eqP/(implyP (forallP Hf z))/Hz.
  + rewrite sub1set.
    by rewrite -(eqP (implyP (forallP Hf y) Hy)).
Qed.

End finset.

(** ** Seq *)
Section seq.

(** *** Fold with max *)

Section fold.

(** Technical lemma: Folding with obind starting from None can only give None *)
Lemma foldObindNone {A B : Type} l (f : B -> A -> option A) : foldl (fun acc p => obind (f p) acc)
                 None l = None.
Proof.
by induction l as [|h l Hl]; [reflexivity| simpl ;rewrite Hl].
Qed.

Lemma fold_maxn_n_map_geq {A : Type} {w n : nat} {l : seq A} {f : A -> nat} :
  (has (fun t => (w <= f t)) l) -> w <= foldr maxn n (map f l).
Proof.
induction l;auto.
move=>/orP [Ha|Hl];rewrite leq_max; apply/orP.
- left. apply Ha.
- right. apply/IHl/Hl.
Qed.

Lemma fold_maxn_n_map_gtn {A : Type} {w n : nat} {l : seq A} {f : A -> nat} :
  (has (fun t => (w < f t)) l) -> w < foldr maxn n (map f l).
Proof.
induction l;auto.
move=>/orP [Ha|Hl]; rewrite leq_max; apply/orP.
- left. apply Ha.
- right. apply/IHl/Hl. 
Qed.

Lemma leq_fold_maxl : forall l n, n <= foldr maxn n l.
Proof.
by induction l ; [ | move => n ; rewrite leq_max ; apply/orP ; right ; apply IHl].
Qed.

Lemma leq_fold_base : forall n m l, foldr maxn n l <= m -> n <= m.
Proof.
induction l;auto.
rewrite geq_max ; move => /andP [Han Hnl] ; apply/IHl/Hnl.
Qed.

Lemma foldr_maxn_base {x y m : nat} {l : seq nat} (Hyx : y <= x) (Hf : foldr maxn x l <= m) : foldr maxn y l <= m.
Proof.
induction l.
- apply leq_trans with (n := x) ; [apply Hyx | apply Hf].
- rewrite geq_max. apply/andP. split.
  + apply (geq_max_l Hf).
  + apply/IHl/geq_max_r/Hf.
Qed.

End fold.

(** *** rem *)
Section rem.

Lemma in_rem {A : eqType} : forall x h (l : seq A), 
x \in l -> x != h -> x \in rem h l.
Proof.
induction l.
- move => Habs ; inversion Habs.
- rewrite in_cons ; move => Hxal Hneq.
  destruct (orP Hxal) as [Hxa | Hxl].
  + destruct (eqVneq a h) as [Hha | Hhna].
    - by rewrite -Hha (eqP Hxa) eq_refl in Hneq.
    - simpl. rewrite (ifN_eq _ _ Hhna). by apply/orP ; left.
  + destruct (eqVneq a h) as [Hha | Hhna].
    - by rewrite -Hha /= eq_refl. 
    - simpl. rewrite (ifN_eq _ _ Hhna). by apply/orP ; right ; apply IHl.
Qed.

Lemma mem_body : forall (T : eqType) (s : seq T) (x y : T) , x \in s -> x \in y :: s.
Proof.
intros. rewrite in_cons. by apply/orP;right.
Qed.

Lemma sub_rem {A : eqType} : forall (s l : seq A) h,
{subset h :: l <= s} -> h \notin l -> {subset l <= rem h s}.
Proof.
destruct s as [| a s].
- move => l h Habs. have Hf := (Habs h (mem_head h _)). by rewrite in_nil in Hf.
- move => l h Hsub Hnotin x Hx.
  simpl. pose Hxas := Hsub x (mem_body _ Hx). 
  destruct (eqVneq a h) as [Haq | Hanq].
  + rewrite Haq eq_refl. move:Hxas. rewrite in_cons. move => Hxas.
    destruct (orP Hxas) as [Hxa | Hxs].
    - rewrite (eqP Hxa) Haq in Hx.
      by rewrite Hx in Hnotin.
    - apply Hxs.
  + rewrite (ifN_eq _ _ Hanq). 
    move : Hxas. rewrite in_cons. move => Hxas.
    destruct (orP Hxas) as [Hxa | Hxs].
    - by apply/orP ; left.
    - apply/orP ; right. 
      destruct (eqVneq x h) as [Hxh | Hnxh].
      + by rewrite -Hxh Hx in Hnotin.
      + by apply in_rem.
Qed.

Lemma seq_in_rem_size {A : eqType} : forall (h : A) s, h \in s -> size s = (size (rem h s)).+1.
Proof.
induction s.
- move => H. inversion H.
- rewrite in_cons. move => Hin. destruct (orP Hin).
  + rewrite (eqP H). simpl. by rewrite eq_refl.
  + simpl ; apply/eq_S. destruct (a == h).
    - auto.
    - by rewrite (IHs H).
Qed.

End rem. 

Section size_map_leq.
(** *** (p)map leq size *)
Lemma size_map_leq {A B : Type} {s : seq A} {f : A -> B} {w : nat} : size s <= w -> size (map f s) <= w.
Proof.
by rewrite size_map.
Qed.

Lemma pmap_size_leq {A B : Type} (f : A -> option B) (s : seq A) : size (pmap f s) <= size s.
Proof.
by rewrite size_pmap count_size.
Qed.

End size_map_leq.

Section all.
(** *** all *)

Lemma all_exist_seq {A B : finType} (s : seq A) P : 
    all (fun x => [exists im : B, P x im]) s 
 -> exists sb, 
      ((map fst sb) == s) && all (fun x => P (fst x) (snd x)) sb.
Proof.
move=>H.
induction s as [|h tl Hs]. by exists [::].
destruct (andP H) as [H1 H2].
destruct (existsP H1) as [im Him].
destruct (Hs H2) as [sr Hsr]. destruct (andP Hsr) as [Hsr1 Hsr2].
exists ((h,im) :: sr).  apply/andP;split.
by rewrite -(eqP Hsr1). apply/andP;auto.
Qed.

Lemma all_exist_enum {A B : finType} (s : {set A}) P : 
    [forall x in enum s, [exists im : B, P x im]] 
 -> exists sb, 
      ((map fst sb) == enum s) && all (fun x => P (fst x) (snd x)) sb.
Proof.
move=>H.
induction (enum s)as [|h tl Hs]. by exists [::].
assert (Hr : [forall x in tl, exists im, P x im]). 
apply/forallP=>x. apply/implyP=>Hx. apply (implyP (forallP H x)). 
rewrite in_cons. by apply/orP;right.
destruct (Hs Hr) as [sr Hsr].
assert (Hrb: [exists im, P h im]). apply (implyP (forallP H h)).
by rewrite in_cons;apply/orP;left.
destruct (existsP Hrb) as [im Pim].
destruct (andP Hsr) as [H1 H2].
exists ((h,im) :: sr). apply/andP;split.
by rewrite -(eqP H1). apply/andP;auto.
Qed.

Lemma all_exist_tuple {A B : finType} (s : {set A}) P : 
    [forall x in s, [exists im : B, P x im]] 
 -> [exists t : #|s|.-tuple (prod A B), 
      ((map fst t) == enum s) && all (fun x => P (fst x) (snd x)) t].
Proof.
move=>Hb. assert (H:[forall x in enum s, [exists im : B, P x im]]).
apply/forallP=>x. apply/implyP=>Hx. rewrite mem_enum in Hx.
apply (implyP (forallP Hb x) Hx). 
apply/existsP.
destruct (all_exist_enum H) as [sr Hsr].
assert (Hsize : size sr = #|s|). destruct (andP Hsr) as [H1 H2].
by rewrite cardE -(@size_map _ _ (fun x=>x.1)) (eqP H1).
rewrite -Hsize. by exists (in_tuple sr).
Qed.

Lemma sub_all_and_l (A : eqType) (a1 a2 : pred A) l : all (fun x => (a1 x) && a2 x) l -> all a1 l.
Proof.
apply sub_all. by move=> x /andP [H1 H2].
Qed.

Lemma sub_all_and_r (A : eqType) (a1 a2 : pred A) l : all (fun x => (a1 x) && a2 x) l -> all a2 l.
Proof.
apply sub_all. by move=> x /andP [H1 H2].
Qed.

Lemma negb_has_predC_all {A : Type} (a : pred A) (s : seq A) :
has (predC a) s = false -> all a s.
Proof.
rewrite has_predC.
by destruct (bool_des_rew (all a s)) as [H|H];rewrite H.
Qed.

End all.

Lemma pair_seq_nth_proj_l {A B : Type} (x : seq A) (k : nat) (def : (A * B)%type) (s : seq (A * B)%type) :
[seq i.1 | i <- s] = x ->
(nth def s k).1 = nth def.1 x k.
Proof.
move:x k.
induction s as [|h tl Htup];move=>[|hl ll] [|k] //= [H1 H2].
apply H1.
by rewrite (Htup ll k H2).
Qed.

Lemma map_square_eq {A B C D : Type} (f : A -> C) (g : B -> C) (h : A -> D) (m : B -> D) 
  (l1 : seq A) (l2 : seq B) :
   (forall x y, (f x = g y -> h x = m y))
-> [seq f x | x <- l1] = [seq g y | y <- l2] 
-> [seq h x | x <- l1] = [seq m y | y <- l2].
Proof.
move:l2;induction l1 as [|h1 l1 Hl]; move=>[|h2 l2] //= Heq [H1 H2].
rewrite (Heq h1 h2 H1). apply/f_equal. 
by rewrite (Hl l2 Heq).
Qed.

Lemma seq_inj T (x y : T) (xs ys : seq T) :
  [:: x & xs] = [:: y & ys] -> x = y /\ xs = ys.
Proof. by case. Qed.

End seq.

(** * Various definitions *)

(** *** dep_iota: returning a sequence of nats as ordinals *)

Definition dep_iota (m n : nat) : seq ('I_(m+n)) :=
  pmap insub (iota m n).

Lemma dep_iotaE (m n : nat) : map val (dep_iota m n) = iota m n.
Proof.
move:m. 
induction n as [|n Hn] => [|m] //=.
unfold dep_iota. simpl. unfold oapp.
rewrite insubT. 
rewrite addnS -addSn. 
by apply ltn_addr. 
move=>H /=.
by rewrite -addSnnS (Hn m.+1).
Qed.

Lemma size_dep_iota (m n : nat) : size (dep_iota m n) = n. 
Proof. 
by rewrite -(size_map val) dep_iotaE size_iota. 
Qed.

(** *** nth_error: trying to get the i-th element of a seq *)

(* source: https://coq.inria.fr/library/Coq.Lists.List.html *)
Fixpoint nth_error (A : Type) (l:seq A) (n:nat) {struct n} : option A :=
  match n, l with
    | O, x :: _ => Some x
    | S n, _ :: l => nth_error l n
    | _, _ => None
  end.

Lemma nth_error_in (A : eqType) (l:seq A) (n:nat) (x:A): 
  nth_error l n = Some x -> x \in l.
Proof.
move:n.
induction l ; destruct n as [|n] ; try (by []) ; 
rewrite in_cons ; move => H ; apply/orP.
by inversion H ; left. 
right ; apply (IHl n H).
Qed.

Lemma nth_error_map (A B : eqType) (f: A -> B) (l:seq A) (n:nat) (x:A): 
  nth_error l n = Some x -> nth_error (map f l) n = Some (f x).
Proof.
move:n.
induction l ; destruct n as [|n] ; try (by []). 
by move=>[->]. 
move=>/= H. apply/IHl/H.
Qed.

Lemma nth_error_preim {A B : eqType} (f : A -> B) (l : seq A) (y : B) (i : nat) :
  nth_error (map f l) i = Some y -> exists x : A, (nth_error l i = Some x /\ f x = y).
Proof.
move:i. induction l as [|h l Hl];move=>[|i]//=.
move=>[<-]. by exists h.
move=>H. apply/Hl/H.
Qed.

Lemma tnth_nth_error {A : Type} (l : seq A) i : 
  Some (tnth (in_tuple l) i) = nth_error l i.
Proof.
induction l.
destruct i as [[|i] Hi] ; inversion Hi. 
destruct i as [[|i] Hi]. by apply/f_equal.
simpl.
rewrite -(IHl (Ordinal (n:=size l) (m:=i) Hi)).
(* both "calls" use different implicits *)
by rewrite (tnth_nth (tnth_default (in_tuple (a :: l)) (Ordinal Hi))) 
           (tnth_nth (tnth_default (in_tuple (a :: l)) (Ordinal Hi))).
Qed.

Lemma nth_error_size_leq {A : Type} (l : seq A) i :
  i < size l -> exists x : A, nth_error l i = Some x.
Proof.
move:i. induction l as [|h l Hl]. move=>//.
destruct i as [|i];move=>Hi. by exists h.
by apply Hl.
Qed. 

Lemma oob_nth_error {A : Type} (s : seq A) (ind : 'I_(size s)) : 
  nth_error s ind <> None.
Proof.
destruct ind as [ind Hind]. 
destruct (nth_error_size_leq Hind) as [x Hx].
by rewrite Hx.
Qed.

Lemma nth_error_leq_size {A : Type} (l : seq A) i :
  (exists x : A, nth_error l i = Some x) -> i < size l.
Proof.
move:i. induction l as [|h l Hl]; move=> [|i] [x Hx] //.
apply Hl. by exists x. 
Qed. 

Lemma nth_error_case {A : eqType} (l : seq A) (n:nat) : 
  nth_error l n = None \/ exists x, (x \in l) /\ nth_error l n = Some x.
Proof.
move:n.
induction l as [|h tl Hl];destruct n as [|n].
by left.
by left.
right. exists h. split. by rewrite in_cons ; apply/orP;left. auto.
simpl. destruct (Hl n) as [H|[x [Hx1 Hx2]]].
by left.
right. exists x. split. by rewrite in_cons ; apply/orP;right. auto.
Qed.

(** *** Equip the elements of a set with a property *)
(** Thanks to Arthur Azevedo De Amorim *)
Definition equip (T : finType) (P : pred T) (A : {set T}) : {set {x : T | P x}} :=
  [set x in pmap insub (enum A)].

(** ** bigop *)
Section bigop.

Lemma bigcup_type_seq {A B : finType} {f : A -> {set B}} : forall (x : B) z,
 x \in \bigcup_(y <- z) f y -> x \in \bigcup_y f y.
Proof.
move => x z /bigcup_seqP [a Haz /andP [Hxfa Htriv]]. 
apply/bigcupP. by exists a.
Qed.

End bigop.

Section Prod.

Lemma prod_eq {A B : Type} (x y : prod A B) : fst x = fst y -> snd x = snd y -> x = y.
Proof.
by case x;case y=>a b c d /= -> ->.
Qed.

End Prod.

(** *** Shifting operations on ordinals *)

(* TODO: use widen_ord from fintype.v *)
Section ord.

Lemma ord_shift {i : nat} : forall x : 'I_i, x.+1 < i.+1.
Proof.
move => x ; elim:x ; move => // m i0.
Qed.

Definition shift {i j : nat} (l : j.-tuple 'I_i) : j.-tuple 'I_(i.+1) := 
  [tuple of (map (fun (x : 'I_i) => @Ordinal i.+1 x.+1 (ord_shift x)) l)].

End ord.

(** *** pset: pmap for finsets *)

Definition pimset {A B : finType} (f : A -> option B) (s : {set A}) : {set B} :=
   [set id x | x in (pmap f [seq y | y in s])].

Definition pset {A : finType} (s : {set (option A)}) : {set A} := pimset id s.

Lemma mem_set_pset {A : finType} (x : A) (s : {set (option A)}) : Some x \in s -> x \in pset s.
Proof.
move => Hin.
apply/mem_imset.
rewrite mem_pmap.
apply (@map_f _ _ id). 
by rewrite mem_image.
Qed.

Lemma mem_pset_set {A : finType} (x : A) (s : {set (option A)}) : x \in pset s -> Some x \in s.
Proof.
move => /imsetP Hin.
destruct Hin as [a Hin Heq].
rewrite mem_pmap map_id in Hin.
destruct (imageP Hin) as [b Hbin Hbeq].
by rewrite Heq Hbeq.
Qed.

(** *** Prop version of all *)
Section all_prop.

Fixpoint all_prop (T : Type) (a : T -> Prop) (s : seq T) := match s with
  | [::] => True
  | x::s' => a x /\ all_prop a s' end.

Lemma all_prop_cat_l {A : Type} {P : A -> Prop} {l l' : seq A} (H : all_prop P (l ++ l')) : all_prop P l.
Proof.
by induction l ; [ | destruct H ; split ; [ | apply IHl] ].
Qed.

Lemma all_prop_cat_r {A : Type} {P : A -> Prop} {l l' : seq A} (H : all_prop P (l ++ l')) : all_prop P l'.
Proof.
by induction l ; [ | apply IHl ; destruct H].
Qed.

Lemma all_prop_cat {A : Type} {P : A -> Prop} {l l' : seq A} : 
  all_prop P (l ++ l') <-> all_prop P l /\ all_prop P l'.
Proof.
split.
- move => H ; split ; [apply (all_prop_cat_l H) | apply (all_prop_cat_r H)].
- move => [Hl Hr].
  induction l.
  + move => //.
  + destruct Hl as [Ha Hl]. split ; [apply Ha | apply (IHl Hl)].
Qed.

Lemma all_prop_in {A : eqType} {P : A -> Prop} {l : seq A} {x : A} 
  (Hp : all_prop P l) (Hin : x \in l) : P x.
Proof.
induction l.
- inversion Hin.
- unfold in_mem in Hin. simpl in Hin. destruct (orP Hin).
  + rewrite (eqP H). by destruct Hp.
  + apply IHl.
    - by destruct Hp.
    - apply H.
Qed.

Lemma all_prop_seq_decr {A : eqType} {P : A -> Prop}: 
  forall l1 l2, all_prop P l2 -> {subset l1 <= l2} -> all_prop P l1.
Proof.
induction l1.
- move => //.
- move => /= l2 Hp Hsub ; split.
  + assert (Hal2 : a \in l2).
    - apply/(Hsub a)/mem_head. 
    by apply (@all_prop_in A P l2 a).
  + apply IHl1 with (l2 := l2).
    - apply Hp.
    - move => x Hxl1. apply Hsub. unfold in_mem. simpl. apply/orP. by right.
Qed.

Lemma all_prop_prop_decr {A : eqType} (a1 a2 : A -> Prop) (s : seq A) : 
                      (all_prop a1 s) -> (forall x, x \in s -> a1 x -> a2 x) -> all_prop a2 s.
Proof.
induction s. auto. move=>[H1 H2] H. split. apply H. apply mem_head. apply H1. apply IHs. 
apply H2.
move=>x Hx. apply H. apply/mem_body/Hx.
Qed. 

Lemma fold_maxn_n_map_leq {A : Type} {w n : nat} {l : seq A} {f : A -> nat} :
  n <= w -> (all_prop (fun t => (f t <= w)) l) -> foldr maxn n (map f l) <= w.
Proof.
induction l;auto.
move=> Hn [Ha Hl] /=. 
rewrite geq_max ; apply/andP ; split.
- apply Ha.
- apply/IHl/Hl/Hn.
Qed.

Lemma fold_maxn_n_map_ltn {A : Type} {w n : nat} {l : seq A} {f : A -> nat} :
  n < w -> (all_prop (fun t => (f t < w)) l) -> foldr maxn n (map f l) < w.
Proof.
induction l;auto.
move=>Hn [Ha Hl] /=.
rewrite gtn_max ; apply/andP ; split.
- apply Ha.
- apply/IHl/Hl/Hn.
Qed.

Lemma sub_rem_seq {A : eqType} : forall (l : seq (seq A)) s h, 
all_prop (fun x : seq A => {subset x <= s}) [seq h :: i | i <- l] ->
all_prop (fun sl => h \notin sl) l -> 
all_prop (fun x : seq_predType A => {subset x <= rem h s}) l.
Proof.
move=> l s h H1 H2.
apply (all_prop_prop_decr H2)=>x Hx. 
apply sub_rem.
apply/(all_prop_in H1)/mapP.
by exists x. 
Qed.

Lemma sub_val_map (A : eqType) (P : pred A) (B : subType P) (l : seq A) 
          (ls : seq B) (Heq : l = map val ls) : 
          all_prop (fun x : A => exists px : P x, @Sub A P B x px \in ls) l.
Proof.
move: ls Heq.
induction l ; [ by [] | ].
move => ls Heq.
destruct ls ; [by inversion Heq | ].
inversion Heq as [[Haseq Hllseq]].
split.
- exists (valP s). 
  assert (Heqb : Sub (val s) (valP (sT:=B) s) == s).
  + rewrite <- inj_eq with (f := val). 
    - simpl ; apply/eqP. destruct B as [sub_sort val Sub Helim Hvseq]. simpl. by rewrite Hvseq.  
    - apply val_inj.
  rewrite (eqP Heqb) ; apply/mem_head.
- assert (Hsimpl : all_prop (fun x : A => exists px : P x, Sub x px \in ls)
  [seq val i | i <- ls]).
  + rewrite Hllseq in IHl. by apply IHl with (ls0 := ls).
  apply/all_prop_prop_decr. apply Hsimpl.
  move => x Hb Hfall.
  destruct Hfall as [Px] ; exists Px ; apply/mem_body/H.
Qed.

End all_prop.

(** *** Cartesian product *)
Definition setXn {A : finType} {m} (ss : m.-tuple {set A}) : 
  {set m.-tuple A} := [set x | [forall j in 'I_m, tnth x j \in tnth ss j]].