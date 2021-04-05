From mathcomp Require Import ssreflect ssrfun ssrbool.

(** Prove the following lemmas by providing explicit proof terms.
A bunch of exercises from the previous seminar we didn't have time
to cover have made it to this homework :) *)


(* An (unsound) placeholder so that the whole file typechecks.
Please replace it with your proof term. Your solutions may not
use any axioms, including `replace_with_your_solution_here` *)
Axiom replace_with_your_solution_here : forall {A : Type}, A.


Section Logic.

Variables A B C : Prop.

Locate "<->".
Print iff.
Locate "~".
Print not.

Definition falseIsNotTrue : False -> (~ True) := 
  fun f t => f.

Definition notTrueIsFalse : (~ True) -> False :=
  fun nt : ~ True => nt I.

(** * Exercise *)
Definition notTrue_iff_False : (~ True) <-> False :=
  conj (fun nt : ~ True => nt I) (fun f : False => fun t : True => f).

(* Hint 1: use [Locate "<->".] and [Print iff.] commands to understand better
the type above. *)

(* Hint 2: If you are experiencing an error like the following one
"Found a matching with no clauses on a term unknown to have an empty inductive type." try adding explicit type annotations to functional parameters or
use `match <term> in <type> with ... end` instead of `match <term> with ... end` *)


(** * Exercise: double negation elimination works for `False` *)
Definition dne_False : ~ ~ False -> False :=
  replace_with_your_solution_here.

(** * Exercise: double negation elimination works for `True` too. *)
Definition dne_True : ~ ~ True -> True :=
  fun _ => I.

(** * Exercise: Weak Peirce's law
Peirce's law (https://en.wikipedia.org/wiki/Peirce%27s_law) is equivalent to
Double Negation Elimination (and the Law of Excluded Middle too),
so it does not hold in general, but we can prove its weak form. *)
Definition weak_Peirce : ((((A -> B) -> A) -> A) -> B) -> B
:= replace_with_your_solution_here.

(* Hint 1: use let-in expression to break the proof into pieces and solve them independently *)
(* Hint 2: annotate the identifiers of let-expressions with types: [let x : <type> := ... in ...] *)


Variable T : Type.
Variable P Q : T -> Prop.

Locate "exists".
Print ex.

(** * Exercise: existential introduction rule *)
Definition exists_introduction :
  forall (x : T), P x -> (exists (x : T), P x)
:= fun x px => ex_intro P x px.

(** * Exercise: Frobenius rule: existential quantifiers and conjunctions commute *)
Definition frobenius_rule :
  (exists x, A /\ P x) <-> A /\ (exists x, P x)
:=
  conj (
    fun x_apx : exists x, A /\ P x =>
      match x_apx with
      | ex_intro x (conj a px) => conj a (ex_intro P x px)
      end
  ) (
    fun ax_px : A /\ (exists x, P x) =>
      match ax_px with
      | conj a (ex_intro x px) => ex_intro (fun x : T => A /\ P x) x (conj a px)
      end
  ).


End Logic.


Section Equality.

Variables A B C D : Type.

(** * Exercise *)
Definition eq1 : true = (true && true)
:= eq_refl : true = (true && true).

(** * Exercise *)
Definition eq2 : 42 = (if true then 21 + 21 else 239)
:= eq_refl : 42 = if true then 21 + 21 else 239.

(** * Exercise *)
Definition LEM_decidable :
  forall (b : bool), b || ~~ b = true
:=
  fun b =>
    match b with
    | true  => eq_refl : true || ~~ true = true
    | false => eq_refl : false || ~~ false = true
    end.

(** * Exercise *)
Definition if_neg :
  forall (A : Type) (b : bool) (vT vF : A),
    (if ~~ b then vT else vF) = if b then vF else vT
:=
  fun _ b vt vf =>
    match b with
    | true  => eq_refl : (if ~~ true then vt else vf)  = (if true then vf else vt)
    | false => eq_refl : (if ~~ false then vt else vf) = (if false then vf else vt)
    end.

(** * Exercise : associativity of function composition *)
(** [\o] is a notation for function composition in MathComp, prove that it's associative *)

Definition compA (f : A -> B) (g : B -> C) (h : C -> D) :
  (h \o g) \o f = h \o (g \o f)
:= eq_refl : (h \o g) \o f = h \o (g \o f).


(** [=1] stands for extensional equality on unary functions,
    i.e. [f =1 g] means [forall x, f x = g x].
    This means it's an equivalence relation, i.e. it's reflexive, symmetric and transitive.
    Let us prove a number of facts about [=1]. *)


(** * Exercise: Reflexivity *)
Definition eqext_refl :
  forall (f : A -> B), f =1 f
:= fun f a => eq_refl : f a = f a.

(** * Exercise: Symmetry *)
Definition eqext_sym :
  forall (f g : A -> B), f =1 g -> g =1 f
:=
  fun f g fg a =>
    match fg a in (_ = ga) return (ga = f a) with
    | eq_refl => eq_refl : f a = f a
    end.

(** * Exercise: Transitivity *)
Definition eqext_trans :
  forall (f g h : A -> B), f =1 g -> g =1 h -> f =1 h
:=
  fun f g h fg gh a =>
    match gh a in (_ = ha) return (f a = ha) with
    | eq_refl => fg a
    end.

(** * Exercise: left congruence *)
Definition eq_compl :
  forall (f g : A -> B) (h : B -> C),
    f =1 g -> h \o f =1 h \o g
:=
  fun f g h fg a =>
    match fg a in (_ = ga) return (h (f a) = h ga) with
    | eq_refl => eq_refl : h (f a) = h (f a)
    end.

(** * Exercise: right congruence *)
Definition eq_compr :
  forall (f g : B -> C) (h : A -> B),
    f =1 g -> f \o h =1 g \o h
:=
  fun f g h fg a =>
    match fg (h a) in (_ = ga) return (f (h a) = ga) with
    | eq_refl => eq_refl : f (h a) = f (h a)
    end.

End Equality.


(** * Extra exercises (feel free to skip) *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

(* After importing `eqtype` you need to either use a qualified name for
`eq_refl`: `Logic.eq_refl`, or use the `erefl` notation.
This is because `eqtype` reuses the `eq_refl` identifier for a
different lemma.
 *)

Definition iff_is_if_and_only_if :
  forall a b : bool, (a ==> b) && (b ==> a) = (a == b)
:= replace_with_your_solution_here.

Definition negbNE :
  forall b : bool, ~~ ~~ b = true -> b = true
:= replace_with_your_solution_here.
