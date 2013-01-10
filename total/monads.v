(****************************************************************)
(*  On monadic parametricity of second-order functionals        *)
(*  by Bauer A., Hofmann M., Karbyshev A.                       *)
(*                                                              *)
(*  Aleksandr Karbyshev                                         *)
(*  May 2012                                                    *)
(*  Build with Coq 8.4 + Ssreflect 1.4                          *)
(****************************************************************)

Require Import ssreflect.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Automatic Coercions Import.

Module Monad.
Section Axioms.
Variable T : Type -> Type.
Variable val : forall X, X -> T X.
Variable bind : forall X Y, T X -> (X -> T Y) -> T Y.
Definition axiom0 := forall A B f a, @bind A B (val a) f = f a.
Definition axiom1 := forall A t, @bind A A t (@val A) = t.
Definition axiom2 := forall A B C t f g,
                       @bind B C (@bind A B t f) g = bind t (fun x => bind (f x) g).
End Axioms.
Definition axiom T val bind := @axiom0 T val bind /\ @axiom1 T val bind /\ @axiom2 T bind.

Record monad := Monad {
  T :> Type -> Type;
  tval : forall X, X -> T X;
  tbind : forall X Y, T X -> (X -> T Y) -> T Y;
  taxiom0 : @axiom0 T tval tbind;
  taxiom1 : @axiom1 T tval tbind;
  taxiom2 : @axiom2 T tbind
}.
End Monad.

Notation monadType := Monad.monad.
Notation tval := Monad.tval.
Notation tbind := Monad.tbind.
Notation taxiom0 := Monad.taxiom0.
Notation taxiom1 := Monad.taxiom1.
Notation taxiom2 := Monad.taxiom2.

Notation "'do' X '<-' A ; B" := (@tbind _ _ _ A (fun X => B))
                 (at level 200, X ident, A at level 100, B at level 200).

Definition Id : monadType.
exists
  (fun X => X)
  (fun X x => x)
  (fun X Y t f => f t); easy.
Defined.

Definition State (S : Type) : monadType.
exists
  (fun X => S -> X * S)
  (fun X => fun x s => (x, s))
  (fun X Y => fun t f =>
    fun s => let: (x1, s1) := t s in f x1 s1).
- rewrite /Monad.axiom0; intuition; by apply: functional_extensionality.
- rewrite /Monad.axiom1; intuition.
  extensionality s. by case: (t s).
- rewrite /Monad.axiom2; intuition.
  extensionality s. by case: (t s).
Defined.

Definition valState S := @tval (State S).
Definition bindState S := @tbind (State S).

Definition Cont (R : Type) : monadType.
exists
  (fun X => (X -> R) -> R)
  (fun X => fun x c => c x)
  (fun X Y => fun t f =>
    fun c => t (fun x => f x c)).
- rewrite /Monad.axiom0; intuition; by apply: functional_extensionality.
- rewrite /Monad.axiom1; by intuition.
- rewrite /Monad.axiom2; by intuition.
Defined.

Definition valCont R := @tval (Cont R).
Definition bindCont R := @tbind (Cont R).

Definition StateT (S : Type) (M : monadType) : monadType.
exists
  (fun X => S -> M (X * S)%type)
  (fun X => fun x s => tval _ (x,s))
  (fun X Y => fun t f =>
     fun s =>
       do p <- (t s);
       let (v,s') := p : (X * S)%type in f v s').
- rewrite /Monad.axiom0 => A B f a.
  extensionality s. now rewrite taxiom0.
- rewrite /Monad.axiom1 => A f.
  extensionality s.
  have H : forall X Y Z (f : X * Y -> Z),
             (fun p => let (x,y) := p : (X * Y)%type in f (x,y)) = f
  by (move => ? ? ? ?; now apply: functional_extensionality; case).
  rewrite H. now rewrite taxiom1.
- rewrite /Monad.axiom2 => A B C f g h.
  extensionality s. rewrite taxiom2. f_equal.
  now apply: functional_extensionality; case.
Defined.


