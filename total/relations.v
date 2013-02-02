(****************************************************************)
(*  On monadic parametricity of second-order functionals        *)
(*  by Bauer A., Hofmann M., Karbyshev A.                       *)
(*                                                              *)
(*  Aleksandr Karbyshev                                         *)
(*  May 2012                                                    *)
(*  Build with Coq 8.4 + Ssreflect 1.4                          *)
(****************************************************************)

Require Import ssreflect.
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
Set Automatic Coercions Import.
Require Export monads.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition Rel X Y := X -> Y -> Prop.

Definition SubRel X Y (R Q : Rel X Y)
  := forall x y, R x y -> Q x y.

Definition IdR : forall X, Rel X X := fun X x x' => x = x'.

Definition ArrR X X' Y Y' (RX : Rel X X') (RY : Rel Y Y')
  : Rel (X -> Y) (X' -> Y')
  := fun f f' => forall x x', RX x x' -> RY (f x) (f' x').

Definition ProdR X X' Y Y' (RX : Rel X X') (RY : Rel Y Y')
  : Rel (X * Y) (X' * Y')
  := fun p p' =>
       let (x,y) := p in
       let (x',y') := p' in RX x x' /\ RY y y'.
Hint Unfold ProdR.

Section nProd.
Variable n : nat.

Inductive nProd (X : 'I_n -> Type) : Type :=
  | tuple : forall (f : forall i :'I_n, X i), nProd X.

Definition proj X i (t : nProd X) :=
  let '(tuple f) := t in f i.

Definition nProdR (X : 'I_n -> Type) (X' : 'I_n -> Type)
                  (R : forall i : 'I_n, Rel (X i) (X' i))
  : Rel (nProd X) (nProd X')
  := fun t t' =>
       let '(tuple f) := t in
       let '(tuple f') := t' in
         forall i, R i (f i) (f' i).
End nProd.

Section nSum.
Variable n : nat.

Definition nSum (X : 'I_n -> Type) : Type := sigT X.

Definition inj (X : 'I_n -> Type) i x : nSum X := existT _ i x.
End nSum.

Infix " =R=> " := ArrR (at level 55).
Infix " *R* " := ProdR (at level 55).

Lemma ProdR_elim X X' Y Y' (RX : Rel X X') (RY : Rel Y Y') x y :
  (RX *R* RY) x y -> RX (fst x) (fst y) /\ RY (snd x) (snd y).
Proof.
by case x; case y.
Qed.

Lemma nProdR_elim n X X' R t t' :
  @nProdR n X X' R t t' -> forall i, R i (proj i t) (proj i t').
Proof.
by case: t; case: t'.
Qed.

Definition Gr A B (f : A -> B) : Rel A B
  := fun x y => f x = y.

Module Acceptable.
Section axiom.
Variable T T' : monadType.

Definition TRtype
  := forall X X', Rel X X' -> Rel (T X) (T' X').

Definition acceptableTR (TR : TRtype) : Prop :=
  (forall X X' (R : Rel X X') (x : X) (x' : X'),
    R x x' -> TR X X' R (tval T x) (tval T' x')) /\
    (forall X X' Y Y'
    (Q : Rel X X') (R : Rel Y Y')
    (f : X -> T Y) (f' : X' -> T' Y')
    (tx : T X) (tx' : T' X'),
    (TR X X' Q tx tx') -> (ArrR Q (TR Y Y' R) f f') -> TR Y Y' R (tbind tx f) (tbind tx' f')).
End axiom.

Record TRacc (T T' : monadType) := mkTRacc {
  TR :> TRtype T T';
  (*TR :> forall X X', Rel X X' -> Rel (T X) (T' X');*)
  axiomAcc :> acceptableTR TR
}.

End Acceptable.

Notation TRtype := Acceptable.TRtype.
Notation TRaccType := Acceptable.TRacc.
Notation TR := Acceptable.TR.
Notation Acc :=  Acceptable.axiomAcc.

Module StateAcceptable.
Section axiom.
Variables S S' : Type.
Definition TRtype
  := forall X X', Rel X X' -> Rel (State S X) (State S' X').

Definition acceptableTR (TR : TRtype) : Prop :=
  (forall X X' (R : Rel X X') (x : X) (x' : X'),
    R x x' -> TR X X' R (valState x) (valState x')) /\
    (forall X X' Y Y'
    (Q : Rel X X') (R : Rel Y Y')
    (f : X -> State S Y) (f' : X' -> State S' Y')
    (tx : State S X) (tx' : State S' X'),
    (TR X X' Q tx tx') -> (ArrR Q (TR Y Y' R) f f') -> TR Y Y' R (bindState tx f) (bindState tx' f')).
End axiom.

Record TRacc (S S' : Type) := mkTRacc {
  TR :> TRtype S S';
  axiomAcc :> acceptableTR TR
}.

End StateAcceptable.

Notation StateTRtype := StateAcceptable.TRtype.
Notation StateTRaccType := StateAcceptable.TRacc.
Notation StateTR := StateAcceptable.TR.
Notation StateAcc :=  StateAcceptable.axiomAcc.

Definition TRparam (S S' : Type) (R : Rel S S') : StateTRtype S S'
  := fun X X' Q =>  R =R=> (Q *R* R).

Definition TRparamAcc (S S' : Type) (P : Rel S S') : StateTRaccType S S'.
exists (TRparam P).
split; first by intuition.
move => X X' Y Y' Q R f f' tx tx' H Harr.
move => s s' Hss'.
rewrite /TRparam in H, Harr.
case e1 : (tx s) => [x1 s1].
case e1' : (tx' s') => [x1' s1'].
have H1 := H _ _ Hss' => {Hss' H}.
rewrite e1 e1' in H1.
elim: H1 => [HQ HR].
rewrite /bindState /tbind /= e1 e1'.
by apply: Harr.
Defined.
