(****************************************************************)
(*  On monadic parametricity of second-order functionals        *)
(*  by Bauer A., Hofmann M., Karbyshev A.                       *)
(*                                                              *)
(*  Aleksandr Karbyshev                                         *)
(*  May 2012                                                    *)
(*  Build with Coq 8.4 + Ssreflect 1.4                          *)
(****************************************************************)

Set Automatic Coercions Import.
Require Export monads.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition Rel X Y := X -> Y -> Prop.

Definition subRel X Y (R Q : Rel X Y) := forall x y, R x y -> Q x y.

Definition eqRel X Y (R Q : Rel X Y) := subRel R Q /\ subRel Q R.

Lemma subRel_refl X Y (R : Rel X Y) : subRel R R.
by firstorder.
Qed.

Lemma subRel_trans X Y (R Q S : Rel X Y) : subRel R Q -> subRel Q S -> subRel R S.
by firstorder.
Qed.

Definition compR X X' Y Y' (R : Rel Y Y') (f : X -> Y) (f' : X' -> Y') : Rel X X'
  := fun x x' => R (f x) (f' x').

Lemma compR_simpl X X' Y Y' (R : Rel Y Y') (f : X -> Y) (f' : X' -> Y') x x' :
  compR R f f' x x' = R (f x) (f' x').
Proof.
by [].
Qed.

(* TODO: we assume that relations are compatible with setoid equation *)
Axiom axiom_Rel_compat :
  forall (X Y : setoidType) (R : Rel X Y) x x' y y',
    x =-= x' -> y =-= y' -> R x y -> R x' y'.

Definition IdR : forall X : setoidType, Rel X X := fun X x x' => x =-= x'.

Lemma IdR_refl (X : setoidType) (x : X) : IdR x x.
Proof.
by rewrite /IdR.
Qed.
Hint Resolve IdR_refl.

Definition ArrR (X X' Y Y' : cpoType) (RX : Rel X X') (RY : Rel Y Y')
  : Rel (X -=> Y) (X' -=> Y')
  := fun f f' => forall x x', RX x x' -> RY (f x) (f' x').
Hint Unfold ArrR.

Definition ProdR (X X' Y Y' : cpoType) (RX : Rel X X') (RY : Rel Y Y')
  : Rel (X * Y) (X' * Y')
  := fun p p' => let (x,y) := p in let (x',y') := p' in RX x x' /\ RY y y'.
Hint Unfold ProdR.

Infix " =R=> " := ArrR (at level 60).
Infix " *R* " := ProdR (at level 55).

Lemma ProdR_elim (X X' Y Y' : cpoType) (R1 : Rel X X') (R2 : Rel Y Y') x y :
  (R1 *R* R2) x y -> R1 (FST _ _ x) (FST _ _ y) /\ R2 (SND _ _ x) (SND _ _ y).
Proof.
by case: x; case: y.
Qed.

Definition Gr (A B : cpoType) (f : A =-> B) : Rel A B
  := fun x y => f x =-= y.

Definition admissibleR (X Y : cpoType) (R : Rel X Y) :=
  forall (cx : natO =-> X) (cy : natO =-> Y), (forall n, R (cx n) (cy n)) -> R (lub cx) (lub cy).

Lemma admissibleIdR (X : cpoType) : admissibleR (@IdR X).
Proof.
move => c c' H. apply: lub_eq_compat. by apply: fmon_eq_intro.
Qed.

Lemma admissibleProdR (X X' Y Y' : cpoType) (RX : Rel X X') (RY : Rel Y Y') :
    admissibleR RX -> admissibleR RY -> admissibleR (RX *R* RY).
Proof.
move => HX HY. move => c1 c2 H /=.
split.
- apply: HX => n /=. by apply (ProdR_elim (H n)).
- apply: HY => n /=. by apply (ProdR_elim (H n)).
Qed.

Lemma admissibleArrR (X X' Y Y' : cpoType) (RX : Rel X X') (RY : Rel Y Y') :
    admissibleR RY -> admissibleR (RX =R=> RY).
Proof.
move => HY. move => c1 c2 H x x' Hxx'.
apply: HY => n /=. by apply H.
Qed.

Lemma fixpR_ind (X X' : cppoType) (R : Rel X X') (f : X =-> X) (f' : X' =-> X') :
    admissibleR R -> R PBot PBot -> (forall x x', R x x' -> R (f x) (f' x')) -> R (fixp f) (fixp f').
Proof.
move => Hadm HBot H. apply: Hadm. elim => //=; by auto.
Qed.

Module MonadicRelation.
Section axioms.
Variables T T' : monadType.

Definition TRelType : Type
  := forall X X' : cpoType, Rel X X' -> Rel (T X) (T' X').

Definition acceptableTR (TR : TRelType) : Prop :=
  (forall (X X' : cpoType) (R : Rel X X') (x : X) (x' : X'),
    R x x' -> TR X X' R (tval T _ x) (tval T' _ x')) /\
  (forall (X X' Y Y' : cpoType)
    (Q : Rel X X') (R : Rel Y Y')
    (f : X =-> T Y) (f' : X' =-> T' Y')
    (t : T X) (t' : T' X'),
    (TR X X' Q t t') -> (ArrR Q (TR Y Y' R) f f') -> TR Y Y' R (tbind T _ _ t f) (tbind T' _ _ t' f')).

Definition admissibleTR (TR : TRelType) : Prop :=
  forall (X X' : cpoType) (R : Rel X X'), admissibleR R -> admissibleR (TR X X' R).

Definition strictTR (TR : TRelType) : Prop :=
  forall (X X' : cpoType) (R : Rel X X'), (TR X X' R) PBot PBot.
End axioms.

(* Acceptable, admissible and strict monadic relation *)
Record goodTRel (T T' : monadType) : Type := GoodTRel {
  TRel :> TRelType T T';
  TRel_acc : acceptableTR TRel;
  TRel_adm : admissibleTR TRel;
  TRel_strict : strictTR TRel
}.
End MonadicRelation.

Notation TRelType := MonadicRelation.TRelType.
Notation TRelAccType := MonadicRelation.goodTRel.
Notation TRel := MonadicRelation.TRel.
Notation Acc :=  MonadicRelation.TRel_acc.
Notation Adm :=  MonadicRelation.TRel_adm.
Notation Str :=  MonadicRelation.TRel_strict.

