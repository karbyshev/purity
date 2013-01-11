Require Import ssreflect ssrfun.
Set Automatic Coercions Import.
Require Import FunctionalExtensionality.
Require Import relations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Functional.
Variables A B : Type.

Definition FuncType : Type
  := forall (T : monadType), A -> T B.
End Functional.

Module AcceptableFO.
Section axiom.
Variable T T' : monadType.

Definition TRtypeFO
  := forall X X', Rel X X' -> Rel (T X) (T' X').

Definition acceptableTRFO (TR : TRtypeFO) : Prop :=
  forall X X' (R : Rel X X') (x : X) (x' : X'),
    R x x' -> TR X X' R (tval T x) (tval T' x').
End axiom.

Record TRaccFO (T T' : monadType) := mkTRacc {
  TR :> TRtypeFO T T';
  axiomAcc :> acceptableTRFO TR
}.

End AcceptableFO.

Notation TRtypeFO := AcceptableFO.TRtypeFO.
Notation TRaccTypeFO := AcceptableFO.TRaccFO.
Notation TRFO := AcceptableFO.TR.
Notation AccFO :=  AcceptableFO.axiomAcc.

Section Purity.
Variables A B : Type.

Definition isPure (f : FuncType A B) : Prop
  := forall (T T' : monadType) (TRacc : TRaccTypeFO T T'),
    (@IdR A =R=> (TRFO TRacc) _ _ (@IdR B)) (f T) (f T').
End Purity.

Section RepresentationTheorems.
Variables A B : Type.

Lemma lem_pure (g : A -> B) : isPure (fun T => (@tval T _) \o g).
Proof.
rewrite /isPure.
move => T T' TR a a'; elim => {a'}.
now apply: AccFO.
Qed.

Section TopTopMonadicRelation.
Variable T : monadType.

Definition RelTop X X' (R : Rel X X') : Rel (X -> T B) (X' -> B)
  := fun h h' =>
       forall x x', R x x' -> h x = tval _ (h' x').

Definition RelTopTop X X' (R : Rel X X') : Rel (T X) X'
  := fun t t' =>
       forall h h', RelTop R h h' -> tbind t h = tval _ (h' t').

Definition TRacc1 : TRaccTypeFO T Id.
exists RelTopTop.
rewrite /RelTopTop /RelTop /=.
move => X X' R /=. 
by intuition; rewrite taxiom0; auto.
Defined.

End TopTopMonadicRelation.

Theorem pure_is_pure (f : FuncType A B) (Hpure : isPure f) T :
  exists g : A -> B, @f T = (@tval _ _) \o g.
Proof.
exists (@f Id).
extensionality a => /=.
have H := Hpure _ _ (@TRacc1 T).
rewrite -[X in X = _]taxiom1.
apply : (H _ _ eq_refl (@tval _ _) id).
rewrite /RelTop /=.
by move => ? ?; elim.
Qed.

End RepresentationTheorems.
