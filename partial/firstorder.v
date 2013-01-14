Set Automatic Coercions Import.
Require Import relations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Functional.
Variables A B : cpoType.

Definition FuncType : Type
  := forall (T : monadType), A =-> T B.
End Functional.

Module AcceptableFO.
Section axiom.
Variable T T' : monadType.

Definition TRtypeFO
  := forall (X X' : cpoType), Rel X X' -> Rel (T X) (T' X').

Definition acceptableTRFO (TR : TRtypeFO) : Prop :=
  forall (X X' : cpoType) (R : Rel X X') (x : X) (x' : X'),
    R x x' -> TR X X' R (tval T _ x) (tval T' _ x').
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
Variables A B : cpoType.

Definition isPure (f : FuncType A B) : Prop
  := forall (T T' : monadType) (TRacc : TRaccTypeFO T T'),
    (@IdR A =R=> (TRFO TRacc) _ _ (@IdR B)) (f T) (f T').
End Purity.

Section RepresentationTheorems.
Variables A B : cpoType.

Lemma lem_pure (g : A =-> B) : isPure (fun T => (@tval T _) << g).
Proof.
rewrite /isPure.
move => T T' TR a a' Heq.
rewrite /IdR in Heq.
apply: AccFO; rewrite /IdR.
by apply: (fcont_eq_compat (Oeq_refl _)).
Qed.

Require Import PredomLiftClassical.

Section TopTopMonadicRelation.
Variable T : monadType.

Definition RelTop (X X' : cpoType) (R : Rel X X')
  : Rel (X =-> T B) (X' =-> Lift B)
  := fun h h' =>
       forall x x', R x x' -> h x =-= mu1 (tval _ _) (h' x').

Definition RelTopTop (X X' : cpoType) (R : Rel X X')
  : Rel (T X) (Lift X')
  := fun t t' =>
       forall h h',
         RelTop R h h' ->
         tbind _ _ _ t h =-= mu1 (tval _ _) (kleisli h' t').

Definition TRacc1 : TRaccTypeFO T Lift.
exists RelTopTop.
rewrite /RelTopTop /RelTop /=.
move => X X' R /=.
move => x x' Hxx' h h' H.
by rewrite Monad.taxiom0 kleisliVal; auto.
Defined.
End TopTopMonadicRelation.

Theorem pure_is_pure (f : FuncType A B) (Hpure : isPure f) T :
  exists g : A =-> B _BOT, @f T =-= mu1 (tval _ _) << g.
Proof.
exists (@f Lift).
apply: fmon_eq_intro => a /=.
have H := Hpure _ _ (@TRacc1 T).
suff: ((f T) a =-= (mu1 (tval T B)) ((kleisli eta) ((f Lift) a)))
  by rewrite kleisli_unit.
rewrite -[X in X =-= _]taxiom1.
apply: H => //.
rewrite /RelTop /= => x x' H.
by rewrite mu1axiom2 H.
Qed.

End RepresentationTheorems.
