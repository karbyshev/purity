(****************************************************************)
(*  On monadic parametricity of second-order functionals        *)
(*  by Bauer A., Hofmann M., Karbyshev A.                       *)
(*                                                              *)
(*  Aleksandr Karbyshev                                         *)
(*  May 2012                                                    *)
(*  Build with Coq 8.4 + Ssreflect 1.4                          *)
(****************************************************************)

Require Import ssreflect ssrfun.
Require Import FunctionalExtensionality.
Set Automatic Coercions Import.
Require Import relations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Functional.
Variables A B C : Type.

Definition FuncType : Type :=
  forall (T : monadType), (A -> T B) -> T C.
End Functional.

Section Purity.
Variables A B C : Type.

Definition isPure (F : FuncType A B C) : Prop
  := forall (T T' : monadType) (TRacc : TRaccType T T'),
    ((IdR (X := A) =R=> (TR TRacc) _ _ (IdR (X := B))) =R=>
       (TR TRacc) _ _ (IdR (X := C))) (F T) (F T').
End Purity.

Section Strategy.
Variables A B C : Type.

Inductive Tree :=
  Ans : C -> Tree
| Que : A -> (B -> Tree) -> Tree.
End Strategy.

Section TreeMonad.
Variables A B : Type.

Fixpoint subst X Y (g : X -> Tree A B Y) (t : Tree A B X) :=
  match t with
    | Ans x => g x
    | Que a f => Que a (fun b => subst g (f b))
  end.

Definition TreeM : monadType.
exists (@Tree A B) (@Ans A B) (fun _ _ t f => @subst _ _ f t).
- by [].
- rewrite /Monad.axiom1 => X.
  elim => [// | a f IH /=].
  f_equal; by extensionality b.
- rewrite /Monad.axiom2 => X Y Z.
  elim => [// | a f IH /=].
  move => g h /=.
  f_equal; by extensionality b.
Defined.

(*Definition valTree := @tval (TreeM).
Definition bindTree := @tbind (TreeM).*)
End TreeMonad.

Section RepresentationTheorems.
Variables A B C : Type.

Definition fun2tree (F : FuncType A B C) : Tree A B C
  := F (TreeM _ _) (fun a => Que a (@Ans _ _ _)).

Fixpoint tree2funT (T : monadType) (t : Tree A B C) :=
  match t with
    | Ans c => fun k => tval T c
    | Que a f =>
        fun k => tbind (k a) (fun b => tree2funT T (f b) k)
  end.

Definition tree2fun (t : Tree A B C) : FuncType A B C.
move => T. by apply: (tree2funT t).
Defined.

Lemma tree2fun_simpl (t : Tree A B C) (T : monadType) :
  @tree2fun t T = tree2funT t.
Proof.
by rewrite /tree2fun.
Qed.

Lemma tree2fun_pure (t : Tree A B C) : isPure (@tree2fun t).
Proof.
rewrite /isPure.
elim: t => [| a f Hind].
- rewrite /ArrR. by intuition; apply TRacc.
- rewrite /ArrR /=. rewrite /ArrR /= in Hind.
  move => T T' TRacc k k' H /=.
  eapply (proj2 (Acc TRacc)); first by eapply H.
  rewrite /ArrR => b b' /=; elim. by apply: Hind.
Qed.

Lemma tree2fun2tree (t : Tree A B C) : fun2tree (tree2fun t) = t.
Proof.
rewrite /fun2tree.
elim: t => [// | a f Hind /=].
f_equal. by apply: functional_extensionality.
Qed.

Section TopTopMonadicRelation.
Variable T : monadType.
Variable f : A -> T B.

Definition RelTop X X' (R : Rel X X') : Rel (X -> TreeM A B C) (X' -> T C)
  := fun h h' =>
       forall x x', R x x' -> tree2fun (h x) f  = h' x'.

Definition RelTopTop X X' (R : Rel X X') : Rel (TreeM A B X) (T X')
  := fun t t' =>
       forall h h', RelTop R h h' -> tree2fun (tbind t h) f = tbind t' h' .

Definition TRacc1 : TRaccType (@TreeM A B) T.
exists RelTopTop.
split.
- rewrite /RelTopTop /RelTop /=.
  by intuition; rewrite taxiom0; auto.
- move => X X' Y Y' Q R g g' t t' H H0.
  rewrite /RelTopTop => h h' Hhh'. rewrite !taxiom2.
  apply: H. by firstorder.
Defined.

End TopTopMonadicRelation.

Theorem fun2tree2fun (F : FuncType A B C) (Hpure : isPure F) :
  forall (T : monadType), @tree2fun (fun2tree F) T = @F T.
Proof.
move => T.
extensionality f.
have H := @Hpure _ _ (TRacc1 f) => {Hpure}.
rewrite /fun2tree.
rewrite -[X in _ = X]taxiom1.
rewrite -[X in tree2fun X f]taxiom1.
have Harg : (IdR (X:=A) =R=>  TR (TRacc1 f) (IdR (X:=B))) (fun a => Que a (@Ans _ _ _)) f.
  move => a a'; elim.
  move => g g' Hgg' /=. f_equal.
  by extensionality b; intuition.
have Htmp := H _ _ Harg => {H Harg}.
apply: Htmp. by rewrite /RelTop => c c'; elim.
Qed.

End RepresentationTheorems.
