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
Require Import FunctionalExtensionality.
Set Automatic Coercions Import.
Require Import relations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Functional.
Variable n : nat.
Variable A : 'I_n -> Set.
Variable B : 'I_n -> Set.
Variable C : Set.

Definition FuncType : Type :=
  forall (T : monadType), nProd (fun i => A i -> T (B i)) -> T C.
End Functional.

Section Purity.
Variable n : nat.
Variable A : 'I_n -> Set.
Variable B : 'I_n -> Set.
Variable C : Set.

Definition isPure (F : FuncType A B C) : Prop
  := forall (T T' : monadType) (TRacc : TRaccType T T'),
       (nProdR (fun i =>
         IdR (X := A i) =R=> (TR TRacc) _ _ (IdR (X := B i))) =R=>
          (TR TRacc) _ _ (IdR (X := C))) (F T) (F T').
End Purity.

Section Strategy.
Variable n : nat.
Variable A : 'I_n -> Set.
Variable B : 'I_n -> Set.
Variable C : Set.

Inductive Tree :=
  | Ans : C -> Tree
  | Que : forall i, A i -> (B i -> Tree) -> Tree.

Definition fun2tree (F : FuncType A B C)
  := F (Cont Tree) (tuple Que) Ans.

Fixpoint tree2funT (T : monadType) (t : Tree) :=
  match t with
    | Ans c => fun _ => @tval T _ c
    | Que i a f =>
        fun (k : nProd (fun i => A i -> T (B i))) =>
          tbind ((proj i k) a) (fun b => tree2funT T (f b) k)
  end.

Definition tree2fun (t : Tree) : FuncType A B C.
move => T. by refine (tree2funT t).
Defined.

Lemma tree2fun_simpl (t : Tree) (T : monadType) :
  @tree2fun t T = tree2funT t.
Proof.
by rewrite /tree2fun.
Qed.

Lemma tree2fun_pure (t : Tree) : isPure (@tree2fun t).
Proof.
rewrite /isPure.
elim: t => [ | i a f Hind].
- rewrite /ArrR. by intuition; apply TRacc.
- rewrite /ArrR /=. rewrite /ArrR /= in Hind.
  move => T T' TRacc k k' H /=.
  have Htmp := nProdR_elim H i.
  eapply (proj2 (Acc TRacc)); first by apply Htmp.
  rewrite /ArrR => b b' /=; elim. by apply: Hind.
Qed.

Lemma tree2fun2tree (t : Tree) : fun2tree (tree2fun t) = t.
Proof.
rewrite /fun2tree.
elim: t => [// | i a f Hind /=].
- f_equal. by apply: functional_extensionality.
Qed.

Section conversion.
Variable S : Type.
Variable q : nProd (fun i => A i -> (B i -> S) -> S).
Variable a : C -> S.

Definition conv (t : Tree) := @tree2funT (Cont S) t q a.

Definition TRacc1 : TRaccType (Cont Tree) (Cont S).
exists
  (fun X X' (R : Rel X X') => fun H H' =>
    forall h h', (R =R=> Gr conv) h h' -> Gr conv (H h) (H' h')).
split.
- by move => /=; intuition.
- move => X X' Y Y' Q R f f' t t' H H0.
  move => h h' Hhh'. apply: H => x x' Hxx'. by firstorder.
Defined.
End conversion.

Lemma fun2tree2fun_Cont S (F : FuncType A B C) (Hpure : isPure F) :
  @tree2funT (Cont S) (fun2tree F) = F (Cont S).
Proof.
extensionality q.
extensionality a.
suff H : Gr (conv q a) (F (Cont Tree) (tuple Que) Ans) (F (Cont S) q a); first by elim H.
have H := @Hpure _ _ (TRacc1 q a) => {Hpure}.
apply: H.
- elim: q => q i.
  move => a1 a1' /=; elim.
  move => h h' Hhh'.
  rewrite /Gr /conv /=.
  f_equal. extensionality b. by firstorder.
- by move => c c'; elim.
Qed.

Definition Phi (T : monadType)
               (F : nProd (fun i => A i -> Cont (T C) (B i)) -> Cont (T C) C)
  : nProd (fun i => A i -> T (B i)) -> T C.
elim => h.
by refine (F (tuple (fun i => (@tbind _ _ _) \o h i)) (@tval _ _)).
Defined.

Definition TRacc2 (T : monadType) : TRaccType (Cont (T C)) T.
exists
  (fun X X' (R : Rel X X') => fun H H' =>
    forall h h', (R =R=> @IdR (T C)) h h' ->
      (@IdR (T C) (H h) (tbind H' h'))).
split.
- move => X X' R x x' H h h' H1 /=. rewrite taxiom0. by intuition.
- move => X X' Y Y' Q R f f' t t' H H0.
  move => h h' Hhh'. rewrite taxiom2 //. apply: H => x x' Hxx'. by apply: H0.
Defined.

Lemma lem_Phi (T : monadType)
            (F : FuncType A B C) (Hpure : isPure F) :
  Phi (F (Cont (T C))) = F T.
Proof.
apply: functional_extensionality; case => g.
rewrite /Phi -[X in _ = X]taxiom1 /=.
have H := @Hpure _ _ (TRacc2 T) => {Hpure}.
apply: H.
- move => i a a'. elim. move => h h' Hhh'.
  suff Htmp: h = h'; first by rewrite Htmp.
  by extensionality x; apply: Hhh'.
- by move => c c'; elim.
Qed.

Theorem fun2tree2tree (F : FuncType A B C) (Hpure : isPure F) :
  forall (T : monadType), @tree2fun (fun2tree F) T = @F T.
Proof.
move => T.
rewrite -lem_Phi; last by apply: tree2fun_pure.
rewrite /tree2fun. rewrite fun2tree2fun_Cont //=.
by apply: lem_Phi.
Qed.

End Strategy.
