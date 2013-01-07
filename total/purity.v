(****************************************************************)
(*  On monadic parametricity of second-order functionals        *)
(*  by Bauer A., Hofmann M., Karbyshev A.                       *)
(*                                                              *)
(*  Aleksandr Karbyshev                                         *)
(*  May 2012                                                    *)
(*  Build with Coq 8.4 + Ssreflect 1.4                          *)
(****************************************************************)

Require Import ssreflect ssrfun.
Set Automatic Coercions Import.
Require Import relations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Functional.
Variables A B C : Set.

Definition FuncType : Type :=
  forall (T : monadType), (A -> T B) -> T C.
End Functional.

Section Purity.
Variables A B C : Set.

Definition isPure (F : FuncType A B C) : Prop
  := forall (T T' : monadType) (TRacc : TRaccType T T'),
    ((IdR (X := A) =R=> (TR TRacc) _ _ (IdR (X := B))) =R=>
       (TR TRacc) _ _ (IdR (X := C))) (F T) (F T').
End Purity.

Section Strategy.
Variables A B C : Set.

Inductive Tree :=
  Ans : C -> Tree
| Que : A -> (B -> Tree) -> Tree.

Definition fun2tree (F : FuncType A B C) := F (Cont Tree) Que Ans.

Fixpoint tree2funT (T : monadType) (t : Tree) :=
  match t with
    | Ans c => fun k => tval T c
    | Que a f =>
        fun k => tbind (k a) (fun b => tree2funT T (f b) k)
  end.

Definition tree2fun (t : Tree) : FuncType A B C.
move => T. by apply: (tree2funT t).
Defined.

Lemma tree2fun_simpl (t : Tree) (T : monadType) :
  @tree2fun t T = tree2funT t.
Proof.
by rewrite /tree2fun.
Qed.

Lemma tree2fun_pure (t : Tree) : isPure (@tree2fun t).
Proof.
rewrite /isPure.
elim: t => [| a f Hind].
- rewrite /ArrR. by intuition; apply TRacc.
- rewrite /ArrR /=. rewrite /ArrR /= in Hind.
  move => T T' TRacc k k' H /=.
  eapply (proj2 (Acc TRacc)); first by eapply H.
  rewrite /ArrR => b b' /=; elim. by apply: Hind.
Qed.

Lemma tree2fun2tree (t : Tree) : fun2tree (tree2fun t) = t.
Proof.
rewrite /fun2tree.
elim: t => [// | a f Hind /=].
f_equal. by apply: extensionality.
Qed.

Section conversion.
Variable S : Type.
Variable q : A -> (B -> S) -> S.
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
apply: extensionality => q. apply: extensionality => a.
suff H : Gr (conv q a) (F (Cont Tree) Que Ans) (F (Cont S) q a); first by elim: H.
rewrite /isPure in Hpure.
have H := @Hpure _ _ (TRacc1 q a) => {Hpure}.
apply: H.
- move => a1 a1' /=; elim. move => h h' Hhh'.
  rewrite /Gr /conv /=.
  f_equal. apply: extensionality => b. by firstorder.
- by move => c c'; elim.
Qed.

Definition Phi (T : monadType) (F : (A -> Cont (T C) B) -> Cont (T C) C)
  : (A -> T B) -> T C.
move => h. by refine (F ((@tbind _ _ _) \o h) (@tval _ _)).
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

Lemma lem_Phi (T : monadType) (F : FuncType A B C) (Hpure : isPure F) :
  Phi (F (Cont (T C))) = F T.
Proof.
apply: extensionality => g.
rewrite /Phi -[X in _ = X]taxiom1.
have H := @Hpure _ _ (TRacc2 T) => {Hpure}.
apply: H.
- move => a a'. elim. move => h h' Hhh'.
  suff Htmp: h = h'; first by rewrite Htmp.
  by apply: extensionality => x; apply: Hhh'.
- by move => c c'; elim.
Qed.

Theorem fun2tree2fun (F : FuncType A B C) (Hpure : isPure F) :
  forall (T : monadType), @tree2fun (fun2tree F) T = @F T.
Proof.
move => T.
rewrite -lem_Phi; last by apply: tree2fun_pure.
rewrite /tree2fun. rewrite fun2tree2fun_Cont //=.
by apply: lem_Phi.
Qed.

(* utils *)
Definition evaltree (t : Tree) (f : A -> B)
  := @tree2fun t Id f.

Lemma evaltree_Que x k f :
  evaltree (Que x k) f = evaltree (k (f x)) f.
Proof.
easy.
Qed.

Definition evaltree_unit (t : Tree) (f : A -> B)
  := fst ((@tree2fun t (State unit) ((@tval _ _) \o f)) tt).

Lemma evaltree_unit_Que x k f :
  evaltree_unit (Que x k) f = evaltree_unit (k (f x)) f.
Proof.
easy.
Qed.

Lemma evaltree_same (t : Tree) (f : A -> B) :
  evaltree t f = evaltree_unit t f.
Proof.
induction t; now firstorder.
Qed.

Definition is_pure (F : FuncType A B C)
  := {t : Tree | F = tree2fun t }.

End Strategy.
