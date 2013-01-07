(****************************************************************)
(*  On monadic parametricity of second-order functionals        *)
(*  by Bauer A., Hofmann M., Karbyshev A.                       *)
(*                                                              *)
(*  Aleksandr Karbyshev                                         *)
(*  May 2012                                                    *)
(*  Build with Coq 8.4 + Ssreflect 1.4                          *)
(****************************************************************)

Require Import ssreflect ssrbool ssrfun ssrnat.
Set Automatic Coercions Import.
Require Import monads.
Require Import purity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import List.
Import ListNotations.

Section deps.
Variables A B C : Set.

Definition instr (T : monadType) (f : A -> T B)
  : A -> (StateT (list (A * B)) T) B
  := fun a l =>
       tbind (f a) (fun b => tval _ (b, (l ++ [(a,b)]))).

Fixpoint deps (t : Tree A B C) (f : A -> B) : list (A * B) :=
  match t with
    | Ans _ => nil
    | Que x k => let d := f x in (x, d) :: deps (k d) f
  end.

Definition deps_1 (t : Tree A B C) (f : A -> B) : list (A * B) :=
  let f' : A -> State (list (A * B)) B := @instr Id f in
    snd (tree2fun t f' []).

Lemma deps_1_app (t : Tree A B C) (f : A -> B)
                 (l : list (A * B)) :
  let f' : A -> State (list (A * B)) B := @instr Id f in
    snd (tree2fun t f' l) = l ++ snd (tree2fun t f' []).
Proof.
move => f'.
move: l.
elim: t => [c | a k IHt].
- move => l /=. now rewrite app_nil_r.
- move => l /=.
  rewrite IHt. rewrite <- app_assoc. now rewrite <- IHt.
Qed.

Lemma deps_are_same t f : deps t f = deps_1 t f.
Proof.
elim: t => [c | a k IHt].
- now rewrite /deps_1.
- now rewrite /= /deps_1 /= deps_1_app /= IHt.
Qed.
End deps.

Fixpoint max_seq_aux s accu :=
  match s with
    | [] => accu
    | x :: xs => max_seq_aux xs (maxn x accu)
  end.

Definition max_seq s := max_seq_aux s 0.

Lemma max_seq_aux_leq x s accu :
  x <= accu -> x <= max_seq_aux s accu.
Proof.
move: accu.
elim: s => [// | a s IH /= accu Hx].
apply: IH.
rewrite leq_max; now intuition.
Qed.

Lemma max_seq_aux_leq_accu s accu1 accu2 :
  accu1 <= accu2 -> max_seq_aux s accu1 <= max_seq_aux s accu2.
Proof.
move: accu1 accu2.
elim: s => [// | a s IH accu1 accu2 H /=].
apply: IH.
rewrite geq_max.
apply/andP.
split; [now apply: leq_maxl |
        apply: (leq_trans H); now apply: leq_maxr].
Qed.

Lemma max_seq_spec s :
  forall x, In x s -> x <= max_seq s.
Proof.
rewrite /max_seq.
elim: s => [// | a s IH].
move => x Hx.
case (in_inv Hx) as [e | H].
- rewrite e {e} //=. idtac.
  apply: max_seq_aux_leq. now apply: leq_maxl.
- apply: (leq_trans (IH _ H)).
  now apply: max_seq_aux_leq_accu.
Qed.

Fixpoint subtree A B C (t : Tree A B C) (path : list (A * B)) :=
  match t, path with
    | _, nil => Some t
    | Ans _, _ :: _ => None
    | Que x k, (_, b) :: ps => subtree (k b) ps
  end.

Lemma deps_subtree A B C (t : Tree A B C) sigma :
  let c := evaltree t sigma in
  subtree t (deps t sigma) = Some (@Ans A B C c).
Proof.
elim: t => [// | x k H].
move => c. now firstorder.
Qed.
Hint Resolve deps_subtree.

Lemma deps_compat A B C (t : Tree A B C) l f1 f2 :
  l = deps t f1 ->
  (forall p : A * B, (In p l) -> f1 (fst p) = f2 (fst p)) ->
  deps t f1 = deps t f2.
Proof.
move: l.
induction t as [| a k IH ]; auto.
- intros l H H0. subst l. rewrite /=.
  have e : f1 a = f2 a
    by apply: (H0 (a, f1 a)); firstorder.
  rewrite -e {e}.
  f_equal. eapply IH; eauto. now firstorder.
Qed.

Lemma deps_val_compat A B C (t : Tree A B C) l f1 f2 :
  l = deps t f1 ->
  (forall p, In p l -> f1 (fst p) = f2 (fst p)) ->
  evaltree t f1 = evaltree t f2.
Proof.
move => E H.
have Hdeps : deps t f1 = deps t f2
  by (eapply deps_compat; eauto).
have Hf1 := deps_subtree t f1; rewrite /= in Hf1.
have Hf2 := deps_subtree t f2; rewrite /= in Hf2.
rewrite -Hdeps Hf1 in Hf2.
now inversion Hf2.
Qed.

Definition modulus A B C (F : FuncType A B C) f : list (A * B)
  := let f' : A -> State (list (A * B)) B
         := @instr _ _ Id f in
       snd (F _ f' []).

Lemma modulus_corr A B C
        (F : FuncType A B C) (Hpure : is_pure F) f1 f2 m :
  m = modulus F f1 ->
  (forall p, In p m -> f1 (fst p) = f2 (fst p)) ->
  F Id f1 = F Id f2.
Proof.
move => Hm H.
pose t := proj1_sig Hpure.
have Ht : F = tree2fun t by (apply: proj2_sig Hpure).
rewrite !Ht.
rewrite /modulus Ht in Hm.
rewrite -/(deps_1 t f1) -deps_are_same in Hm.
now apply: (@deps_val_compat _ _ _ _ m).
Qed.

Definition modulus_max (F : FuncType nat nat bool) f : nat
  := let args := fst (split (modulus F f)) in max_seq args.

Lemma modulus_max_corr
        (F : FuncType nat nat bool) (Hpure : is_pure F) f1 f2 m :
  m = modulus_max F f1 ->
  (forall i, i <= m -> f1 i = f2 i) ->
  F Id f1 = F Id f2.
Proof.
move => Hm H.
rewrite /modulus_max in Hm.
apply: modulus_corr => //.
move => p Hp /=.
apply: H.
rewrite Hm.
apply: max_seq_spec.
now apply: in_split_l.
Qed.

