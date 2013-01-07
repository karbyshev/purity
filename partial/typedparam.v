(****************************************************************)
(*  On monadic parametricity of second-order functionals        *)
(*  by Bauer A., Hofmann M., Karbyshev A.                       *)
(*                                                              *)
(*  Aleksandr Karbyshev                                         *)
(*  May 2012                                                    *)
(*  Build with Coq 8.4 + Ssreflect 1.4                          *)
(****************************************************************)

(* typedparam.v
   Parametricity theorem
*)

Set Automatic Coercions Import.
Require Import seq.
Require Import typeddensem.
Require Import relations.
Require Import Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TypesRSem.

Variables T T' : monadType.
Variable TRacc : TRelAccType T T'.

Parameter RSem_Base :
  forall (o : baseType), Rel (semBase o T) (semBase o T').
Parameter admissible_RSem_Base :
  forall (o : baseType), admissibleR (@RSem_Base o).

Fixpoint TRSemTy (ty : Ty) : Rel (SemTy T ty) (SemTy T' ty) :=
  match ty with
    | Base o => @RSem_Base o
    | ty1 --> ty2 =>
        (@TRSemTy ty1) =R=>
        (TRel TRacc (X:=SemTy T ty2) (X':=SemTy T' ty2) (@TRSemTy ty2))
    | ty1 ** ty2 => (@TRSemTy ty1) *R* (@TRSemTy ty2)
  end.

Lemma admissibleTRSemTy : forall ty, admissibleR (@TRSemTy ty).
elim => [o | ty1 Hty1 ty2 Hty2 | ty1 Hty1 ty2 Hty2].
- by apply: admissible_RSem_Base.
- rewrite /=. apply: admissibleArrR. by apply: (@Adm _ _ TRacc).
- rewrite /=. by apply: admissibleProdR.
Qed.

End TypesRSem.

Implicit Arguments TRSemTy [T T'].

Lemma parametricity
        T T' (TRacc : TRelAccType T T')
        env (eta : SemEnv T env) (eta' : SemEnv T' env) :
    (forall ty (c : Const ty),
      TRSemTy TRacc _ (SemConst T c) (SemConst T' c)) ->
    (forall ty (v : Var env ty),
      TRSemTy TRacc _ (SemVar T v eta) (SemVar T' v eta')) ->
    forall ty (e : Exp env ty),
      TRel TRacc (X:=SemTy T ty) (X':=SemTy T' ty)
        (TRSemTy TRacc _)
        (SemExp T e eta)
        (SemExp T' e eta').
Proof.
move => Hconst Hvar.
dependent induction e.

(* TCONST *)
- rewrite /=. by apply: (proj1 (Acc TRacc)).

(* TVAR *)
- rewrite /=. by apply: (proj1 (Acc TRacc)).

(* TPROD *)
- move => /=.
  apply: (proj2 (Acc TRacc)); first by auto.
  move => x x' Hxx' /=.
  apply: (proj2 (Acc TRacc)); first by auto.
  move => y y' Hyy' /=.
  by apply: (proj1 (Acc TRacc)).

(* TFST *)
- move => /=.
  apply: (proj2 (Acc TRacc)); first by auto.
  intros x x' Hxx' => /=.
  apply: (proj1 (Acc TRacc)).
  by apply: (proj1 (ProdR_elim Hxx')).

(* TSND *)
- move => /=.
  apply: (proj2 (Acc TRacc)); first by auto.
  intros x x' Hxx' => /=.
  apply: (proj1 (Acc TRacc)).
  by apply: (proj2 (ProdR_elim Hxx')).

(* TABS *)
- move => /=.
  apply: (proj1 (Acc TRacc)).
  intros x x' Hxx' => /=.
  apply: IHe => // ty v.
  by dependent destruction v => //=.

(* TAPP *)
- move => /=.
  apply: (proj2 (Acc TRacc)); first by auto.
  move => f f' Hff' => /=.
  by apply: (proj2 (Acc TRacc)); auto.

(* TLET *)
- move => /=.
  apply: (proj2 (Acc TRacc)); first by auto.
  move => f f' Hff' => /=.
  apply: IHe2 => //.
  move => ty v.
  by  dependent destruction v => //=.

(* TFIX *)
- move => /=.
  apply: (proj1 (Acc TRacc)).
  have Hadm : admissibleR (TRSemTy TRacc ty1 =R=> TRel TRacc (TRSemTy TRacc ty2)).
    apply: admissibleArrR. apply: (@Adm _ _ TRacc). by apply: admissibleTRSemTy.
  apply: (fixpR_ind Hadm).
  + move => x x' Hxx' /=. by apply: (Str TRacc).
  + move => f f' Hff' x x' Hxx' /=.
    apply: IHe => //.
    move => ty v.
    dependent destruction v => //=.
    by dependent destruction v => //=.
Qed.

Corollary ParametricityTheorem
            T T' (TRacc : TRelAccType T T')
            (eta : SemEnv T [::]) (eta' : SemEnv T' [::]) :
    (forall ty (c : Const ty),
      TRSemTy TRacc _ (SemConst T c) (SemConst T' c)) ->
    forall ty (e : CExp ty),
      TRel TRacc (X:=SemTy T ty) (X':=SemTy T' ty)
           (TRSemTy TRacc _)
           (SemExp T e eta)
           (SemExp T' e eta').
Proof.
move => Hconst ty e.
apply: parametricity => //.
move => {ty e Hconst} ty v.
by dependent destruction v.
Qed.
