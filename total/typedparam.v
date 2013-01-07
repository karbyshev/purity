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

Require Import ssreflect seq.
Require Import relations.
Require Import typeddensem.
Require Import Coq.Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TypesRSem.

Variables T T' : monadType.
Variable TRacc : TRaccType T T'.

Parameter RSem_Base : forall (o : baseType), Rel (semBase o T) (semBase o T').

Fixpoint TRSemTy (ty : Ty) : Rel (SemTy T ty) (SemTy T' ty) :=
  match ty with
    | Base o => @RSem_Base o
    | ty1 --> ty2 =>
      (@TRSemTy ty1) =R=> (TR TRacc (@TRSemTy ty2))
    | ty1 ** ty2 => (@TRSemTy ty1) *R* (@TRSemTy ty2)
  end.

End TypesRSem.

Implicit Arguments TRSemTy [T T'].

Lemma parametricity
        T T' (TRacc : TRaccType T T') env
        (eta : SemEnv T env) (eta' : SemEnv T' env) :
    (forall ty (c : Const ty),
      TRSemTy TRacc _ (SemConst T c) (SemConst T' c)) ->
    (forall (ty : Ty) (v : Var env ty),
      TRSemTy TRacc _ (SemVar v eta) (SemVar v eta')) ->
    forall ty (e : Exp env ty),
    TR TRacc (TRSemTy TRacc ty) (SemExp e eta) (SemExp e eta').
Proof.
move => Hconst Hvar ty e.
induction e.

(* TCONST *)
- by apply: (proj1 (Acc TRacc)).

(* TVAR *)
- by apply: (proj1 (Acc TRacc)).

(* TABS *)
- move => /=.
  apply: (proj1 (Acc TRacc)).
  move => x x' Hxx'.
  apply: IHe => // ty v.
  by dependent destruction v => //=.

(* TAPP *)
- move => /=.
  apply: (proj2 (Acc TRacc)); first by auto.
  move => f f' Hff'.
  by apply: (proj2 (Acc TRacc)); auto.

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
  move => x x' Hxx' /=.
  apply: (proj1 (Acc TRacc)).
  by apply: (proj1 (ProdR_elim Hxx')).

(* TSND *)
- move => /=.
  apply: (proj2 (Acc TRacc)); first by auto.
  move => x x' Hxx' /=.
  apply: (proj1 (Acc TRacc)).
  by apply: (proj2 (ProdR_elim Hxx')).

(* TLET *)
- move => /=.
  apply: (proj2 (Acc TRacc)); first by auto.
  move => x x' Hxx' /=.
  apply: IHe2 => // ty v.
  by dependent destruction v => //=.
Qed.

Corollary ParametricityTheorem
            T T' (TRacc : TRaccType T T')
            (eta : SemEnv T [::]) (eta' : SemEnv T' [::]) :
    (forall ty (c : Const ty),
      TRSemTy TRacc _ (SemConst T c) (SemConst T' c)) ->
    forall ty (e : CExp ty),
    TR TRacc (TRSemTy TRacc ty) (SemExp e eta) (SemExp e eta').
Proof.
move => Hconst ty e.
apply: parametricity => //=.
move => {ty e Hconst} ty v.
by dependent destruction v.
Qed.

