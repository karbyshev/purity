(****************************************************************)
(*  On monadic parametricity of second-order functionals        *)
(*  by Bauer A., Hofmann M., Karbyshev A.                       *)
(*                                                              *)
(*  Aleksandr Karbyshev                                         *)
(*  May 2012                                                    *)
(*  Build with Coq 8.4 + Ssreflect 1.4                          *)
(****************************************************************)

(* typeddensem.v
   Calculus specification and its denotational semantics
*)

Require Import ssreflect seq.
Set Automatic Coercions Import.
Require Export PredomAll.
Require Export monads.
Require Import stuff.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*Set Printing Width 65.*)

(* Types and contexts *)

Parameter baseType : Type.

Inductive Ty := Base (o : baseType) | Arrow (ty1 ty2 : Ty) | Prod (ty1 ty2 : Ty).
Infix " --> " := Arrow (at level 55, right associativity).
Infix " ** " := Prod (at level 55).
Definition Env := seq Ty.

(* Typed terms in context *)

Parameter Const : Ty -> Type.
(* Inductive Const : Ty -> Type :=
   | CONST : forall ty, Const ty. *)

Inductive Var : Env -> Ty -> Type := 
| ZVAR : forall env ty, Var (ty :: env) ty
| SVAR : forall env ty ty', Var env ty -> Var (ty' :: env) ty.

Inductive Exp : Env -> Ty -> Type :=
| TCONST : forall env ty, Const ty -> Exp env ty
| TVAR :> forall env ty, Var env ty -> Exp env ty
| TPAIR : forall env ty1 ty2, Exp env ty1 -> Exp env ty2 -> Exp env (ty1 ** ty2)
| TFST : forall env ty1 ty2, Exp env (ty1 ** ty2) -> Exp env ty1
| TSND : forall env ty1 ty2, Exp env (ty1 ** ty2) -> Exp env ty2
| TABS : forall env ty1 ty2, Exp (ty1 :: env) ty2 -> Exp env (ty1 --> ty2)
| TAPP : forall env ty1 ty2, Exp env (ty1 --> ty2) -> Exp env ty1 -> Exp env ty2
| TLET : forall env ty1 ty2, Exp env ty1 -> Exp (ty1 :: env) ty2 -> Exp env ty2
| TFIX : forall env ty1 ty2, Exp (ty1 :: ty1 --> ty2 :: env) ty2 -> Exp env (ty1 --> ty2).

Definition CExp t := Exp nil t.

Implicit Arguments TCONST [env].

(* Semantics of types and contexts *)

Section Semantics.

Variable T : monadType.

Parameter semBase : baseType -> monadType -> cpoType.

Fixpoint SemTy ty : cpoType :=
  match ty with
    | Base o => semBase o T
    | ty1 --> ty2 => SemTy ty1 -=> T (SemTy ty2)
    | ty1 ** ty2 => SemTy ty1 * SemTy ty2
  end.

Fixpoint SemEnv env : cpoType :=
  match env with
    | nil => One
    | ty :: env => SemEnv env * SemTy ty
  end.

Fixpoint SemVar env ty (var : Var env ty) : SemEnv env =-> SemTy ty :=
  match var with
    | ZVAR _ _ => SND _ _
    | SVAR _ _ _ v => SemVar v << FST _ _
  end.

(* Semantics of constants as a parameter *)
Parameter SemConst : forall ty, Const ty -> SemTy ty.

(* Semantics of values and expressions *)

Fixpoint SemExp env ty (e : Exp env ty) : SemEnv env =-> T (SemTy ty) :=
  match e with
    | TCONST _ _ c => const _ (tval _ _ (SemConst c))
    | TVAR _ _ v => tval _ _ << SemVar v
    | TABS _ _ _ e => tval _ _ << CURRY (SemExp e)
    | TAPP _ _ _ e1 e2 =>
        Comp2 (tbind _ _ _) (SemExp e1) (tbind _ _ _ << SemExp e2)
    | TPAIR _ _ _ e1 e2 =>
        Comp2 (tbind _ _ _) (SemExp e1)
          (Fcont_app
            (CURRY (CCOMP _ _ _) << tbind _ _ _ << SemExp e2)
            (CURRY (tval _ _))
          )
    | TFST _ _ _ e =>
        Fcont_app (tbind _ _ _ << SemExp e) (tval _ _ << FST _ _)
    | TSND _ _ _ e =>
        Fcont_app (tbind _ _ _ << SemExp e) (tval _ _ << SND _ _)
    | TLET _ _ _ e1 e2 => Comp2 (tbind _ _ _) (SemExp e1) (CURRY (SemExp e2))
    | TFIX _ _ _ e =>
        tval _ _ << FIXP << CURRY (CURRY (SemExp e))
  end.

End Semantics.

