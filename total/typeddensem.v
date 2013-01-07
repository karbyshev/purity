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

Require Import ssreflect ssrfun seq.
Set Automatic Coercions Import.
Require Export monads.
Require Export Program.Basics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Types and contexts *)

Parameter baseType : Type.

Inductive Ty := Base (o : baseType) | Arrow (ty1 ty2 : Ty) | Prod (ty1 ty2 : Ty).
Infix " --> " := Arrow (at level 55, right associativity).
Infix " ** " := Prod (at level 55).
Definition Env := seq Ty.

Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..) : list_scope.

(* Typed terms in context *)

Parameter Const : Ty -> Type.

Inductive Var : Env -> Ty -> Type := 
| ZVAR : forall env ty, Var (ty :: env) ty
| SVAR : forall env ty ty', Var env ty -> Var (ty' :: env) ty.

Inductive Exp : Env -> Ty -> Type :=
| TCONST : forall env ty, Const ty -> Exp env ty
| TVAR :> forall env ty, Var env ty -> Exp env ty
| TABS : forall env ty1 ty2,
    Exp (ty1 :: env) ty2 -> Exp env (ty1 --> ty2)
| TAPP : forall env ty1 ty2,
    Exp env (ty1 --> ty2) -> Exp env ty1 -> Exp env ty2
| TPAIR : forall env ty1 ty2,
    Exp env ty1 -> Exp env ty2 -> Exp env (ty1 ** ty2)
| TFST : forall env ty1 ty2, Exp env (ty1 ** ty2) -> Exp env ty1
| TSND : forall env ty1 ty2, Exp env (ty1 ** ty2) -> Exp env ty2
| TLET : forall env ty1 ty2, Exp env ty1 -> Exp (ty1 :: env) ty2 -> Exp env ty2.

Definition CExp t := Exp nil t.

Implicit Arguments TCONST [env].

(* Semantics of types and contexts *)

Section Semantics.

Variable T : monadType.

Parameter semBase : baseType -> monadType -> Type.

Fixpoint SemTy ty :=
  match ty with
    | Base o => semBase o T
    | ty1 --> ty2 => SemTy ty1 -> T (SemTy ty2)
    | ty1 ** ty2 => (SemTy ty1 * SemTy ty2)%type
  end.

Fixpoint SemEnv env : Type :=
  match env with
    | nil => unit
    | ty :: env => (SemEnv env * SemTy ty)%type
  end.

Fixpoint SemVar env ty (var : Var env ty) : SemEnv env -> SemTy ty :=
  match var with
    | ZVAR _ _ => @snd _ _
    | SVAR _ _ _ v => (SemVar v) \o @fst _ _
  end.

(* Semantics of constants as a parameter *)
Parameter SemConst : forall ty, Const ty -> SemTy ty.

(* Semantics of values and expressions *)

Notation curry := prod_uncurry.

Fixpoint SemExp env ty (e : Exp env ty) : SemEnv env -> T (SemTy ty) :=
  match e with
    | TCONST _ _ c => const (tval T (SemConst c))
    | TVAR _ _ v => (@tval T _) \o (SemVar v)
    | TABS _ _ _ e => compose (@tval T _) (curry (SemExp e))
    | TAPP _ _ _ e1 e2 =>
        fun eta => (tbind (SemExp e1 eta)) (tbind (SemExp e2 eta))
    | TPAIR eta0 t1 t2 e1 e2 =>
        fun eta =>
          tbind (SemExp e1 eta)
          ((tbind (SemExp e2 eta)) \o (curry (@tval T _)))
    | TFST _ _ _ e =>
        fun eta => tbind (SemExp e eta) ((@tval T _) \o (@fst _ _))
    | TSND _ _ _ e =>
        fun eta => tbind (SemExp e eta) ((@tval T _) \o (@snd _ _))
    | TLET _ _ _ e1 e2 =>
        fun eta => tbind (SemExp e1 eta) (curry (SemExp e2) eta)
  end.

End Semantics.

