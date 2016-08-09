Require Import Stlc.SpecSyntax.
Require Import UVal.UVal.

Inductive Prec : Set :=
| precise
| imprecise.

Inductive PTy : Set :=
| ptarr (τ₁ τ₂ : PTy)
| ptunit
| ptbool
| ptprod (τ₁ τ₂ : PTy)
| ptsum (τ₁ τ₂ : PTy)
| pEmulDV (n : nat) (p : Prec).

Inductive PEnv : Set :=
| pempty
| pevar (Γ : PEnv) (τ : PTy).

Fixpoint repEmul (τ : PTy) : Ty :=
  match τ with
    | ptarr τ₁ τ₂ => tarr (repEmul τ₁) (repEmul τ₂)
    | ptunit => tunit
    | ptbool => tbool
    | ptprod τ₁ τ₂ => tprod (repEmul τ₁) (repEmul τ₂)
    | ptsum τ₁ τ₂ => tsum (repEmul τ₁) (repEmul τ₂)
    | pEmulDV n p => UVal n
  end.

Fixpoint repEmulCtx (Γ : PEnv) : Env :=
  match Γ with
    | pempty => empty
    | pevar Γ τ => evar (repEmulCtx Γ) (repEmul τ)
  end.