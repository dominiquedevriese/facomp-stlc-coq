Require Export LogRel.PseudoType.
Require Import Stlc.SpecSyntax.
Require Import Stlc.SpecTyping.
Require Import Utlc.SpecSyntax.
Require Import Coq.Arith.Wf_nat.

Module S := Stlc.SpecSyntax.
Module U := Utlc.SpecSyntax.

Definition OfTypeStlc (τ : PTy) (t : S.Tm) : Prop :=
  ⟪ empty ⊢ t : repEmul τ ⟫.

Fixpoint OfTypeUtlc (τ : PTy) (t : U.UTm) : Prop :=
  match τ with
    | ptarr τ₁ τ₂ => exists t', t = abs t'
    | ptunit => t = U.unit
    | ptbool => t = U.true ∨ t = U.false
    | ptprod τ₁ τ₂ => exists t₁ t₂, t = U.pair t₁ t₂ ∧ OfTypeUtlc τ₁ t₁ ∧ OfTypeUtlc τ₂ t₂
    | ptsum τ₁ τ₂ => (exists t₁, t = U.inl t₁ ∧ OfTypeUtlc τ₁ t₁) ∨ (exists t₂, t = U.inr t₂ ∧ OfTypeUtlc τ₂ t₂)
    | pEmulDV n p => True
  end.

Definition OfType (τ : PTy) (t₁ : S.Tm) (t₂ : U.UTm) : Prop :=
  OfTypeStlc τ t₁ ∧ OfTypeUtlc τ t₂.

Definition World := nat.

Definition valrel'' 
           (w : World) (ind : forall w' : World, w' < w -> forall (τ : PTy) (t₁ : S.Tm) (t₂ : U.UTm), Prop)
           (τ : PTy)(t₁ : S.Tm) (t₂ : U.UTm) : Prop :=
  match τ with
    | ptarr τ₁ τ₂ => OfType (ptarr τ₁ τ₂) t₁ t₂ ∧ True
    | ptunit => t₁ = S.unit ∧ t₂ = U.unit
    | ptbool => (t₁ = S.true ∧ t₂ = U.true) ∨ (t₁ = S.false ∧ t₂ = U.false)
    | ptprod τ₁ τ₂ => OfType (ptprod τ₁ τ₂) t₁ t₂ ∧ True
    | ptsum τ₁ τ₂ => OfType (ptsum τ₁ τ₂) t₁ t₂ ∧ True
    | pEmulDV n p => OfType (pEmulDV n p) t₁ t₂ ∧ True
  end.

Definition valrel' (w : World) (τ : PTy)(t₁ : S.Tm) (t₂ : U.UTm) : Prop :=
  well_founded_induction_type (well_founded_ltof World (fun w => w))
                  (fun w => forall (τ : PTy) (t₁ : S.Tm) (t₂ : U.UTm), Prop)
                  valrel'' w τ t₁ t₂.
Definition valrel (τ : PTy) (w : World) (t₁ : S.Tm) (t₂ : U.UTm) : Prop :=
  valrel' w τ t₁ t₂.
  