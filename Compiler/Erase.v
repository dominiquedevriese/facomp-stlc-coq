Require Stlc.SpecSyntax.
Require Utlc.SpecSyntax.
Require Import Stlc.SpecTyping.
Require Import Stlc.LemmasTyping.
Require Import Utlc.SpecScoping.
Require Import Utlc.LemmasScoping.
Require Utlc.Fix.

Module SS := Stlc.SpecSyntax.
Module US := Utlc.SpecSyntax.
Module UF := Utlc.Fix.

Fixpoint erase (t : SS.Tm) : US.UTm :=
  match t with
    | SS.abs τ t         => US.abs (erase t)
    | SS.unit            => US.unit
    | SS.true            => US.true
    | SS.false           => US.false
    | SS.pair t₁ t₂      => US.pair (erase t₁) (erase t₂)
    | SS.inl t           => US.inl (erase t)
    | SS.inr t           => US.inr (erase t)
    | SS.var x           => US.var x
    | SS.app t₁ t₂       => US.app (erase t₁) (erase t₂)
    | SS.ite t₁ t₂ t₃    => US.ite (erase t₁) (erase t₂) (erase t₃)
    | SS.proj₁ t₁        => US.proj₁ (erase t₁)
    | SS.proj₂ t₁        => US.proj₂ (erase t₁)
    | SS.caseof t₁ t₂ t₃ => US.caseof (erase t₁) (erase t₂) (erase t₃)
    | SS.seq t₁ t₂       => US.seq (erase t₁) (erase t₂)
    | SS.fixt _ _ t₁     => US.app UF.ufix (erase t₁)
  end.

Fixpoint erase_pctx (C : SS.PCtx) : US.PCtx :=
  match C with
    | SS.phole => phole
    | SS.pabs τ C => US.pabs (erase_pctx C)
    | SS.papp₁ C t => US.papp₁ (erase_pctx C) (erase t) 
    | SS.papp₂ t C => US.papp₂ (erase t) (erase_pctx C)
    | SS.pite₁ C t₂ t₃ => US.pite₁ (erase_pctx C) (erase t₂) (erase t₃)
    | SS.pite₂ t₁ C t₃ => US.pite₂ (erase t₁) (erase_pctx C) (erase t₃)
    | SS.pite₃ t₁ t₂ C => US.pite₃ (erase t₁) (erase t₂) (erase_pctx C)
    | SS.ppair₁ C t => US.ppair₁ (erase_pctx C) (erase t)
    | SS.ppair₂ t C => US.ppair₂ (erase t) (erase_pctx C)
    | SS.pproj₁ C => US.pproj₁ (erase_pctx C)
    | SS.pproj₂ C => US.pproj₂ (erase_pctx C)
    | SS.pinl C => US.pinl (erase_pctx C)
    | SS.pinr C => US.pinr (erase_pctx C)
    | SS.pcaseof₁ C t₂ t₃ => US.pcaseof₁ (erase_pctx C) (erase t₂) (erase t₃)
    | SS.pcaseof₂ t₁ C t₃ => US.pcaseof₂ (erase t₁) (erase_pctx C) (erase t₃)
    | SS.pcaseof₃ t₁ t₂ C => US.pcaseof₃ (erase t₁) (erase t₂) (erase_pctx C)
    | SS.pseq₁ C t => US.pseq₁ (erase_pctx C) (erase t)
    | SS.pseq₂ t C => US.pseq₂ (erase t) (erase_pctx C)
    | SS.pfixt τ₁ τ₂ C => US.papp₂ UF.ufix (erase_pctx C)
  end.

Lemma erase_scope (t : SS.Tm) (Γ : SS.Env) (τ : SS.Ty) :
  ⟪ Γ ⊢ t : τ ⟫ -> ⟨ dom Γ ⊢ erase t ⟩.
Proof.
  intro wt; induction wt; crushUtlcScoping.
  apply UF.ufix_ws.
Qed.

Ltac apply_erase_scope :=
  match goal with
      [ H : ⟪ _ ⊢ ?t : _ ⟫ |- ⟨ _ ⊢ erase ?t ⟩ ] => refine (erase_scope _ _ _ H)
  end.

Lemma erase_pctx_scope (C : SS.PCtx) (Γ₀ Γ : SS.Env) (τ₀ τ : SS.Ty) :
  ⟪ ⊢ C : Γ₀ , τ₀ → Γ , τ ⟫ → ⟨ ⊢ erase_pctx C : dom Γ₀ → dom Γ ⟩.
Proof.
  intro wt; induction wt; crushUtlcScoping; try apply_erase_scope.
  apply UF.ufix_ws.
Qed.