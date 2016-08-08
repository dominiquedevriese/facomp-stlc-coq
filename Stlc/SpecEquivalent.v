Require Export Stlc.SpecTyping.
Require Export Stlc.SpecEvaluation.

Definition PCtxEquivalent (Γ: Env) (t₁ t₂: Tm) (τ: Ty) : Prop :=
  ∀ C τ',
    ⟪ ⊢ C : Γ , τ → empty, τ' ⟫ →
    (pctx_app t₁ C)⇓ ↔ (pctx_app t₂ C)⇓.
Notation "⟪  Γ ⊢ t₁ ≃ t₂ : τ  ⟫" :=
  (PCtxEquivalent Γ t₁ t₂ τ)
  (at level 0, Γ at level 10, t₁ at level 10, t₂ at level 10, τ at level 10).
