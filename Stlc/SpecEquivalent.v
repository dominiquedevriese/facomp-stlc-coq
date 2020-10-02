Require Export Stlc.SpecTyping.
Require Export Stlc.SpecEvaluation.

Definition PCtxEquivalent (Γ: Env) (t₁ t₂: Tm) (τ: Ty) : Prop :=
  ∀ C τ',
    ⟪ ⊢ C : Γ , τ → empty, τ' ⟫ →
    (pctx_app t₁ C)⇓ ↔ (pctx_app t₂ C)⇓.
Notation "⟪  Γ ⊢ t₁ ≃ t₂ : τ  ⟫" :=
  (PCtxEquivalent Γ t₁ t₂ τ)
  (at level 0, Γ at level 98, t₁ at level 98, t₂ at level 98, τ at level 98).

Lemma pctx_equiv_symm {Γ t₁ t₂ τ} :
  ⟪ Γ ⊢ t₁ ≃ t₂ : τ ⟫ → ⟪ Γ ⊢ t₂ ≃ t₁ : τ ⟫.
Proof.
  unfold PCtxEquivalent.
  intros equiv C τ' ty; split;
  apply (equiv C τ' ty).
Qed.

Definition PCtxEquivalentCtx (Γᵢ : Env) (C₁ C₂ : PCtx) (τᵢ τₒ : Ty) : Prop :=
  ∀ t ,
    ⟪ Γᵢ ⊢ t : τᵢ ⟫ →
    (pctx_app t C₁)⇓ ↔ (pctx_app t C₂)⇓.
Notation "⟪ ⊢ C₁ ≃ C₂ : Γᵢ , τᵢ → τₒ  ⟫" :=
  (PCtxEquivalentCtx Γᵢ C₁ C₂ τᵢ τₒ)
  (at level 0, Γᵢ  at level 98, C₁ at level 98, C₂ at level 98, τᵢ  at level 98, τₒ at level 98).

Lemma pctx_equiv_ctx_symm {Γᵢ C₁ C₂ τᵢ τₒ} :
  ⟪ ⊢ C₁ ≃ C₂ : Γᵢ , τᵢ → τₒ  ⟫ ->
  ⟪ ⊢ C₂ ≃ C₁ : Γᵢ , τᵢ → τₒ  ⟫.
Proof.
  intros equiv C wsc; split;
  apply (equiv C wsc).
Qed.
