Require Export Utlc.SpecScoping.
Require Export Utlc.SpecEvaluation.

Definition PCtxEquivalent (γ: Dom) (t₁ t₂: UTm) : Prop :=
  ∀ C,
    ⟨ ⊢ C : γ → 0 ⟩ →
    (pctx_app t₁ C)⇓ ↔ (pctx_app t₂ C)⇓.
Notation "⟨  γ ⊢ t₁ ≃ t₂ ⟩" :=
  (PCtxEquivalent γ t₁ t₂)
  (at level 0, γ at level 10, t₁ at level 10, t₂ at level 10).

Definition PCtxEquivalentCtx (γᵢ : Dom) (C₁ C₂: PCtx) : Prop :=
  ∀ t,
    wsUTm γᵢ t ->
    (* ⟨ γᵢ ⊢ t ⟩ → *)
    (pctx_app t C₁)⇓ ↔ (pctx_app t C₂)⇓.
Notation "⟨ ⊢ C₁ ≃ C₂ : γᵢ → 0 ⟩" :=
  (PCtxEquivalentCtx γᵢ C₁ C₂)
  (at level 0, γᵢ at level 10, C₁ at level 10, C₂ at level 10).

Lemma pctx_equiv_symm {γ t₁ t₂} :
  ⟨ γ ⊢ t₁ ≃ t₂ ⟩ → ⟨ γ ⊢ t₂ ≃ t₁ ⟩.
Proof.
  unfold PCtxEquivalent.
  intros equiv C wsc; split;
  apply (equiv C wsc).
Qed.

Lemma pctx_equiv_ctx_symm {γᵢ C₁ C₂} :
  ⟨ ⊢ C₁ ≃ C₂ : γᵢ → 0 ⟩ ->
  ⟨ ⊢ C₂ ≃ C₁ : γᵢ → 0 ⟩.
Proof.
  intros equiv C wsc; split;
  apply (equiv C wsc).
Qed.
