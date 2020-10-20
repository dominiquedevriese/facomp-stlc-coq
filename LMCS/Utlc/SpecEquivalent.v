Require Export Utlc.SpecScoping.
Require Export Utlc.SpecEvaluation.

Definition PCtxEquivalent (γ: Dom) (t₁ t₂: UTm) : Prop :=
  ∀ C,
    ⟨ ⊢ C : γ → 0 ⟩ →
    (pctx_app t₁ C)⇓ ↔ (pctx_app t₂ C)⇓.
Notation "⟨  γ ⊢ t₁ ≃ t₂ ⟩" :=
  (PCtxEquivalent γ t₁ t₂)
  (at level 0, γ at level 10, t₁ at level 10, t₂ at level 10).

Lemma pctx_equiv_symm {γ t₁ t₂} :
  ⟨ γ ⊢ t₁ ≃ t₂ ⟩ → ⟨ γ ⊢ t₂ ≃ t₁ ⟩.
Proof.
  unfold PCtxEquivalent.
  intros equiv C wsc; split;  
  apply (equiv C wsc).
Qed.