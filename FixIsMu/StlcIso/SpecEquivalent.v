Require Export StlcIso.SpecTyping.
Require Export StlcIso.SpecEvaluation.

Definition PCtxEquivalent (Γ: Env) (t₁ t₂: Tm) (τ: Ty) : Prop :=
  ∀ C τ',
    ⟪ i⊢ C : Γ , τ → empty, τ' ⟫ →
    (pctx_app t₁ C)⇓ ↔ (pctx_app t₂ C)⇓.
Notation "⟪  Γ i⊢ t₁ ≃ t₂ : τ  ⟫" :=
  (PCtxEquivalent Γ t₁ t₂ τ)
  (at level 0, Γ at level 98, t₁ at level 98, t₂ at level 98, τ at level 98).

Lemma pctx_equiv_symm {Γ t₁ t₂ τ} :
  ⟪ Γ i⊢ t₁ ≃ t₂ : τ ⟫ → ⟪ Γ i⊢ t₂ ≃ t₁ : τ ⟫.
Proof.
  unfold PCtxEquivalent.
  intros equiv C τ' ty; split;
  apply (equiv C τ' ty).
Qed.
