Require Import Stlc.SpecTyping.
Require Import Stlc.SpecEquivalent.
Require Import Stlc.LemmasEvaluation.
Require Import Utlc.SpecEquivalent.
Require Import Utlc.LemmasEvaluation.

Require Import Compiler.Erase.
Require Import Compiler.ProtectConfine.

Require Import LogRel.PseudoType.
Require Import LogRel.LemmasPseudoType.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.

Require Import Omega.

Definition compile (τ : S.Ty) (t : S.Tm) : U.UTm :=
  U.app (protect τ) (erase t).

Lemma equivalenceReflection {t₁ t₂ τ} :
  ⟪ S.empty ⊢ t₁ : τ ⟫ →
  ⟪ S.empty ⊢ t₂ : τ ⟫ →
  ⟨ 0 ⊢ compile τ t₁ ≃ compile τ t₂ ⟩ →
  ⟪ S.empty ⊢ t₁ ≃ t₂ : τ ⟫.
Proof.
  revert t₁ t₂ τ.
  enough (∀ {t₁ t₂} τ, 
            ⟪ S.empty ⊢ t₁ : τ ⟫ →
            ⟪ S.empty ⊢ t₂ : τ ⟫ →
            ⟨ 0 ⊢ compile τ t₁ ≃ compile τ t₂ ⟩ →
            ∀ C τ', ⟪ ⊢ C : S.empty , τ → S.empty, τ' ⟫ →
                    S.Terminating (S.pctx_app t₁ C) → S.Terminating (S.pctx_app t₂ C)) as Hltor
      by (intros t₁ t₂ τ ty1 ty2 eq C τ';
          assert (⟨ 0 ⊢ compile τ t₂ ≃ compile τ t₁ ⟩)
            by (apply U.pctx_equiv_symm; assumption);
          split;
          refine (Hltor _ _ τ _ _ _ C τ' _); assumption).

  intros t₁ t₂ τ ty1 ty2 eq C τ' tyC term.

  destruct (S.Terminating_TerminatingN term) as [n termN]; clear term.

  assert (⟪ pempty ⊩ t₁ ⟦ dir_lt , S n ⟧ compile τ t₁ : embed τ ⟫) as lrt₁ by
      (unfold compile;
       apply protect_transp_open;
       exact (erase_correct ty1)).
  assert (⟪ ⊩ C ⟦ dir_lt , S n ⟧ erase_pctx C : pempty , embed τ → pempty , embed τ' ⟫) as lrC_lt
    by (apply (erase_ctx_correct tyC)).
  apply lrC_lt in lrt₁.

  assert (U.Terminating (U.pctx_app (compile τ t₁) (erase_pctx C)))
    as termu₁ by (apply (adequacy_lt lrt₁ termN); omega).

  assert (U.Terminating (U.pctx_app (compile τ t₂) (erase_pctx C)))
    by (apply eq; try assumption;
        apply (erase_pctx_scope C _ _ _ _ tyC)).

  destruct (U.Terminating_TerminatingN H) as [n' termN']; clear H.

  assert (⟪ ⊩ C ⟦ dir_gt , S n' ⟧ erase_pctx C : pempty , embed τ → pempty , embed τ' ⟫) as lrC_gt
    by (apply (erase_ctx_correct tyC)).
  assert (⟪ pempty ⊩ t₂ ⟦ dir_gt , S n' ⟧ compile τ t₂ : embed τ ⟫) as lrt₂ by
      (unfold compile;
       apply protect_transp_open;
       exact (erase_correct ty2)).
  apply lrC_gt in lrt₂.

  apply (adequacy_gt lrt₂ termN'); omega.
Qed.
