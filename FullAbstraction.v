Require Import Stlc.SpecTyping.
Require Import Stlc.SpecEquivalent.
Require Import Stlc.LemmasEvaluation.
Require Import Stlc.LemmasTyping.
Require Import Utlc.SpecEquivalent.
Require Import Utlc.LemmasEvaluation.

Require Import Compiler.Erase.
Require Import Compiler.Compiler.
Require Import Compiler.ProtectConfine.

Require Import UVal.UVal.

Require Import LogRel.PseudoType.
Require Import LogRel.LemmasPseudoType.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.

Require Import BackTrans.InjectExtract.
Require Import BackTrans.UpgradeDowngrade.
Require Import BackTrans.Emulate.

Require Import Omega.

Lemma equivalencePreservation {t₁ t₂ τ} :
  ⟪ S.empty ⊢ t₁ : τ ⟫ →
  ⟪ S.empty ⊢ t₂ : τ ⟫ →
  ⟪ S.empty ⊢ t₁ ≃ t₂ : τ ⟫ →
  ⟨ 0 ⊢ compile τ t₁ ≃ compile τ t₂ ⟩.
Proof.
  revert t₁ t₂ τ.
  enough (∀ {t₁ t₂ τ}, 
            ⟪ S.empty ⊢ t₁ : τ ⟫ →
            ⟪ S.empty ⊢ t₂ : τ ⟫ →
            ⟪ S.empty ⊢ t₁ ≃ t₂ : τ ⟫ →
            ∀ {C}, ⟨ ⊢ C : 0 → 0 ⟩ →
                 U.Terminating (U.pctx_app (compile τ t₁) C) → U.Terminating (U.pctx_app (compile τ t₂) C)) as Hltor
      by (intros t₁ t₂ τ ty1 ty2 ceq;
          assert (⟪ S.empty ⊢ t₂ ≃ t₁ : τ ⟫)
            by (apply S.pctx_equiv_symm; assumption);
          split;
          refine (Hltor _ _ _ _ _ _ _ _); assumption).
  intros t₁ t₂ τ ty₁ ty₂ ceq Cu sCu term.
  
  destruct (U.Terminating_TerminatingN term) as [n termN]; clear term.

  assert (⟪ pempty ⊩ t₁ ⟦ dir_gt , S n ⟧ erase t₁ : embed τ ⟫) as lre₁
      by (change pempty with (embedCtx (repEmulCtx pempty)); 
          eapply erase_correct;
          cbn; assumption).
  assert (⟪ pempty ⊩ S.app (inject (S (S n)) τ) t₁ ⟦ dir_gt , S n ⟧ U.app (protect τ) (erase t₁) : pEmulDV (S (S n)) precise ⟫) as lrpe₁
      by (eapply inject_works_open;
          eauto using dwp_precise with arith).
  fold (compile τ t₁) in lrpe₁.

  assert (⟪ ⊩ emulate_pctx (S (S n)) Cu ⟦ dir_gt , S n ⟧ Cu : 
              pempty , pEmulDV (S (S n)) precise → pempty , pEmulDV (S (S n)) precise ⟫) as lrem₁ by
      (change pempty with (toEmulDV (S (S n)) precise 0);
       eapply emulate_pctx_works; eauto using dwp_precise with arith).

  pose proof (proj2 lrem₁ _ _ lrpe₁) as lrfull₁.

  assert (S.Terminating (S.pctx_app (S.app (inject (S (S n)) τ) t₁)
                                    (emulate_pctx (S (S n)) Cu))) as termS
    by (eapply (adequacy_gt lrfull₁ termN); eauto with arith).

  change (S.app (inject (S (S n)) τ) t₁) with (S.pctx_app t₁ (S.papp₂ (inject (S (S n)) τ) S.phole)) in termS.
  rewrite <- S.pctx_cat_app in termS. 

  assert (⟪ ⊢ emulate_pctx (S (S n)) Cu : S.empty, UVal (S (S n)) → S.empty, UVal (S (S n)) ⟫)
    by (change S.empty with (toUVals (S (S n)) 0);
        eapply emulate_pctx_T; assumption).

  assert (S.Terminating (S.pctx_app t₂ (S.pctx_cat
                 (S.papp₂ (inject (S (S n)) τ) S.phole)
                 (emulate_pctx (S (S n)) Cu)))) as termS'
    by (eapply ceq; eauto;
        eapply pctxtyping_cat; crushTyping;
        eauto using injectT, emulate_pctx_T).

  destruct (S.Terminating_TerminatingN termS') as [m termSm']; clear termS'.

  assert (⟪ pempty ⊩ t₂ ⟦ dir_lt , S m ⟧ erase t₂ : embed τ ⟫) as lre₂
      by (change pempty with (embedCtx (repEmulCtx pempty)); 
          eapply erase_correct;
          cbn; assumption).
  assert (⟪ pempty ⊩ S.app (inject (S (S n)) τ) t₂ ⟦ dir_lt , S m ⟧ U.app (protect τ) (erase t₂) : pEmulDV (S (S n)) imprecise ⟫) as lrpe₂
      by (eapply inject_works_open;
          eauto using dwp_imprecise).
  fold (compile τ t₁) in lrpe₂.

  assert (⟪ ⊩ emulate_pctx (S (S n)) Cu ⟦ dir_lt , S m ⟧ Cu : 
              pempty , pEmulDV (S (S n)) imprecise → pempty , pEmulDV (S (S n)) imprecise ⟫) as lrem₂ by
      (change pempty with (toEmulDV (S (S n)) imprecise 0);
       eapply emulate_pctx_works; eauto using dwp_imprecise).

  pose proof (proj2 lrem₂ _ _ lrpe₂) as lrfull₂.
  rewrite S.pctx_cat_app in termSm'.

  eapply (adequacy_lt lrfull₂ termSm'); eauto with arith.
Qed.

Lemma fullAbstraction {t₁ t₂ τ} :
  ⟪ S.empty ⊢ t₁ : τ ⟫ →
  ⟪ S.empty ⊢ t₂ : τ ⟫ →
  ⟪ S.empty ⊢ t₁ ≃ t₂ : τ ⟫ ↔
  ⟨ 0 ⊢ compile τ t₁ ≃ compile τ t₂ ⟩.
Proof.
  intros.
  split;
  eauto using equivalenceReflection, equivalencePreservation.
Qed.

Print Assumptions fullAbstraction.