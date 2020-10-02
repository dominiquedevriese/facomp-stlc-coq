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
            ∀ {C}, WsPCtx 0 0 C →
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

Lemma equivalenceReflectionDF {C₁ C₂ τᵢ τₒ} :
  ⟪ ⊢ C₁ : S.empty , τᵢ → S.empty , τₒ ⟫ ->
  ⟪ ⊢ C₂ : S.empty , τᵢ → S.empty , τₒ ⟫ ->
                                (* (⟨ ⊢ (compile_pctx τᵢ C₁) ≃ (compile_pctx τᵢ C₂) : dom Γᵢ → 0 ⟩). *)
  PCtxEquivalentCtx 0 (compile_pctx τᵢ C₁) (compile_pctx τᵢ C₂) ->
  ⟪ ⊢ C₁ ≃ C₂ : S.empty , τᵢ → τₒ  ⟫.
Proof.
  revert C₁ C₂ τᵢ τₒ.
  enough (forall (C₁ C₂ : Stlc.SpecSyntax.PCtx) (τᵢ τₒ : Ty),
            ⟪ ⊢ C₁ : S.empty, τᵢ → S.empty, τₒ ⟫ ->
            ⟪ ⊢ C₂ : S.empty, τᵢ → S.empty, τₒ ⟫ ->
            PCtxEquivalentCtx 0 (compile_pctx τᵢ C₁) (compile_pctx τᵢ C₂) ->
            forall (t : Tm), ⟪ S.empty ⊢ t : τᵢ ⟫ -> Stlc.SpecEvaluation.Terminating (Stlc.SpecSyntax.pctx_app t C₁) ->
              Stlc.SpecEvaluation.Terminating (Stlc.SpecSyntax.pctx_app t C₂)).
  {
    intros C₁ C₂ τᵢ τₒ tyC₁ tyC₂ seq t tyT.
    split.
    - intros termC₁.
      eapply (H C₁ C₂ τᵢ τₒ tyC₁ tyC₂ seq t tyT termC₁).
    - intros termC₂.
      refine (H C₂ C₁ τᵢ τₒ tyC₂ tyC₁ _ t tyT termC₂).
      eapply U.pctx_equiv_ctx_symm.
      intuition.
  }

  intros C₁ C₂ τᵢ τₒ tyC₁ tyC₂ seq t tyT term.

  destruct (S.Terminating_TerminatingN term) as [n termN]; clear term.
  unfold compile_pctx in seq.

  assert (⟪ ⊩ C₁ ⟦ dir_lt , S n ⟧ erase_pctx C₁ : pempty , embed τᵢ → pempty , embed τₒ ⟫) as lrC₁
  by (change pempty with (embedCtx (repEmulCtx pempty));
      eapply erase_ctx_correct; cbn; assumption).

  assert (⟪ pempty ⊩ t ⟦ dir_lt , S n ⟧ U.app (confine τᵢ) (erase t) : embed τᵢ ⟫) as lrct
  by (eapply confine_transp_open;
      change pempty with (embedCtx S.empty);
      eapply erase_correct;
      assumption).

  pose proof (proj2 lrC₁ _ _ lrct) as lrfull₁.

  assert (U.Terminating (U.pctx_app (U.app (confine τᵢ) (erase t)) (erase_pctx C₁))) as termU₁
  by (eapply (adequacy_lt lrfull₁ termN); eauto with arith).

  assert (U.Terminating (U.pctx_app (U.app (confine τᵢ) (erase t)) (erase_pctx C₂))) as termU₂.
  { specialize (seq (erase t)).
    rewrite ?pctx_cat_app in seq.
    eapply seq.
    change 0 with (dom S.empty).
    eapply (erase_scope _ _ _ tyT).
    cbn. assumption.
  }

  destruct (U.Terminating_TerminatingN termU₂) as [n₂ termUN₂].
  refine (adequacy_gt (n := S n₂) _ termUN₂ _); [|omega].

  assert (⟪ ⊩ C₂ ⟦ dir_gt , S n₂ ⟧ erase_pctx C₂ : pempty , embed τᵢ → pempty , embed τₒ ⟫) as lrC₂
  by (change pempty with (embedCtx (repEmulCtx pempty));
      eapply erase_ctx_correct; cbn; assumption).

  eapply (proj2 lrC₂).
  eapply confine_transp_open.
  change pempty with (embedCtx S.empty).
  eapply erase_correct.
  assumption.
Qed.

Lemma equivalencePreservationDF {C₁ C₂ τᵢ τₒ} :
  ⟪ ⊢ C₁ : S.empty , τᵢ → S.empty , τₒ ⟫ ->
  ⟪ ⊢ C₂ : S.empty , τᵢ → S.empty , τₒ ⟫ ->
                                (* (⟨ ⊢ (compile_pctx τᵢ C₁) ≃ (compile_pctx τᵢ C₂) : dom Γᵢ → 0 ⟩). *)
  ⟪ ⊢ C₁ ≃ C₂ : S.empty , τᵢ → τₒ  ⟫ ->
  PCtxEquivalentCtx 0 (compile_pctx τᵢ C₁) (compile_pctx τᵢ C₂).
Proof.
  revert C₁ C₂ τᵢ τₒ.
  enough (forall (C₁ C₂ : Stlc.SpecSyntax.PCtx) (τᵢ τₒ : Ty),
            ⟪ ⊢ C₁ : S.empty, τᵢ → S.empty, τₒ ⟫ ->
            ⟪ ⊢ C₂ : S.empty, τᵢ → S.empty, τₒ ⟫ ->
            ⟪ ⊢ C₁ ≃ C₂ : S.empty, τᵢ → τₒ ⟫ ->
            forall (t : UTm), wsUTm 0 t ->
                         (pctx_app t (compile_pctx τᵢ C₁))⇓ → (pctx_app t (compile_pctx τᵢ C₂)) ⇓ ).
  {
    intros C₁ C₂ τᵢ τₒ tyC₁ tyC₂ seq t tyT.
    split.
    - intros termC₁.
      eapply (H C₁ C₂ τᵢ τₒ tyC₁ tyC₂ seq t tyT termC₁).
    - intros termC₂.
      refine (H C₂ C₁ τᵢ τₒ tyC₂ tyC₁ _ t tyT termC₂).
      eapply S.pctx_equiv_ctx_symm.
      intuition.
  }

  intros C₁ C₂ τᵢ τₒ tyC₁ tyC₂ seq t tyT term.

  destruct (U.Terminating_TerminatingN term) as [n termN]; clear term.
  unfold compile_pctx in *.
  rewrite ?U.pctx_cat_app in *.
  cbn in *.

  assert (⟪ ⊩ C₁ ⟦ dir_gt , S n ⟧ erase_pctx C₁ : pempty , embed τᵢ → pempty , embed τₒ ⟫) as lrC₁
  by (change pempty with (embedCtx (repEmulCtx pempty));
      eapply erase_ctx_correct; cbn; assumption).

  assert (⟪ pempty ⊩ S.app (extract (S (S n)) τᵢ) (emulate (S (S n)) t) ⟦ dir_gt , S n ⟧ U.app (confine τᵢ) t : embed τᵢ ⟫) as lrct
  by (eapply extract_works_open;
      eauto using dwp_precise with arith;
      change pempty with (toEmulDV (S (S n)) precise 0);
      eapply emulate_works;
      eauto using dwp_precise with arith;
      assumption).

  pose proof (proj2 lrC₁ _ _ lrct) as lrfull₁.


  assert (S.Terminating (S.pctx_app (S.app (extract (S (S n)) τᵢ) (emulate (S (S n)) t)) C₁)) as termS₁
  by (eapply (adequacy_gt lrfull₁ termN); eauto with arith).

  assert (S.Terminating (S.pctx_app (S.app (extract (S (S n)) τᵢ) (emulate (S (S n)) t)) C₂)) as termS₂
  by (eapply seq;
    crushTyping;
    eauto using extractT;
    change S.empty with (toUVals (S (S n)) 0);
    eapply emulate_T;
    assumption).

  destruct (S.Terminating_TerminatingN termS₂) as [n₂ termSN₂].
  refine (adequacy_lt (n := S n₂) _ termSN₂ _); [|omega].

  assert (⟪ ⊩ C₂ ⟦ dir_lt , S n₂ ⟧ erase_pctx C₂ : pempty , embed τᵢ → pempty , embed τₒ ⟫) as lrC₂
  by (change pempty with (embedCtx (repEmulCtx pempty));
      eapply erase_ctx_correct; cbn; assumption).

  eapply lrC₂.
  eapply extract_works_open.
  - eauto using dwp_imprecise with arith.
  - change pempty with (toEmulDV (S (S n)) imprecise 0).
    eapply emulate_works; [|assumption].
    eauto using dwp_imprecise with arith.
Qed.

Lemma fullAbstractionDF {C₁ C₂ : Stlc.SpecSyntax.PCtx} {τᵢ τₒ} :
  ⟪ ⊢ C₁ : S.empty , τᵢ → S.empty , τₒ ⟫ ->
  ⟪ ⊢ C₂ : S.empty , τᵢ → S.empty , τₒ ⟫ ->
  ⟪ ⊢ C₁ ≃ C₂ : S.empty , τᵢ → τₒ  ⟫ ↔
                                (* (⟨ ⊢ (compile_pctx τᵢ C₁) ≃ (compile_pctx τᵢ C₂) : dom Γᵢ → 0 ⟩). *)
   PCtxEquivalentCtx 0 (compile_pctx τᵢ C₁) (compile_pctx τᵢ C₂).
Proof.
  intros.
  split;
  eauto using equivalencePreservationDF, equivalenceReflectionDF.
Qed.

Print Assumptions fullAbstraction.
Print Assumptions fullAbstractionDF.
