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

Definition URobustlyDivergentCtx (γᵢ : Dom) (C : U.PCtx) : Prop :=
  ∀ t,
    wsUTm γᵢ t ->
    (U.pctx_app t C) ⇑.

Definition SRobustlyDivergentCtx (Γᵢ : Env) (C : S.PCtx) (τᵢ τₒ : Ty) : Prop :=
  ∀ t ,
    ⟪ Γᵢ ⊢ t : τᵢ ⟫ →
    ¬ S.Terminating (S.pctx_app t C).


Lemma equivalenceReflection1DF {C τᵢ τₒ} :
  ⟪ ⊢ C : S.empty , τᵢ → S.empty , τₒ ⟫ ->
  URobustlyDivergentCtx 0 (compile_pctx τᵢ C) ->
  SRobustlyDivergentCtx S.empty C τᵢ τₒ.
Proof.
  intros tyC urd t tyT term.

  destruct (S.Terminating_TerminatingN term) as [n termN]; clear term.
  unfold compile_pctx in urd.

  assert (⟪ ⊩ C ⟦ dir_lt , S n ⟧ erase_pctx C : pempty , embed τᵢ → pempty , embed τₒ ⟫) as lrC₁
  by (change pempty with (embedCtx (repEmulCtx pempty));
      eapply erase_ctx_correct; cbn; assumption).

  assert (⟪ pempty ⊩ t ⟦ dir_lt , S n ⟧ U.app (confine τᵢ) (erase t) : embed τᵢ ⟫) as lrct
  by (eapply confine_transp_open;
      change pempty with (embedCtx S.empty);
      eapply erase_correct;
      assumption).

  pose proof (proj2 lrC₁ _ _ lrct) as lrfull.

  assert (U.Terminating (U.pctx_app (U.app (confine τᵢ) (erase t)) (erase_pctx C))) as termU
  by (eapply (adequacy_lt lrfull termN); eauto with arith).

  eapply (urd (erase t)).
  - change 0 with (dom S.empty).
    eapply (erase_scope _ _ _ tyT).
  - rewrite U.pctx_cat_app.
    cbn.
    assumption.
Qed.

Lemma equivalencePreservation1DF {C τᵢ τₒ} :
  ⟪ ⊢ C : S.empty , τᵢ → S.empty , τₒ ⟫ ->
  SRobustlyDivergentCtx S.empty C τᵢ τₒ ->
  URobustlyDivergentCtx 0 (compile_pctx τᵢ C).
Proof.
  intros tyC srd t tyT term.

  destruct (U.Terminating_TerminatingN term) as [n termN]; clear term.
  unfold compile_pctx in *.
  rewrite ?U.pctx_cat_app in *.
  cbn in *.

 assert (⟪ ⊩ C ⟦ dir_gt , S n ⟧ erase_pctx C : pempty , embed τᵢ → pempty , embed τₒ ⟫) as lrC
  by (change pempty with (embedCtx (repEmulCtx pempty));
      eapply erase_ctx_correct; cbn; assumption).

  assert (⟪ pempty ⊩ S.app (extract (S (S n)) τᵢ) (emulate (S (S n)) t) ⟦ dir_gt , S n ⟧ U.app (confine τᵢ) t : embed τᵢ ⟫) as lrct
  by (eapply extract_works_open;
      eauto using dwp_precise with arith;
      change pempty with (toEmulDV (S (S n)) precise 0);
      eapply emulate_works;
      eauto using dwp_precise with arith;
      assumption).

  pose proof (proj2 lrC _ _ lrct) as lrfull.

  assert (S.Terminating (S.pctx_app (S.app (extract (S (S n)) τᵢ) (emulate (S (S n)) t)) C)) as termS
  by (eapply (adequacy_gt lrfull termN); eauto with arith).

  refine (srd _ _ termS).
  crushTyping.
  - eapply extractT.
  - change S.empty with (toUVals (S (S n)) 0).
    eapply emulate_T.
    assumption.
Qed.

Lemma fullAbstraction1DF {C : Stlc.SpecSyntax.PCtx} {τᵢ τₒ} :
  ⟪ ⊢ C : S.empty , τᵢ → S.empty , τₒ ⟫ ->
  SRobustlyDivergentCtx S.empty C τᵢ τₒ <->
  URobustlyDivergentCtx 0 (compile_pctx τᵢ C).
Proof.
  intros.
  split;
  eauto using equivalencePreservation1DF, equivalenceReflection1DF.
Qed.

Print Assumptions fullAbstraction1DF.
