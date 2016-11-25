Require Stlc.SpecSyntax.
Require Utlc.SpecSyntax.
Require Import BackTrans.UValHelpers.
Require Import Stlc.SpecTyping.
Require Import Stlc.StlcOmega.
Require Import Stlc.LemmasTyping.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.LemmasEvaluation.
Require Import Utlc.SpecScoping.
Require Import Utlc.LemmasScoping.
Require Import Utlc.LemmasEvaluation.
Require Import Utlc.DecideEval.
Require Import LogRel.PseudoType.
Require Import LogRel.LemmasPseudoType.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.
Require Import LogRel.LemmasIntro.
Require Import LogRel.LemmasInversion.
Require Import Omega.
Require Import Db.Lemmas.
Require Import UVal.UVal.
Require Utlc.Fix.
Require Omega.

Definition uvalApp_pctx₁ n ts₂ := S.papp₁ (S.papp₂ (S.abs (UVal n) (S.abs (UVal n) (S.app (caseArrUp n (S.var 1)) (S.var 0)))) S.phole) ts₂.
Definition uvalApp_pctx₂ n ts₁ := S.papp₂ (S.app (S.abs (UVal n) (S.abs (UVal n) (S.app (caseArrUp n (S.var 1)) (S.var 0)))) ts₁) S.phole.
Definition uvalApp n ts₁ ts₂ := S.app (S.app (S.abs (UVal n) (S.abs (UVal n) (S.app (caseArrUp n (S.var 1)) (S.var 0)))) ts₁) ts₂.

(* Arguments uvalApp_pctx₁ n ts₂ : simpl never. *)
(* Arguments uvalApp_pctx₂ n ts₁ : simpl never. *)
(* Arguments uvalApp n ts₁ ts₂ : simpl never. *)

Lemma uvalApp_T {n ts₁ ts₂ Γ} :
  ⟪ Γ ⊢ ts₁ : UVal n ⟫ →
  ⟪ Γ ⊢ ts₂ : UVal n ⟫ →
  ⟪ Γ ⊢ uvalApp n ts₁ ts₂ : UVal n ⟫.
Proof.
  unfold uvalApp.
  eauto with typing uval_typing.
Qed.

Lemma uvalApp_pctx₁_T {n ts₂ Γ} :
  ⟪ Γ ⊢ ts₂ : UVal n ⟫ →
  ⟪ ⊢ uvalApp_pctx₁ n ts₂ : Γ , UVal n → Γ , UVal n ⟫.
Proof.
  unfold uvalApp_pctx₁.
  eauto with typing uval_typing.
Qed.

Lemma uvalApp_pctx₂_T {n ts₁ Γ} :
  ⟪ Γ ⊢ ts₁ : UVal n ⟫ →
  ⟪ ⊢ uvalApp_pctx₂ n ts₁ : Γ , UVal n → Γ , UVal n ⟫.
Proof.
  unfold uvalApp_pctx₂.
  eauto with typing uval_typing.
Qed.

Hint Resolve uvalApp_T : uval_typing.
Hint Resolve uvalApp_pctx₁_T : uval_typing.
Hint Resolve uvalApp_pctx₂_T : uval_typing.

Local Ltac crush :=
  repeat (repeat crushUtlcSyntaxMatchH; 
          repeat crushStlcSyntaxMatchH; 
          repeat crushStlcEval; 
          repeat crushUtlcEvaluationMatchH; 
          repeat crushUtlcEvaluationMatchH2; 
          repeat crushUtlcEvaluationMatchH2; 
          repeat crushUtlcScopingMatchH;
          repeat crushDbSyntaxMatchH;
          repeat crushDbLemmasMatchH;
          repeat crushDbLemmasRewriteH;
          try assumption;
          crushOfType;
          trivial;
          eauto using caseUnit_pctx_ECtx, caseBool_pctx_ECtx, caseProd_pctx_ECtx, caseSum_pctx_ECtx, caseArr_pctx_ECtx, upgrade_value, downgrade_value with typing
         ).

Lemma uvalApp_sub {n ts₁ ts₂ γ} :
  (uvalApp n ts₁ ts₂) [γ] = uvalApp n (ts₁[γ]) (ts₂[γ]).
Proof.
  unfold uvalApp; cbn.
  crush; rewrite caseArrUp_sub;
  crush.
Qed.

Lemma termrel_uvalApp {d w n p ts₁ tu₁ ts₂ tu₂} :
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p) ts₁ tu₁ →
  (∀ w' : World, w' ≤ w → termrel d w' (pEmulDV n p) ts₂ tu₂) →
  termrel d w (pEmulDV n p) (uvalApp n ts₁ ts₂) (U.app tu₁ tu₂).
Proof.
  intros dwp tr₁ tr₂.
  unfold uvalApp, caseArrUp, caseArrUp_pctx.
  (* evaluate ts₁ and tu₁ *)
  eapply (termrel_ectx' tr₁); S.inferContext; U.inferContext; 
  unfold pctx_cat, U.ECtx; crush.

  (* continuation boilerplate *)
  intros w' futw vs₁ vu₁ vr₁.
  destruct (valrel_implies_OfType vr₁) as [[vvs₁ ?] [? ?]].
  rewrite S.pctx_cat_app; cbn.

  (* beta-reduce the outer let *)
  eapply termrel_antired_eval_left.
  eapply (S.eval_from_eval₀ (S.eval_beta vvs₁)); S.inferContext; crush.
  cbn; crush.

  (* bureaucracy *)
  fold (caseArr n (S.app (upgrade n 1) (S.var 1))).
  rewrite caseArr_sub; cbn; crush; rewrite upgrade_sub.

  (* evaluate ts₂ and tu₂ *)
  specialize (tr₂ w' futw).
  eapply (termrel_ectx' tr₂); S.inferContext; U.inferContext; 
  unfold pctx_cat, U.ECtx; crush.
  
  (* continuation boilerplate *)
  intros w'' futw' vs₂ vu₂ vr₂.
  destruct (valrel_implies_Value vr₂) as [vvs₂ ?].
  cbn.

  (* beta-reduce the remaining let *)
  eapply termrel_antired_eval_left.
  eapply (S.eval_from_eval₀ (S.eval_beta vvs₂)); S.inferContext; crush.
  cbn; crush.

  (* bureaucracy *)
  fold (caseArr n (S.app (upgrade n 1) (S.var 1))).
  rewrite ?caseArr_sub; cbn; crush; rewrite ?upgrade_sub.
  rewrite <- ?ap_liftSub; rewrite -> ?liftSub_wkm; rewrite (apply_wkm_beta1_cancel vs₁ vs₂).
  
  (* execute the upgrade *)
  assert (w'' ≤ w) by Omega.omega.
  assert (valrel d w'' (pEmulDV n p) vs₁ vu₁) by eauto using valrel_mono.
  assert (trupg : termrel d w'' (pEmulDV (n + 1) p) (S.app (upgrade n 1) vs₁) vu₁)
    by (eauto using upgrade_works', dwp_mono).
  unfold caseArr.
  eapply (termrel_ectx' trupg); S.inferContext; U.inferContext; cbn; crush.

  (* continuation bureaucracy *)
  intros w''' futw'' vs₁' vu₁' vr₁'.
  replace (n + 1) with (S n) in vr₁' by Omega.omega.

  destruct (valrel_implies_Value vr₁').
  (* case analysis *)
  eapply invert_valrel_pEmulDV_for_caseUValArr in vr₁'.
  destruct vr₁' as [(vs₁'' & ? & es & vr₁')|[(? & div)|(neq & div)]]; subst.
  - (* Correct case *)

    (* caseArr succeeds *)
    eapply termrel_antired_star_left.
    fold (caseArr n (inArr n vs₁'')).
    eapply (evalstar_ctx' es); S.inferContext; crush.
    cbn.

    (* application works *)
    eapply valrel_in_termrel in vr₁'.
    eapply (termrel_app vr₁').

    (* application argument is also fine *)
    eauto using valrel_in_termrel, valrel_mono.
  - (* unk case *) 
    eapply dwp_invert_imprecise in dwp; subst.
    eapply termrel_div_lt.
    fold (caseArr n vs₁').
    eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
  - (* other cases *)
    
    eapply termrel_div_wrong.
    + fold (caseArr n vs₁').
      eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
    + right.
      eapply evalToStar.
      eapply U.eval₀_to_eval.
      eauto with eval.
Qed.

Lemma uvalApp_pctx₁_app {n ts₁ ts₂} :
  S.pctx_app ts₁ (uvalApp_pctx₁ n ts₂) = uvalApp n ts₁ ts₂.
Proof.
  crush.
Qed.

Lemma uvalApp_pctx₂_app {n ts₁ ts₂} :
  S.pctx_app ts₂ (uvalApp_pctx₂ n ts₁) = uvalApp n ts₁ ts₂.
Proof.
  crush.
Qed.

Arguments uvalApp_pctx₁ n ts₂ : simpl never.
Arguments uvalApp_pctx₂ n ts₁ : simpl never.
Arguments uvalApp n ts₁ ts₂ : simpl never.