Require Import Db.Lemmas.
Require Import Utlc.SpecSyntax.
Require Import Utlc.SpecEvaluation.
Require Import Utlc.LemmasScoping.
Require Import LogRel.PseudoType.
Require Import LogRel.LemmasPseudoType.
Require Import LogRel.LR.
Require Import Erase.
Require Import Common.Relations.

Fixpoint protect (ty : S.Ty) : U.UTm :=
  abs (match ty with
         | S.tunit => var 0
         | S.tbool => var 0
         | S.tarr ty1 ty2 => abs (app (protect ty2)[wkms 2] (app (var 1) (app (confine ty1)[wkms 2] (var 0))))
         | S.tprod ty1 ty2 => pair (app (protect ty1)[wkm] (proj₁ (var 0))) (app (protect ty2)[wkm] (proj₂ (var 0)))
         | S.tsum ty1 ty2 => caseof (var 0) (inl (app (protect ty1)[wkms 2] (var 0))) (inr (app (protect ty2)[wkms 2] (var 0)))
       end)
with confine (ty : S.Ty) : U.UTm :=
  abs (match ty with
         | S.tunit => seq (var 0) unit
         | S.tbool => ite (var 0) true false
         | S.tarr ty1 ty2 => abs (app (confine ty2)[wkms 2] (app (var 1) (app (protect ty1)[wkms 2] (var 0))))
         | S.tprod ty1 ty2 => pair (app (confine ty1)[wkm] (proj₁ (var 0))) (app (confine ty2)[wkm] (proj₂ (var 0)))
         | S.tsum ty1 ty2 => caseof (var 0) (inl (app (confine ty1)[wkms 2] (var 0))) (inr (app (confine ty2)[wkms 2] (var 0)))
       end).

Lemma protect_wkm_beta1 {τ tu} :
  (protect τ)[wkm][beta1 tu] = protect τ.
Proof. apply apply_wkm_beta1_cancel. Qed.

Lemma protect_wkm2_beta1 {τ tu} :
  (protect τ)[wkms 2][(beta1 tu)↑] = (protect τ)[wkm].
Proof. rewrite ap_comp; reflexivity. Qed.

Lemma confine_wkm_beta1 {τ tu} :
  (confine τ)[wkm][beta1 tu] = confine τ.
Proof. apply apply_wkm_beta1_cancel. Qed.

Lemma confine_wkm2_beta1 {τ tu} :
  (confine τ)[wkms 2][(beta1 tu)↑] = (confine τ)[wkm].
Proof. rewrite ap_comp; reflexivity. Qed.

Local Ltac crush :=
  repeat (cbn in *;
          subst*;
          repeat rewrite
            ?protect_wkm_beta1, ?protect_wkm2_beta1,
            ?confine_wkm_beta1, ?confine_wkm2_beta1,
            ?apply_up_def_O, ?apply_up_def_S;
          repeat crushUtlcScoping;
          repeat crushUtlcSyntaxMatchH;
          repeat crushUtlcEvaluationMatchH;
          repeat match goal with
                     [ |- _ ∧ _ ] => split
                   | [ |- OfType _ _ _ ] => unfold OfType, OfTypeStlc
                   | [ H: OfType _ _ _  |- _ ] => destruct H as [[? ?] ?]
                   | [ H: OfTypeStlc _ _  |- _ ] => destruct H as [? ?]
                 end;
          S.crushTyping;
          trivial
         ).

(* These should probably be made globally opaque
   in the Db library.
 *)
Local Opaque wkms.
Local Opaque up.

Lemma protect_closed {τ} : ⟨ 0 ⊢ protect τ ⟩
with confine_closed {τ}: ⟨ 0 ⊢ confine τ ⟩.
Proof.
  - induction τ; crush;
    try apply weakening; auto;
    try apply (weakenings 2); auto.
  - induction τ; crush;
    try apply weakening; auto;
    try apply (weakenings 2); auto.
Qed.

Lemma protect_confine_terminate {τ vu} :
  OfTypeUtlc (embed τ) vu →
  ∃ vu', U.Value vu' ∧
    ∀ Cu, U.ECtx Cu →
          (U.pctx_app (U.app (protect τ) vu) Cu) -->* (U.pctx_app vu' Cu).
Proof.
  revert vu.
  induction τ; crush.
  - (* ptarr τ₁ τ₂ *)
    destruct vu; crush.
    exists
      (abs
         (app
            (protect τ2)[wkm]
            (app
               (abs vu[wkm↑])
               (app (confine τ1)[wkm] (var 0))))).
    crush.
    apply evalToStar, U.eval_ctx₀; crush.
    apply U.eval_beta''; crush.
  - (* ptunit *)
    exists U.unit.
    crush.
    apply evalToStar, U.eval_ctx₀; crush.
    apply U.eval_beta''; crush.
  - (* ptbool *)
    assert (Value vu) by (destruct H; subst; crush).
    exists vu.
    crush.
    apply evalToStar, U.eval_ctx₀; crush.
    apply U.eval_beta''; crush.
  - (* ptprod *)
    destruct vu; try contradiction.
    destruct H as [ot1 ot2].
    specialize (IHτ1 vu1 ot1); destruct IHτ1 as (vu1' & vvu1' & hyp1).
    specialize (IHτ2 vu2 ot2); destruct IHτ2 as (vu2' & vvu2' & hyp2).
    exists (U.pair vu1' vu2'); crush.
    apply (evalStepStar
             (U.pctx_app
               (pair (app (protect τ1) (proj₁ (U.pair vu1 vu2)))
                  (app (protect τ2) (proj₂ (U.pair vu1 vu2))))
               Cu)).
    apply U.eval_ctx₀; crush.
    eapply U.eval_beta''; crush;
      eauto using OfTypeUtlc_implies_Value.
    apply (evalStepStar
             (U.pctx_app
                (pair (app (protect τ1) vu1)
                   (app (protect τ2) (proj₂ (U.pair vu1 vu2)))) Cu)).
    admit.
    apply (evalStepStar
             (U.pctx_app
                (pair vu1'
                   (app (protect τ2) (proj₂ (U.pair vu1 vu2)))) Cu)).
    admit.
    apply (evalStepStar
             (U.pctx_app
                (pair vu1'
                   (app (protect τ2) vu2)) Cu)).
    admit.
    admit.
  - (* ptsum *)
    destruct vu; try contradiction;
      [ rename IHτ1 into IH | rename IHτ2 into IH ];
      specialize (IH vu H); destruct IH as (vu' & vvu' & hyp);
      assert (vvu: Value vu) by eauto using OfTypeUtlc_implies_Value;
      exists vu'; crush.
    + apply (evalStepStar
               (U.pctx_app
                  (caseof
                     (U.inl vu)
                     (inl (app (protect τ1)[wkm] (var 0)))
                     (inr (app (protect τ2)[wkm] (var 0))))
                  Cu)).
      apply U.eval_ctx₀; crush.
      apply U.eval_beta''; crush.
      apply (evalStepStar
               (U.pctx_app
                 (inl (app (protect τ1) vu))
                 Cu)).
      apply U.eval_ctx₀; crush.
      eapply eval₀_case_inl'; crush.
      admit.
    + apply (evalStepStar
               (U.pctx_app
                  (caseof
                     (U.inr vu)
                     (inl (app (protect τ1)[wkm] (var 0)))
                     (inr (app (protect τ2)[wkm] (var 0))))
                  Cu)).
      apply U.eval_ctx₀; crush.
      apply U.eval_beta''; crush.
      apply (evalStepStar
               (U.pctx_app
                 (inr (app (protect τ2) vu))
                 Cu)).
      apply U.eval_ctx₀; crush.
      eapply eval₀_case_inr'; crush.
      admit.
Admitted.
