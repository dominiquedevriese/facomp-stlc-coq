Require Import Db.Lemmas.
Require Import Utlc.SpecSyntax.
Require Import Utlc.SpecEvaluation.
Require Import Utlc.LemmasEvaluation.
Require Import Utlc.LemmasScoping.
Require Import Utlc.Inst.
Require Import Utlc.DecideEval.
Require Import Stlc.CanForm.
Require Import LogRel.PseudoType.
Require Import LogRel.LemmasPseudoType.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.
Require Import LogRel.LemmasIntro.
Require Import LogRel.LemmasInversion.
Require Import Erase.
Require Import Common.Relations.
Require Import Compiler.Erase.

Require Import Omega.

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
            ?apply_wkm_beta1_up_cancel,
            ?apply_up_def_S;
          repeat crushDbLemmasMatchH;
          repeat crushDbSyntaxMatchH;
          repeat crushUtlcEvaluationMatchH2;
          repeat crushUtlcEvaluationMatchH;
          repeat crushUtlcScopingMatchH;
          repeat crushUtlcSyntaxMatchH;
          repeat crushUtlcSyntaxMatchH;
          repeat S.crushStlcSyntaxMatchH;
          repeat S.crushTypingMatchH2;
          repeat S.crushTypingMatchH;
          crushOfType;
          repeat match goal with
                     [ |- _ ∧ _ ] => split
                   (* | [ |- OfType _ _ _ ] => unfold OfType, OfTypeStlc *)
                   (* | [ H: OfType _ _ _  |- _ ] => destruct H as [[? ?] ?] *)
                   (* | [ H: OfTypeStlc _ _  |- _ ] => destruct H as [? ?] *)
                 end;
          repeat valrelIntro;
          trivial
         ); eauto with ws; try omega.
(* These should probably be made globally opaque
   in the Db library.
 *)
Local Opaque wkms.
Local Opaque up.

Lemma protect_Value {τ} : Value (protect τ).
Proof.
  destruct τ; now cbn.
Qed.

Lemma confine_Value {τ} : Value (confine τ).
Proof.
  destruct τ; now cbn.
Qed.


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

Lemma protect_prod {τ1 τ2 vu1 vu2 vu1' vu2'} :
      Value vu1 → Value vu2 → Value vu1' → Value vu2' →
      ctxevalStar (app (protect τ1) vu1) vu1' →
      ctxevalStar (app (protect τ2) vu2) vu2' →
      ctxevalStar (app (protect (S.tprod τ1 τ2)) (pair vu1 vu2)) (pair vu1' vu2').
Proof.
  intros vv1 vv2 vv1' vv2' hyp1 hyp2.
  (* it would be nice if we could automate the following argument some more... Perhaps improve DecideEval with vi_Terminates ... somehow? *)
  apply (evalStepStar
           (pair (app (protect τ1) (proj₁ (U.pair vu1 vu2)))
                 (app (protect τ2) (proj₂ (U.pair vu1 vu2))))).
  apply U.eval₀_ctxeval; crush.
  eapply U.eval_beta''; crush;
  eauto using OfTypeUtlc_implies_Value.
  apply (evalStepStar
           (pair (app (protect τ1) vu1)
                 (app (protect τ2) (proj₂ (U.pair vu1 vu2))))).

  assert (e₀ : U.proj₁ (U.pair vu1 vu2) -->₀ vu1) by (eauto with eval).
  eapply (ctxeval_from_eval₀ e₀); repeat inferContext; crush; eauto using protect_Value.

  pose (hyp1' := extend_ctxevalStar (ppair₁ phole (app (protect τ2) (proj₂ (U.pair vu1 vu2)))) I hyp1).
  simpl in hyp1'.
  apply (evalStepTrans (pair vu1' (app (protect τ2) (proj₂ (U.pair vu1 vu2)))) hyp1').

  apply (evalStepStar (pair vu1' (app (protect τ2) vu2))).
  assert (e₀ : U.proj₂ (U.pair vu1 vu2) -->₀ vu2) by (eauto with eval).
  eapply (ctxeval_from_eval₀ e₀); repeat inferContext; crush; eauto using protect_Value.

  assert (eC' : ECtx (ppair₂ vu1' phole)) by crush.
  pose (hyp2' := extend_ctxevalStar (ppair₂ vu1' phole) eC' hyp2).
  simpl in hyp2'.
  exact hyp2'.

Qed.

Lemma protect_inl {τ1 τ2 vu vu' } :
      Value vu → Value vu' →
      ctxevalStar (app (protect τ1) vu) vu' →
      ctxevalStar (app (protect (S.tsum τ1 τ2)) (inl vu)) (inl vu').
Proof.
  intros vv vv' hyp.
  apply (evalStepStar (caseof
                   (U.inl vu)
                   (inl (app (protect τ1)[wkm] (var 0)))
                   (inr (app (protect τ2)[wkm] (var 0))))).

  apply U.eval₀_ctxeval; crush.
  apply U.eval_beta''; crush.

  apply (evalStepStar (inl (app (protect τ1) vu))).
  apply U.eval₀_ctxeval; crush.
  eapply eval₀_case_inl'; crush.

  refine (extend_ctxevalStar (pinl phole) I hyp).
Qed.

Lemma protect_inr {τ1 τ2 vu vu' } :
      Value vu → Value vu' →
      ctxevalStar (app (protect τ2) vu) vu' →
      ctxevalStar (app (protect (S.tsum τ1 τ2)) (inr vu)) (inr vu').
Proof.
  intros vv vv' hyp.
  apply (evalStepStar (caseof
                   (U.inr vu)
                   (inl (app (protect τ1)[wkm] (var 0)))
                   (inr (app (protect τ2)[wkm] (var 0))))).

  apply U.eval₀_ctxeval; crush.
  apply U.eval_beta''; crush.

  apply (evalStepStar (inr (app (protect τ2) vu))).
  apply U.eval₀_ctxeval; crush.
  eapply eval₀_case_inr'; crush.

  refine (extend_ctxevalStar (pinr phole) I hyp).
Qed.

Lemma confine_prod {τ1 τ2 vu1 vu2 vu1' vu2'} :
      Value vu1 → Value vu2 → Value vu1' → Value vu2' →
      ctxevalStar (app (confine τ1) vu1) vu1' →
      ctxevalStar (app (confine τ2) vu2) vu2' →
      ctxevalStar (app (confine (S.tprod τ1 τ2)) (pair vu1 vu2)) (pair vu1' vu2').
Proof.
  intros vv1 vv2 vv1' vv2' hyp1 hyp2.
  (* it would be nice if we could automate the following argument some more... Perhaps improve DecideEval with vi_Terminates ... somehow? *)
  apply (evalStepStar
           (pair (app (confine τ1) (proj₁ (U.pair vu1 vu2)))
                 (app (confine τ2) (proj₂ (U.pair vu1 vu2))))).
  apply U.eval₀_ctxeval; crush.
  eapply U.eval_beta''; crush;
  eauto using OfTypeUtlc_implies_Value.
  apply (evalStepStar
           (pair (app (confine τ1) vu1)
                 (app (confine τ2) (proj₂ (U.pair vu1 vu2))))).

  assert (e₀ : U.proj₁ (U.pair vu1 vu2) -->₀ vu1) by (eauto with eval).
  eapply (ctxeval_from_eval₀ e₀); repeat inferContext; crush; eauto using confine_Value.

  pose (hyp1' := extend_ctxevalStar (ppair₁ phole (app (confine τ2) (proj₂ (U.pair vu1 vu2)))) I hyp1).
  simpl in hyp1'.
  apply (evalStepTrans (pair vu1' (app (confine τ2) (proj₂ (U.pair vu1 vu2)))) hyp1').

  apply (evalStepStar (pair vu1' (app (confine τ2) vu2))).
  assert (e₀ : U.proj₂ (U.pair vu1 vu2) -->₀ vu2) by (eauto with eval).
  eapply (ctxeval_from_eval₀ e₀); repeat inferContext; crush; eauto using confine_Value.

  assert (eC' : ECtx (ppair₂ vu1' phole)) by crush.
  pose (hyp2' := extend_ctxevalStar (ppair₂ vu1' phole) eC' hyp2).
  simpl in hyp2'.
  exact hyp2'.

Qed.

Lemma confine_inl {τ1 τ2 vu vu' } :
      Value vu → Value vu' →
      ctxevalStar (app (confine τ1) vu) vu' →
      ctxevalStar (app (confine (S.tsum τ1 τ2)) (inl vu)) (inl vu').
Proof.
  intros vv vv' hyp.
  apply (evalStepStar (caseof
                   (U.inl vu)
                   (inl (app (confine τ1)[wkm] (var 0)))
                   (inr (app (confine τ2)[wkm] (var 0))))).

  apply U.eval₀_ctxeval; crush.
  apply U.eval_beta''; crush.

  apply (evalStepStar (inl (app (confine τ1) vu))).
  apply U.eval₀_ctxeval; crush.
  eapply eval₀_case_inl'; crush.

  refine (extend_ctxevalStar (pinl phole) I hyp).
Qed.

Lemma confine_inr {τ1 τ2 vu vu' } :
      Value vu → Value vu' →
      ctxevalStar (app (confine τ2) vu) vu' →
      ctxevalStar (app (confine (S.tsum τ1 τ2)) (inr vu)) (inr vu').
Proof.
  intros vv vv' hyp.
  apply (evalStepStar (caseof
                   (U.inr vu)
                   (inl (app (confine τ1)[wkm] (var 0)))
                   (inr (app (confine τ2)[wkm] (var 0))))).

  apply U.eval₀_ctxeval; crush.
  apply U.eval_beta''; crush.

  apply (evalStepStar (inr (app (confine τ2) vu))).
  apply U.eval₀_ctxeval; crush.
  eapply eval₀_case_inr'; crush.

  refine (extend_ctxevalStar (pinr phole) I hyp).
Qed.


Hint Unfold OfType.

Lemma protect_terminates {τ vu} :
  OfTypeUtlc (embed τ) vu →
  ∃ vu', U.Value vu' ∧
         U.ctxevalStar (U.app (protect τ) vu) vu' ∧
         OfTypeUtlc (embed τ) vu'.
Proof.
  revert vu.
  induction τ; intros vu oft_vu; crush;
    pose proof (OfTypeUtlc_implies_Value oft_vu) as vvu.
  - (* ptarr *)
    exists
      (abs
         (app
            (protect τ2)[wkm]
            (app
               vu[wkm]
               (app (confine τ1)[wkm] (var 0))))).
    crush.
    apply evalToStar, U.eval₀_ctxeval; crush.
    apply U.eval_beta''; crush.

  - (* ptunit *)
    exists U.unit; crush.
    apply evalToStar, U.eval₀_ctxeval; crush.
    apply U.eval_beta''; crush.
  - (* ptbool *)
    exists vu; crush.
    apply evalToStar, U.eval₀_ctxeval; crush.
    apply U.eval_beta''; crush.
  - (* ptprod *)
    destruct vu; crush.

    specialize (IHτ1 vu1 H1); destruct IHτ1 as (vu1' & vvu1' & hyp1).
    specialize (IHτ2 vu2 H2); destruct IHτ2 as (vu2' & vvu2' & hyp2).
    exists (U.pair vu1' vu2'); crush.

    refine (protect_prod _ _ _ _ _ _); crush.

  - (* ptsum *)
    destruct vu; crush.
    + (* inl *)
      specialize (IHτ1 vu oft_vu); destruct IHτ1 as (vu' & vvu' & hyp).
      exists (inl vu'); crush.
      refine (protect_inl _ _ _); crush.
    + (* inr *)
      specialize (IHτ2 vu oft_vu); destruct IHτ2 as (vu' & vvu' & hyp).
      exists (inr vu'); crush.
      refine (protect_inr _ _ _); crush.
Qed.


Lemma confine_terminates {τ vu} :
  OfTypeUtlc (embed τ) vu →
  ∃ vu', U.Value vu' ∧
         ctxevalStar (U.app (confine τ) vu) vu' ∧
         OfTypeUtlc (embed τ) vu'.
Proof.
  revert vu.
  induction τ; intros vu oft_vu; crush;
    pose proof (OfTypeUtlc_implies_Value oft_vu) as vvu.
  - exists (abs
         (app
            (confine τ2)[wkm]
            (app
               (vu[wkm])
               (app (protect τ1)[wkm] (var 0))))).
    crush.
    apply evalToStar, U.eval₀_ctxeval; crush.
    apply U.eval_beta''; crush.
  - (* ptunit *)
    exists U.unit; crush.
    apply (evalStepStar (seq unit unit)).
    apply U.eval₀_ctxeval; crush.
    apply U.eval_beta''; crush.
    apply evalToStar, eval₀_ctxeval; crush.
    apply U.eval_seq_next.
  - (* ptbool *)
    exists vu; crush.
    apply (evalStepStar (ite vu true false)).
    apply U.eval₀_ctxeval; crush.
    apply U.eval_beta''; crush.
    apply evalToStar, U.eval₀_ctxeval; crush.
    destruct oft_vu; subst; [apply eval_ite_true|apply eval_ite_false]; crush.
  - (* ptprod *)
    destruct vu; crush.

    specialize (IHτ1 vu1 H1); destruct IHτ1 as (vu1' & vvu1' & hyp1).
    specialize (IHτ2 vu2 H2); destruct IHτ2 as (vu2' & vvu2' & hyp2).
    exists (U.pair vu1' vu2'); crush.
    refine (confine_prod _ _ _ _ _ _); crush.

  - (* ptsum *)
    destruct vu; crush.
    + (* inl *)
      specialize (IHτ1 vu oft_vu); destruct IHτ1 as (vu' & vvu' & hyp).
      exists (inl vu'); crush.
      refine (confine_inl _ _ _); crush.
    + (* inr *)
      specialize (IHτ2 vu oft_vu); destruct IHτ2 as (vu' & vvu' & hyp).
      exists (inr vu'); crush.
      refine (confine_inr _ _ _); crush.
Qed.

Local Hint Resolve valrel_implies_OfType.

(* domi: I should really refactor this to share the common parts with protect_tsum_transp... *)
Lemma confine_tsum_transp {d w τ₁ τ₂ vs vu} :
  valrel d w (embed (S.tsum τ₁ τ₂)) vs vu →
  (∀ w vs vu, valrel d w (embed τ₁) vs vu → 
              ∃ vu', U.Value vu' ∧ ctxevalStar (U.app (confine τ₁) vu) vu' ∧
                     valrel d w (embed τ₁) vs vu') →
  (∀ w vs vu, valrel d w (embed τ₂) vs vu → 
              ∃ vu', U.Value vu' ∧ ctxevalStar (U.app (confine τ₂) vu) vu' ∧
                     valrel d w (embed τ₂) vs vu') →
  ∃ vu', U.Value vu' ∧
         ctxevalStar (U.app (confine (S.tsum τ₁ τ₂)) vu) vu' ∧
         valrel d w (embed (S.tsum τ₁ τ₂)) vs vu'.
Proof.
  cbn; intros vr hyp₁ hyp₂.
  pose proof (valrel_implies_Value vr) as vvu.

  apply valrel_ptsum_inversion in vr.
  destruct vr as [vs' [vu' [[? [? [[ots otu] hyp]]]|[? [? [[ots otu] hyp]]]]]];
  destruct w.
  * destruct (confine_terminates otu) as [vu'' [vvu'' eu]].
    exists (inl vu''); crush.
    eapply confine_inl; crush.
  * assert (fw : w < S w) by omega.
    specialize (hyp w fw).
    destruct (hyp₁ w _ _ hyp) as [vu1' [vvu1' [e1 vr1]]].
    exists (inl vu1'); crush.
    apply confine_inl; crush.
  * destruct (confine_terminates otu) as [vu'' [vvu'' eu]].
    exists (inr vu''); crush.
    eapply confine_inr; crush.
  * assert (fw : w < S w) by omega.
    specialize (hyp w fw).
    destruct (hyp₂ w  _ _ hyp) as [vu2' [vvu2' [e2 vr2]]].
    exists (inr vu2'); crush.
    apply confine_inr; crush.
Qed.


Lemma protect_tprod_transp {d w τ₁ τ₂ vs vu} :
  valrel d w (embed (S.tprod τ₁ τ₂)) vs vu →
  (∀ w vs vu, valrel d w (embed τ₁) vs vu → 
              ∃ vu', U.Value vu' ∧ ctxevalStar (U.app (protect τ₁) vu) vu' ∧
                     valrel d w (embed τ₁) vs vu') →
  (∀ w vs vu, valrel d w (embed τ₂) vs vu → 
              ∃ vu', U.Value vu' ∧ ctxevalStar (U.app (protect τ₂) vu) vu' ∧
                     valrel d w (embed τ₂) vs vu') →
  ∃ vu', U.Value vu' ∧
         ctxevalStar (U.app (protect (S.tprod τ₁ τ₂)) vu) vu' ∧
         valrel d w (embed (S.tprod τ₁ τ₂)) vs vu'.
Proof.
  cbn; intros vr hyp₁ hyp₂.
  pose proof (valrel_implies_Value vr) as vvu.

  apply valrel_ptprod_inversion in vr.
  destruct vr as [vs₁ [vs₂ [vu₁ [vu₂ [? [? [ot₁ [ot₂ hyp]]]]]]]].
  destruct w.
  * (* w = 0 *)
    destruct ot₁ as [ots₁ otu₁].
    destruct ot₂ as [ots₂ otu₂].
    destruct (protect_terminates otu₁) as [vu₁' [vvu₁' eu₁]].
    destruct (protect_terminates otu₂) as [vu₂' [vvu₂' eu₂]].
    exists (pair vu₁' vu₂'); crush.
    eapply protect_prod; crush.

  * assert (fw : w < S w) by omega.
    destruct (hyp w fw) as [vr₁ vr₂].
    destruct (hyp₁ w  _ _ vr₁) as [vu1' [vvu1' [e1 vr1]]].
    destruct (hyp₂ w  _ _ vr₂) as [vu2' [vvu2' [e2 vr2]]].
    exists (pair vu1' vu2'); crush.
    apply protect_prod; crush.
Qed.


(* domi: I should really refactor this to share the common parts with protect_tprod_transp... *)
Lemma confine_tprod_transp {d w τ₁ τ₂ vs vu} :
  valrel d w (embed (S.tprod τ₁ τ₂)) vs vu →
  (∀ w vs vu, valrel d w (embed τ₁) vs vu → 
              ∃ vu', U.Value vu' ∧ ctxevalStar (U.app (confine τ₁) vu) vu' ∧
                     valrel d w (embed τ₁) vs vu') →
  (∀ w vs vu, valrel d w (embed τ₂) vs vu → 
              ∃ vu', U.Value vu' ∧ ctxevalStar (U.app (confine τ₂) vu) vu' ∧
                     valrel d w (embed τ₂) vs vu') →
  ∃ vu', U.Value vu' ∧
         ctxevalStar (U.app (confine (S.tprod τ₁ τ₂)) vu) vu' ∧
         valrel d w (embed (S.tprod τ₁ τ₂)) vs vu'.
Proof.
  cbn; intros vr hyp₁ hyp₂.
  pose proof (valrel_implies_Value vr) as vvu.

  apply valrel_ptprod_inversion in vr.
  destruct vr as [vs₁ [vs₂ [vu₁ [vu₂ [? [? [ot₁ [ot₂ hyp]]]]]]]]; subst.
  destruct w.
  * (* w = 0 *)
    destruct ot₁ as [ots₁ otu₁].
    destruct ot₂ as [ots₂ otu₂].
    destruct (confine_terminates otu₁) as [vu₁' [vvu₁' eu₁]].
    destruct (confine_terminates otu₂) as [vu₂' [vvu₂' eu₂]].

    exists (pair vu₁' vu₂'); crush.
    eapply confine_prod; crush.

  * assert (fw : w < S w) by omega.
    destruct (hyp w fw) as [vr₁ vr₂].
    destruct (hyp₁ w  _ _ vr₁) as [vu1' [vvu1' [e1 vr1]]].
    destruct (hyp₂ w  _ _ vr₂) as [vu2' [vvu2' [e2 vr2]]].

    exists (pair vu1' vu2'); crush.
    apply confine_prod; crush.
Qed.

Lemma protect_tsum_transp {d w τ₁ τ₂ vs vu} :
  valrel d w (embed (S.tsum τ₁ τ₂)) vs vu →
  (∀ w vs vu, valrel d w (embed τ₁) vs vu → 
              ∃ vu', U.Value vu' ∧ ctxevalStar (U.app (protect τ₁) vu) vu' ∧
                     valrel d w (embed τ₁) vs vu') →
  (∀ w vs vu, valrel d w (embed τ₂) vs vu → 
              ∃ vu', U.Value vu' ∧ ctxevalStar (U.app (protect τ₂) vu) vu' ∧
                     valrel d w (embed τ₂) vs vu') →
  ∃ vu', U.Value vu' ∧
         ctxevalStar (U.app (protect (S.tsum τ₁ τ₂)) vu) vu' ∧
         valrel d w (embed (S.tsum τ₁ τ₂)) vs vu'.
Proof.
  cbn; intros vr hyp₁ hyp₂.
  pose proof (valrel_implies_Value vr) as vvu.

  apply valrel_ptsum_inversion in vr.
  destruct vr as [vs' [vu' [[? [? [[ots otu] hyp]]]|[? [? [[ots otu] hyp]]]]]];
  destruct w.
  * destruct (protect_terminates otu) as [vu'' [vvu'' eu]].
    exists (inl vu''); crush; try omega.
    eapply protect_inl; crush.
  * assert (fw : w < S w) by omega.
    specialize (hyp w fw).
    destruct (hyp₁ w _ _ hyp) as [vu1' [vvu1' [e1 vr1]]].
    pose proof (valrel_implies_OfType vr1).
    exists (inl vu1'); crush.
    apply protect_inl; crush.
  * destruct (protect_terminates otu) as [vu'' [vvu'' eu]].
    exists (inr vu''); crush; try omega.
    eapply protect_inr; crush.
  * assert (fw : w < S w) by omega.
    specialize (hyp w fw).
    destruct (hyp₂ w  _ _ hyp) as [vu2' [vvu2' [e2 vr2]]].
    pose proof (valrel_implies_OfType vr2).
    exists (inr vu2'); crush.
    apply protect_inr; crush.
Qed.

Lemma protect_tarr_transp {d w τ₁ τ₂ vs vu} :
  valrel d w (embed (S.tarr τ₁ τ₂)) vs vu →
  (∀ w vs vu, valrel d w (embed τ₁) vs vu → 
              ∃ vu', U.Value vu' ∧ ctxevalStar (U.app (confine τ₁) vu) vu' ∧
                     valrel d w (embed τ₁) vs vu') →
  (∀ w vs vu, valrel d w (embed τ₂) vs vu → 
              ∃ vu', U.Value vu' ∧ ctxevalStar (U.app (protect τ₂) vu) vu' ∧
                     valrel d w (embed τ₂) vs vu') →
  ∃ vu', U.Value vu' ∧
         ctxevalStar (U.app (protect (S.tarr τ₁ τ₂)) vu) vu' ∧
         valrel d w (embed (S.tarr τ₁ τ₂)) vs vu'.
Proof.
  cbn; intros vr hyp₁ hyp₂.
  pose proof (valrel_implies_Value vr) as vvu.

  apply valrel_ptarr_inversion in vr.
  destruct vr as (tsb & tub & ? & ? & wtsb & bodyrel).
  exists (abs
       (app
          (protect τ₂)[wkm]
          (app vu[wkm]
               (app (confine τ₁)[wkm] (var 0))))).
  crush.
  - apply evalToStar, eval₀_ctxeval; crush.
    apply eval_beta''; crush.
  - intros w₂ vs₂ vu₂ fw₂ vr₂; crush.
    destruct (hyp₁ _ _ _ vr₂) as [vu₂' [vvu₂' [eu₂' vr₂']]].
    assert (Value (protect τ₂)) by apply protect_Value.

    enough (termrel d w₂ (embed τ₂) tsb[beta1 vs₂]
                    (app (protect τ₂) (app (abs tub) vu₂')))
      by (refine (termrel_antired_star _ (extend_ctxevalStar' eu₂' _ _ _) _);
          eauto with eval; inferContext; crush).

    enough (termrel d w₂ (embed τ₂) tsb[beta1 vs₂]
                    (app (protect τ₂) tub[beta1 vu₂'])) by
        (refine (termrel_antired_star (rt1n_refl _ _ _) (evalToStar _) _); crush;
         assert (e₀ : app (abs tub) vu₂' -->₀ tub[beta1 vu₂']) by eauto with eval;
         eapply (ctxeval_from_eval₀ e₀); inferContext; crush;
         inferContext; crush).

    specialize (bodyrel w₂ vs₂ vu₂' fw₂ vr₂').
    eapply (termrel_ectx' (Cs := S.phole) bodyrel); inferContext; crush.

    intros w₃ fw₃ vs₃ vu₃ vr₃.
    destruct (hyp₂ _ _ _ vr₃) as [vu₃' [vvu₃' [e₃' vr₃']]].
    enough (termrel d w₃ (embed τ₂) vs₃ vu₃')
      by (refine (termrel_antired_star _ (extend_ctxevalStar' e₃' _ _ _) _);
          eauto with eval; inferContext; crush).
    apply valrel_in_termrel; crush.
Qed.

Lemma confine_tarr_transp {d w τ₁ τ₂ vs vu} :
  valrel d w (embed (S.tarr τ₁ τ₂)) vs vu →
  (∀ w vs vu, valrel d w (embed τ₁) vs vu → 
              ∃ vu', U.Value vu' ∧ ctxevalStar (U.app (protect τ₁) vu) vu' ∧
                     valrel d w (embed τ₁) vs vu') →
  (∀ w vs vu, valrel d w (embed τ₂) vs vu → 
              ∃ vu', U.Value vu' ∧ ctxevalStar (U.app (confine τ₂) vu) vu' ∧
                     valrel d w (embed τ₂) vs vu') →
  ∃ vu', U.Value vu' ∧
         ctxevalStar (U.app (confine (S.tarr τ₁ τ₂)) vu) vu' ∧
         valrel d w (embed (S.tarr τ₁ τ₂)) vs vu'.
Proof.
  cbn; intros vr hyp₁ hyp₂.
  pose proof (valrel_implies_Value vr) as vvu.

  exists (abs
            (app
               (confine τ₂)[wkm]
               (app vu[wkm]
                    (app (protect τ₁)[wkm] (var 0))))).
  apply valrel_ptarr_inversion in vr.
  destruct vr as (tsb & tub & ? & ? & wtsb & bodyrel).
  crush.
  - apply evalToStar, eval₀_ctxeval; crush.
    apply eval_beta''; crush.
  - intros w' vs' vu' fw vr'; crush.
    unfold termrel in bodyrel.

    assert (Value (confine τ₂)) by apply confine_Value.

    destruct (hyp₁ _ _ _ vr') as [vu'' [vvu'' [eu'' vr'']]].
    enough (termrel d w' (embed τ₂) tsb[beta1 vs']
                    (app (confine τ₂) (app (abs tub) vu'')))
      by (refine (termrel_antired_star _ (extend_ctxevalStar' eu'' _ _ _) _);
            eauto with eval; inferContext; crush).

    enough (termrel d w' (embed τ₂) tsb[beta1 vs']
                    (app (confine τ₂) tub[beta1 vu''])) by
        (refine (termrel_antired_star (rt1n_refl _ _ _) (evalToStar _) _); crush;
         assert (e₀ : app (abs tub) vu'' -->₀ tub[beta1 vu'']) by eauto with eval;
         eapply (ctxeval_from_eval₀ e₀); inferContext; crush;
         inferContext; crush).

    specialize (bodyrel w' vs' vu'' fw vr'').
    eapply (termrel_ectx' (Cs := S.phole) bodyrel); inferContext; crush.

    intros.
    destruct (hyp₂ _ _ _ H0) as [vu0' [vvu0' [e0 vr0]]].
    enough (termrel d w'0 (embed τ₂) vs vu0')
      by (refine (termrel_antired_star _ (extend_ctxevalStar' e0 _ _ _) _);
          eauto with eval; inferContext; crush).
    apply valrel_in_termrel; crush.
Qed.


Lemma protect_transp {d w τ vs vu} :
  valrel d w (embed τ) vs vu →
  ∃ vu', U.Value vu' ∧
         ctxevalStar (U.app (protect τ) vu) vu' ∧
         valrel d w (embed τ) vs vu'
  with confine_transp {d w τ vs vu} :
         valrel d w (embed τ) vs vu →
         ∃ vu', U.Value vu' ∧
                (ctxevalStar (U.app (confine τ) vu) vu') ∧
                valrel d w (embed τ) vs vu'.
Proof.
  - destruct τ; intros vr; crush.
    + (* ptarr τ1 τ2 *)
      apply protect_tarr_transp; crush.
    + (* ptunit *)
      pose proof (valrel_implies_Value vr).
      exists vu; crush.
      eapply evalToStar, eval₀_ctxeval, eval_beta''; crush.
    + (* ptbool *)
      pose proof (valrel_implies_Value vr).
      exists vu; crush.
      eapply evalToStar, eval₀_ctxeval, eval_beta''; crush.
    + (* ptprod τ1 τ2 *)
      apply protect_tprod_transp; crush.
    + (* ptsum τ1 τ2 *)
      apply protect_tsum_transp; crush.
  - (* confine *)
    destruct τ; intros vr; crush.
    + (* ptarr τ1 τ2 *)
      apply confine_tarr_transp; crush.
    + (* ptunit *)
      pose (valrel_implies_OfType vr).
      exists vu; crush.
      eapply (evalStepStar (seq unit unit)).
      eapply eval₀_ctxeval, eval_beta''; crush.
      eapply evalToStar, eval₀_ctxeval, eval_seq_next; crush.
    + (* ptbool *)
      pose proof (valrel_implies_Value vr).
      exists vu; crush.
      eapply (evalStepStar (ite vu true false)).
      eapply eval₀_ctxeval, eval_beta''; crush.
      destruct vr as [_ [[? ?]|[? ?]]]; subst;
      eapply evalToStar, eval₀_ctxeval; crush;
      [eapply eval_ite_true|eapply eval_ite_false].
    + (* ptprod τ1 τ2 *)
      apply confine_tprod_transp; crush.
    + (* ptsum τ1 τ2 *)
      apply confine_tsum_transp; crush.
Qed.

Lemma protect_transp' {d w τ vs vu} :
  valrel d w (embed τ) vs vu →
  termrel d w (embed τ) vs (U.app (protect τ) vu).
Proof.
  intros vr.
  destruct (protect_transp vr) as (vu' & vvu' & eu & vr').
  refine (termrel_antired_star _ eu _); 
  eauto using valrel_in_termrel with eval.
Qed.

Lemma protect_transp'' {d w τ ts tu} :
  termrel d w (embed τ) ts tu →
  termrel d w (embed τ) ts (U.app (protect τ) tu).
Proof.
  intros tr.
  assert (U.Value (protect τ)) by apply protect_Value.
  eapply (termrel_ectx' (Cs := S.phole) tr); inferContext; crush.
  intros; apply protect_transp'; crush.
Qed.

(* Lemma confine_transp' {d w τ vs vu} : *)
(*   valrel d w (embed τ) vs vu → *)
(*   termrel d w (embed τ) vs (U.app (confine τ) vu). *)
(* Proof. *)
(*   intros vr. *)
(*   destruct (confine_transp vr) as (vu' & vvu' & eu & vr'). *)
(*   refine (termrel_antired_star _ eu _);  *)
(*   eauto using valrel_in_termrel with eval. *)
(* Qed. *)

Lemma protect_transp_open {d n τ ts tu Γ} :
  ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : embed τ ⟫ →
  ⟪ Γ ⊩ ts ⟦ d , n ⟧ U.app (protect τ) tu : embed τ ⟫.
Proof.
  destruct 1 as [ot lr].
  unfold OpenLRN; crush; intros; crush.
  rewrite -> (wsClosed_invariant protect_closed γu).
  eapply protect_transp''; crush.
Qed.
