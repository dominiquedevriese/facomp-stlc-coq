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
          repeat crushUtlcEvaluationMatchH2;
          crushOfType;
          repeat match goal with
                     [ |- _ ∧ _ ] => split
                   | [ |- OfType _ _ _ ] => unfold OfType, OfTypeStlc, OfTypeUtlc
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

Lemma protect_Value {τ} : Value (protect τ).
Proof.
  (* quite annoying that I have to crush here... *)
  destruct τ; crush.
Qed.

Lemma confine_Value {τ} : Value (confine τ).
Proof.
  (* quite annoying that I have to crush here... *)
  destruct τ; crush.
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

Lemma protect_terminates {τ vu} :
  OfTypeUtlc (embed τ) vu →
  ∃ vu', U.Value vu' ∧
          U.ctxevalStar (U.app (protect τ) vu) vu'.
Proof.
  revert vu.
  induction τ; crush.
  - exists
      (abs
         (app
            (protect τ2)[wkm]
            (app
               (abs vu[wkm↑])
               (app (confine τ1)[wkm] (var 0))))).
    crush.
    apply evalToStar, U.eval₀_ctxeval; crush.
    apply U.eval_beta''; crush.
  - (* ptunit *)
    exists U.unit.
    crush.
    apply evalToStar, U.eval₀_ctxeval; crush.
    apply U.eval_beta''; crush.
  - (* ptbool *)
    (* why isn't this included in crush through crushOfType *)
    match goal with 
      | [ H: OfTypeUtlc ptbool ?t  |- _ ] => (assert (t = true ∨ t = false) by (destruct t; unfold OfTypeUtlc in H; try inversion H; intuition))
    end.
    assert (Value vu) by (destruct H; subst; crush).
    exists vu.
    crush.
    apply evalToStar, U.eval₀_ctxeval; crush.
    apply U.eval_beta''; crush.
  - (* ptprod *)

    pose (OfTypeUtlc_implies_Value H).
    pose (OfTypeUtlc_implies_Value H0).
    
    specialize (IHτ1 vu1 H); destruct IHτ1 as (vu1' & vvu1' & hyp1).
    specialize (IHτ2 vu2 H0); destruct IHτ2 as (vu2' & vvu2' & hyp2).
    exists (U.pair vu1' vu2'); crush.

    refine (protect_prod _ _ _ _ _ _); crush.

  - (* ptsum, inl *)
    specialize (IHτ1 vu H); destruct IHτ1 as (vu' & vvu' & hyp).
    assert (vvu: Value vu) by eauto using OfTypeUtlc_implies_Value.
    exists (inl vu'); crush.
    refine (protect_inl _ _ _); crush.

  - (* ptsum, inr *)
    specialize (IHτ2 vu H); destruct IHτ2 as (vu' & vvu' & hyp).
    assert (vvu: Value vu) by eauto using OfTypeUtlc_implies_Value.
    exists (inr vu'); crush.
    refine (protect_inr _ _ _); crush.
Qed.


Lemma confine_terminates {τ vu} :
  OfTypeUtlc (embed τ) vu →
  ∃ vu', U.Value vu' ∧ ctxevalStar (U.app (confine τ) vu) vu'.
Proof.
  revert vu.
  induction τ; crush.
  - exists
      (abs
         (app
            (confine τ2)[wkm]
            (app
               (abs vu[wkm↑])
               (app (protect τ1)[wkm] (var 0))))).
    crush.
    apply evalToStar, U.eval₀_ctxeval; crush.
    apply U.eval_beta''; crush.
  - (* ptunit *)
    exists U.unit.
    crush.
    apply (evalStepStar (seq unit unit)). 
    apply U.eval₀_ctxeval; crush.
    apply U.eval_beta''; crush.
    apply evalToStar, eval₀_ctxeval; crush.
    apply U.eval_seq_next.
  - (* ptbool *)
    (* why isn't this included in crush through crushOfType *)
    match goal with 
      | [ H: OfTypeUtlc ptbool ?t  |- _ ] => (assert (t = true ∨ t = false) by (destruct t; unfold OfTypeUtlc in H; try inversion H; intuition))
    end.
    assert (Value vu) by (destruct H; subst; crush).
    exists vu.
    crush.
    apply (evalStepStar (ite vu true false)). 
    apply U.eval₀_ctxeval; crush.
    apply U.eval_beta''; crush.
    apply evalToStar, U.eval₀_ctxeval; crush.
    destruct H0; subst; [apply eval_ite_true|apply eval_ite_false]; crush.
  - (* ptprod *)

    pose (OfTypeUtlc_implies_Value H).
    pose (OfTypeUtlc_implies_Value H0).
    
    specialize (IHτ1 vu1 H); destruct IHτ1 as (vu1' & vvu1' & hyp1).
    specialize (IHτ2 vu2 H0); destruct IHτ2 as (vu2' & vvu2' & hyp2).
    exists (U.pair vu1' vu2'); crush.
    refine (confine_prod _ _ _ _ _ _); crush.


  - (* ptsum, inl *)
    specialize (IHτ1 vu H); destruct IHτ1 as (vu' & vvu' & hyp).
    assert (vvu: Value vu) by eauto using OfTypeUtlc_implies_Value.
    exists (inl vu'); crush.
    refine (confine_inl _ _ _); crush.

  - (* ptsum, inr *)
    specialize (IHτ2 vu H); destruct IHτ2 as (vu' & vvu' & hyp).
    assert (vvu: Value vu) by eauto using OfTypeUtlc_implies_Value.
    exists (inr vu'); crush.
    refine (confine_inr _ _ _); crush.
Qed.




Lemma protect_confine_transp {d w τ vs vu} :
  valrel d w (embed τ) vs vu →
  ∃ vu', U.Value vu' ∧
             (∀ Cu, U.ECtx Cu →
                   (U.pctx_app (U.app (protect τ) vu) Cu) -->* (U.pctx_app vu' Cu)) ∧
             valrel d w (embed τ) vs vu'.
Proof.
  revert vs vu w; induction τ; intros vs vu w vr; crush.
  destruct (valrel_implies_Value vr).
  - (* ptarr τ1 τ2 *)
    exists (abs
              (app
                 (protect τ2)[wkm]
                 (app vu[wkm]
                    (app (confine τ1)[wkm] (var 0))))).
    crush.
    apply evalToStar, eval_ctx₀; crush.
    apply eval_beta''; crush.

    destruct (valrel_implies_OfType vr).
    rewrite -> valrel_fixp; unfold valrel'; crush.
    rewrite -> valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as [[[vvs tvs] _] bodyrel].
    destruct (can_form_tarr vvs tvs) as [tsb [eq ttsb]]; subst. 
    unfold arr_rel in *; simpl in *. 

    intros vs' vu' vr'.
    refine (termrel_antired_star _ _ (bodyrel w' fw vs' vu' vr')); eauto with eval.
    
