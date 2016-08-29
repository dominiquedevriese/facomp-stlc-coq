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
         U.ctxevalStar (U.app (protect τ) vu) vu' ∧
         OfTypeUtlc (embed τ) vu'.
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
  ∃ vu', U.Value vu' ∧ 
         ctxevalStar (U.app (confine τ) vu) vu' ∧
         OfTypeUtlc (embed τ) vu'.
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
    destruct (valrel_implies_Value vr).
    + (* ptarr τ1 τ2 *)
      exists (abs
                (app
                   (protect τ2)[wkm]
                   (app vu[wkm]
                        (app (confine τ1)[wkm] (var 0))))).
      crush.
      apply evalToStar, eval₀_ctxeval; crush.
      apply eval_beta''; crush.

      destruct (valrel_implies_OfType vr).
      destruct (valrel_ptarr_inversion vr) as [tsb [tub [? [? bodyrel]]]]; crush.
      rewrite -> valrel_fixp; unfold valrel'; crush.

      change (abs tub[wkm↑][(beta1 tu')↑]) with ((abs tub)[wkm][beta1 tu']).
      rewrite -> apply_wkm_beta1_cancel.

      assert (Value (protect τ2)) by apply protect_Value.

      destruct (confine_transp _ _ _ _ _ H) as [vu'' [vvu'' [eu'' vr'']]].
      enough (termrel d w' (embed τ2) tsb[beta1 ts']
                      (app (protect τ2) (app (abs tub) vu'')))
        by (refine (termrel_antired_star _ (extend_ctxevalStar' eu'' _ _ _) _);
              eauto with eval; inferContext; crush).

      enough (termrel d w' (embed τ2) tsb[beta1 ts']
                      (app (protect τ2) tub[beta1 vu''])) by
          (refine (termrel_antired_star (rt1n_refl _ _ _) (evalToStar _) _); crush;
           assert (e₀ : app (abs tub) vu'' -->₀ tub[beta1 vu'']) by eauto with eval;
           eapply (ctxeval_from_eval₀ e₀); inferContext; crush;
           inferContext; crush).

      specialize (bodyrel w' ts' vu'' fw vr'').
      eapply (termrel_ectx' (Cs := S.phole) bodyrel); inferContext; crush.
      
      destruct (protect_transp d _ τ2 _ _ H2) as [vu0' [vvu0' [e0 vr0]]].
      enough (termrel d w'0 (embed τ2) vs vu0')
        by (refine (termrel_antired_star _ (extend_ctxevalStar' e0 _ _ _) _);
            eauto with eval; inferContext; crush).
      apply valrel_in_termrel; crush.

    + (* ptunit *)
      exists vu.
      pose (valrel_implies_OfType vr).
      crush.
      eapply evalToStar, eval₀_ctxeval, eval_beta''; crush.
    + (* ptbool *)
      pose (valrel_implies_Value vr).
      exists vu; crush.
      eapply evalToStar, eval₀_ctxeval, eval_beta''; crush.
    + (* ptprod τ1 τ2 *)
      destruct (valrel_ptprod_inversion vr) as [vs₁ [vs₂ [vu₁ [vu₂ [? [? [ot₁ [ot₂ hyp]]]]]]]]; subst.
      destruct w.
      * (* w = 0 *)
        destruct (OfType_implies_Value ot₁).
        destruct (OfType_implies_Value ot₂).
        destruct ot₁ as [ots₁ otu₁].
        destruct ot₂ as [ots₂ otu₂].
        destruct (protect_terminates otu₁) as [vu₁' [vvu₁' eu₁]].
        destruct (protect_terminates otu₂) as [vu₂' [vvu₂' eu₂]].
        exists (pair vu₁' vu₂'); crush.
        eapply protect_prod; crush.
        rewrite -> valrel_fixp; unfold valrel', prod_rel; crush;
        match goal with [ H : _ < 0 |- _] => inversion H end.
      * assert (fw : w < S w) by omega.
        destruct (hyp w fw) as [vr₁ vr₂].
        destruct (valrel_implies_Value vr₁).
        destruct (valrel_implies_Value vr₂).
        destruct (protect_transp d w τ1 _ _ vr₁) as [vu1' [vvu1' [e1 vr1]]].
        destruct (protect_transp d w τ2 _ _ vr₂) as [vu2' [vvu2' [e2 vr2]]].
        exists (pair vu1' vu2'); crush.

        apply protect_prod; crush. 

        apply valrel_pair'; crush.
    + (* ptsum τ1 τ2 *)
      destruct (valrel_ptsum_inversion vr) as [vs' [vu' [[? [? [[ots otu] hyp]]]|[? [? [[ots otu] hyp]]]]]]; subst;
      rewrite -> valrel_fixp in vr; unfold valrel', sum_rel in vr;
      rewrite -> valrel_fixp; unfold valrel', sum_rel; crush;
      destruct w.
      * pose (OfTypeUtlc_implies_Value otu).
        destruct (protect_terminates otu) as [vu'' [vvu'' eu]].
        exists (inl vu''); crush.
        eapply protect_inl; crush.
        match goal with [ H : _ < 0 |- _] => inversion H end.
      * assert (fw : w < S w) by omega.
        specialize (hyp w fw).
        pose (valrel_implies_Value hyp).
        destruct (protect_transp d w τ1 _ _ hyp) as [vu1' [vvu1' [e1 vr1]]].
        pose (valrel_implies_OfType vr1).
        exists (inl vu1'); crush.
        apply protect_inl; crush.

        refine (valrel_mono _ vr1); omega.
      * pose (OfTypeUtlc_implies_Value otu).
        destruct (protect_terminates otu) as [vu'' [vvu'' eu]].
        exists (inr vu''); crush.
        eapply protect_inr; crush.
        match goal with [ H : _ < 0 |- _] => inversion H end.
      * assert (fw : w < S w) by omega.
        specialize (hyp w fw).
        pose (valrel_implies_Value hyp).
        destruct (protect_transp d w τ2 _ _ hyp) as [vu2' [vvu2' [e2 vr2]]].
        pose (valrel_implies_OfType vr2).
        exists (inr vu2'); crush.
        apply protect_inr; crush.

        refine (valrel_mono _ vr2); omega.
  - destruct τ; intros vr; crush.
    destruct (valrel_implies_Value vr).
    + (* ptarr τ1 τ2 *)
      exists (abs
                (app
                   (confine τ2)[wkm]
                   (app vu[wkm]
                        (app (protect τ1)[wkm] (var 0))))).
      crush.
      apply evalToStar, eval₀_ctxeval; crush.
      apply eval_beta''; crush.

      destruct (valrel_implies_OfType vr).
      rewrite -> valrel_fixp; unfold valrel'; crush.
      rewrite -> valrel_fixp in vr; unfold valrel' in vr.
      destruct vr as [[[vvs tvs] _] bodyrel].
      destruct (can_form_tarr vvs tvs) as [tsb [eq ttsb]]; subst. 
      unfold arr_rel in *; simpl in *. 

      intros vs' vu' vr'; crush.
      change (abs vu[wkm↑][(beta1 vu')↑]) with ((abs vu)[wkm][beta1 vu']).
      rewrite -> apply_wkm_beta1_cancel.

      assert (Value (confine τ2)) by apply confine_Value.

      destruct (protect_transp _ _ _ _ _ vr') as [vu'' [vvu'' [eu'' vr'']]].
      enough (termrel d w' (embed τ2) tsb[beta1 vs']
                      (app (confine τ2) (app (abs vu) vu'')))
        by (refine (termrel_antired_star _ (extend_ctxevalStar' eu'' _ _ _) _);
              eauto with eval; inferContext; crush).

      enough (termrel d w' (embed τ2) tsb[beta1 vs']
                      (app (confine τ2) vu[beta1 vu''])) by
          (refine (termrel_antired_star (rt1n_refl _ _ _) (evalToStar _) _); crush;
           assert (e₀ : app (abs vu) vu'' -->₀ vu[beta1 vu'']) by eauto with eval;
           eapply (ctxeval_from_eval₀ e₀); inferContext; crush;
           inferContext; crush).

      specialize (bodyrel w' fw vs' vu'' vr'').
      eapply (termrel_ectx' (Cs := S.phole) bodyrel); inferContext; crush.
      
      destruct (confine_transp d _ τ2 _ _ H1) as [vu0' [vvu0' [e0 vr0]]].
      enough (termrel d w'0 (embed τ2) vs vu0')
        by (refine (termrel_antired_star _ (extend_ctxevalStar' e0 _ _ _) _);
            eauto with eval; inferContext; crush).
      apply valrel_in_termrel; crush.

    + (* ptunit *)
      exists vu.
      pose (valrel_implies_OfType vr).
      crush.
      eapply (evalStepStar (seq unit unit)).
      eapply eval₀_ctxeval, eval_beta''; crush.
      eapply evalToStar, eval₀_ctxeval, eval_seq_next; crush.
    + (* ptbool *)
      pose (valrel_implies_Value vr).
      exists vu; crush.
      eapply (evalStepStar (ite vu true false)).
      eapply eval₀_ctxeval, eval_beta''; crush.
      destruct vr as [_ [[? ?]|[? ?]]]; subst;
      eapply evalToStar, eval₀_ctxeval; crush;
      [eapply eval_ite_true|eapply eval_ite_false].
    + (* ptprod τ1 τ2 *)
      destruct (valrel_ptprod_inversion vr) as [vs₁ [vs₂ [vu₁ [vu₂ [? [? [ot₁ [ot₂ hyp]]]]]]]]; subst.
      destruct w.
      * (* w = 0 *)
        destruct (OfType_implies_Value ot₁).
        destruct (OfType_implies_Value ot₂).
        destruct ot₁ as [ots₁ otu₁].
        destruct ot₂ as [ots₂ otu₂].

        destruct (confine_terminates otu₁) as [vu₁' [vvu₁' eu₁]].
        destruct (confine_terminates otu₂) as [vu₂' [vvu₂' eu₂]].
        exists (pair vu₁' vu₂'); crush.
        eapply confine_prod; crush.
        
        rewrite -> valrel_fixp; unfold valrel', prod_rel; crush;
        try match goal with [ H : _ < 0 |- _] => inversion H end.
      * assert (fw : w < S w) by omega.
        destruct (hyp w fw) as [vr₁ vr₂].
        destruct (valrel_implies_OfType vr₁).
        destruct (valrel_implies_OfType vr₂).
        destruct (valrel_implies_Value vr₁).
        destruct (valrel_implies_Value vr₂).
        destruct (confine_transp d w τ1 _ _ vr₁) as [vu1' [vvu1' [e1 vr1]]].
        destruct (confine_transp d w τ2 _ _ vr₂) as [vu2' [vvu2' [e2 vr2]]].
        exists (pair vu1' vu2'); crush.

        apply confine_prod; crush. 

        apply valrel_pair'; crush.
    + (* ptsum τ1 τ2 *)
      destruct (valrel_ptsum_inversion vr) as [vs' [vu' [[? [? [[ots otu] hyp]]]|[? [? [[ots otu] hyp]]]]]]; subst;
      rewrite -> valrel_fixp in vr; unfold valrel', sum_rel in vr;
      rewrite -> valrel_fixp; unfold valrel', sum_rel; crush;
      destruct w.
      * pose (OfTypeUtlc_implies_Value otu).
        destruct (confine_terminates otu) as [vu'' [vvu'' eu]].
        exists (inl vu''); crush.
        eapply confine_inl; crush.
        match goal with [ H : _ < 0 |- _] => inversion H end.
      * assert (fw : w < S w) by omega.
        specialize (hyp w fw).
        pose (valrel_implies_Value hyp).
        destruct (confine_transp d w τ1 _ _ hyp) as [vu1' [vvu1' [e1 vr1]]].
        pose (valrel_implies_OfType vr1).
        exists (inl vu1'); crush.
        apply confine_inl; crush.

        refine (valrel_mono _ vr1); omega.
      * pose (OfTypeUtlc_implies_Value otu).
        destruct (confine_terminates otu) as [vu'' [vvu'' eu]].
        exists (inr vu''); crush.
        eapply confine_inr; crush.
        match goal with [ H : _ < 0 |- _] => inversion H end.
      * assert (fw : w < S w) by omega.
        specialize (hyp w fw).
        pose (valrel_implies_Value hyp).
        destruct (confine_transp d w τ2 _ _ hyp) as [vu2' [vvu2' [e2 vr2]]].
        pose (valrel_implies_OfType vr2).
        exists (inr vu2'); crush.
        apply confine_inr; crush.

        refine (valrel_mono _ vr2); omega.
       Show Proof. 
Qed.
        
