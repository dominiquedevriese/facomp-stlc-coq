Require Import LogRel.PseudoType.
Require Import LogRel.LR.
Require Import Stlc.SpecSyntax.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.LemmasEvaluation.
Require Import Stlc.SpecTyping.
Require Import Utlc.SpecSyntax.
Require Import Utlc.SpecEvaluation.
Require Import Utlc.LemmasEvaluation.
Require Import Utlc.Inst.

Require Import Omega.
Require Import Min.

Module S.
  Include Stlc.SpecSyntax.
  Include Stlc.SpecEvaluation.
  Include Stlc.LemmasEvaluation.
End S.
Module U.
  Include Utlc.SpecSyntax.
  Include Utlc.SpecEvaluation.
  Include Utlc.LemmasEvaluation.
End U.

Section Obs.
  Lemma obs_mono {d W' W ts tu} :
    lev W' ≤ lev W →
    Obs d W ts tu →
    Obs d W' ts tu.
  Proof.
    intros fw obs.
    destruct d; simpl in *; 
    eauto using S.TerminatingN_lt, U.TerminatingN_lt.
  Qed.
  
  Lemma obs_antired {ts ts' tu tu' W' W d i j} :
    S.evaln ts ts' i →
    U.evaln tu tu' j →
    W' ≤ W →
    lev W' + min i j ≥ lev W →
    Obs d W' ts' tu' →
    Obs d W ts tu.
  Proof.
    intros es eu fw sge obs.
    destruct d; unfold Obs in *; intros ttsw.
    - cut (tu'⇓).
      + refine (U.termination_closed_under_antireductionStar _).
        eauto using evaln_to_evalStar.
      + apply obs; clear obs.
        rewrite -> (S.TerminatingN_evaln (lev W') es).
        refine (S.TerminatingN_lt ttsw _).
        enough (min i j ≤ i) by omega.
        auto using le_min_l.
    - refine (S.termination_closed_under_antireductionStar _ _).
      + refine (S.evaln_to_evalStar es).
      + apply obs.
        rewrite -> (U.TerminatingN_evaln (lev W') eu).
        refine (U.TerminatingN_lt ttsw _).
        enough (min i j ≤ j) by omega.
        auto using le_min_r.
  Qed.
End Obs.

Section ClosedLR.
  Lemma valrel_implies_OfType {d W τ ts tu} :
    valrel d W τ ts tu → OfType τ ts tu.
  Proof.
    rewrite -> valrel_fixp. unfold valrel'. intuition.
  Qed.
  
  Lemma envrel_implies_WtSub {d W Γ γs γu} :
    envrel d W Γ γs γu → WtSub (repEmulCtx Γ) empty γs.
  Proof.
    intros er i τ vi_τ.
    destruct (getevar_repEmulCtx vi_τ) as [pτ [vi_pτ ?]].
    assert (vr : valrel d W pτ (γs i) (γu i)) by refine (er _ _ vi_pτ).
    destruct (valrel_implies_OfType vr) as [ots _].
    unfold OfTypeStlc in ots.
    subst. exact ots.
  Qed.
    
  Lemma valrel_mono {d W τ ts tu W'} :
    W' ≤ W → valrel d W τ ts tu → valrel d W' τ ts tu.
  Proof.
    rewrite -> ?valrel_fixp.
    unfold valrel'.
    revert ts tu W' W.
    induction τ;
    intros ts tu W' W fw vr;
    destruct_conjs; split; subst; auto.
    - (* ptarr _ _ *)
      exists H0. exists H1.
      repeat split; auto.
      intros W'' fw' ts' tu' vr'.
      apply H4; try omega; try assumption.
    - (* ptprod *)
      unfold prod_rel in *.
      destruct H0 as [ts₁ [ts₂ [tu₁ [tu₂ [eqs [equ [vr1 vr2]]]]]]].
      exists ts₁. exists ts₂. exists tu₁. exists tu₂.
      split; intuition.
    - (* ptsum *) 
      unfold sum_rel in *.
      destruct H0 as [[ts₁ [tu₁ [eqs [equ vr1]]]] | [ts₂ [tu₂ [eqs [equ vr2]]]]];
      [left; exists ts₁; exists tu₁; intuition | right; exists ts₂; exists tu₂; intuition].
    - (* pEmulDV n p *)
      induction n; try assumption.
      destruct H0 as [[eqs eqp]
                     |[[ts' [eqs [eqs' equ']]]
                      |[[ts' [eqs eqbools]]
                       |[[ts' [eqs [ts₁ [ts₂ [tu₁ [tu₂ [eqs' [equ' hyp]]]]]]]]
                        |[[ts' [eqs sumrel]]
                         |[ts' [eqs [tsb [tub [eqs' [equ' hyp]]]]]]]]]]];
        [ left
        | right;left; exists S.unit
        | right;right;left ; exists ts'
        | right; right; right; left; exists ts'; unfold prod_rel; repeat split; intuition;
          exists ts₁; exists ts₂; exists tu₁; exists tu₂
        | right; right; right; right; left; exists ts'; split; try assumption; unfold sum_rel in *;
          destruct sumrel as [[ts₁ [tu₁ [eqs' [equ' vr]]]]|[ts₂ [tu₂ [eqs' [equ' vr]]]]];
          [left;exists ts₁; exists tu₁ | right; exists ts₂; exists tu₂]
        | right; right; right; right; right; exists ts'; intuition; exists tsb; exists tub];
        subst; intuition.
  Qed.
        
  Lemma envrel_mono {d W Γ γs γu W'} :
    W' ≤ W → envrel d W Γ γs γu → envrel d W' Γ γs γu.
  Proof.
    intros fw er i τ viτ.
    refine (valrel_mono fw _).
    apply er; auto.
  Qed.
    
  Lemma contrel_mono {d W τ Cs Cu W'} :
    W' ≤ W → contrel d W τ Cs Cu → contrel d W' τ Cs Cu.
  Proof.
    intros fw cr. simpl.
    intros W'' fw' vs vu vr.
    apply cr; try omega; auto.
  Qed.
  
  Lemma termrel_antired (ts ts' : S.Tm) (tu tu' : U.UTm) (W' W : World) d τ i j :
    S.evaln ts ts' i →
    (forall C, ECtx C → U.evaln (U.pctx_app tu C) (U.pctx_app tu' C) j) →
    W' ≤ W →
    lev W' + min i j ≥ lev W →
    termrel d W' τ ts' tu' →
    termrel d W τ ts tu.
  Proof.
    intros es eu fw sge tr.
    unfold termrel, termrel'.
    intros Cs Cu ecs ecu cr.
    refine (obs_antired _ _ fw sge _); eauto using S.evaln_ctx.
    apply tr; auto. 
    refine (contrel_mono fw cr).
  Qed.

  Lemma valrel_in_termrel {ts tu W d τ} :
    valrel d W τ ts tu → termrel d W τ ts tu.
  Proof.
    intros vr Cs Cu eCs eCu contrel.
    apply contrel; auto.
  Qed.
    
End ClosedLR.