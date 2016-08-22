Require Import Common.Common.
Require Import LogRel.PseudoType.
Require Import LogRel.LR.
Require Import Stlc.SpecSyntax.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.LemmasEvaluation.
Require Import Stlc.LemmasTyping.
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
  Include Stlc.LemmasTyping.
End S.
Module U.
  Include Utlc.SpecSyntax.
  Include Utlc.SpecEvaluation.
  Include Utlc.LemmasEvaluation.
End U.

Section Obs.
  Lemma obs_zero {d ts tu} : Obs d 0 ts tu.
  Proof.
    destruct d; simpl; intuition.
  Qed.

  Lemma obs_mono {d W' W ts tu} :
    lev W' ≤ lev W →
    Obs d W ts tu →
    Obs d W' ts tu.
  Proof.
    intros fw obs.
    destruct d; destruct W'; 
    simpl in *; intuition; 
    destruct (S_le fw) as [W'' [eq fw']];
    replace (lev W) with (S W'') in *; simpl in *;
    eauto using S.TerminatingN_lt, U.TerminatingN_lt.
  Qed.
  
  Lemma S_TerminatingN_xor_evaln {t t' n} :
    S.TerminatingN t n → S.evaln t t' (S n) → False.
  Proof.
    induction 1 as [?|? ? ? indHyp];
    inversion 1 as [|? ? ? e es]; subst.
    - refine (S.values_are_normal _ _); eauto.
    - refine (indHyp _ e es).
  Qed.

  Lemma S_ObserveTerminatingN_xor_evaln {t t' n} :
    S.evaln t t' n → False ↔ Observe n (S.TerminatingN t).
  Proof.
    destruct n; simpl in *; intuition; eauto using S_TerminatingN_xor_evaln.
  Qed.

  Lemma S_Observe_TerminatingN_evaln {t t' n } n' :
    S.evaln t t' n → Observe n' (S.TerminatingN t') ↔ Observe (n + n') (S.TerminatingN t).
  Proof.
    destruct n'; 
    try replace (n + 0) with n by omega;
    try replace (n + S n') with (S n + n') by omega;
    simpl in *; eauto using S.TerminatingN_evaln, S_ObserveTerminatingN_xor_evaln.
  Qed.    

  Lemma S_Observe_TerminatingN_lt {t n n'} :
    n ≤ n' → Observe n (S.TerminatingN t) → Observe n' (S.TerminatingN t).
  Proof.
    intros ineq obs.
    destruct n; simpl; intuition.
    destruct (S_le ineq) as [n'' [eq ineq']]; subst; simpl in *.
    eauto using S.TerminatingN_lt.
  Qed.
    

  Lemma U_TerminatingN_xor_evaln {t t' n} :
    U.TerminatingN t n → U.evaln t t' (S n) → False.
  Proof.
    induction 1 as [?|? ? ? indHyp];
    inversion 1 as [|? ? ? e es]; subst.
    - refine (U.values_are_normal _ _); eauto.
    - refine (indHyp _ e es).
  Qed.

  Lemma U_ObserveTerminatingN_xor_evaln {t t' n} :
    U.evaln t t' n → False ↔ Observe n (U.TerminatingN t).
  Proof.
    destruct n; simpl in *; intuition; eauto using U_TerminatingN_xor_evaln.
  Qed.

  Lemma U_Observe_TerminatingN_evaln {t t' n } n' :
    U.evaln t t' n → Observe n' (U.TerminatingN t') ↔ Observe (n + n') (U.TerminatingN t).
  Proof.
    destruct n'; try replace (n + 0) with n by omega; try replace (n + S n') with (S n + n') by omega;
    simpl in *; eauto using U.TerminatingN_evaln, U_ObserveTerminatingN_xor_evaln.
  Qed.    

  Lemma U_Observe_TerminatingN_lt {t n n'} :
    n ≤ n' → Observe n (U.TerminatingN t) → Observe n' (U.TerminatingN t).
  Proof.
    intros ineq obs.
    destruct n; simpl; intuition.
    destruct (S_le ineq) as [n'' [eq ineq']]; subst; simpl; simpl in obs.
    eauto using U.TerminatingN_lt.
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
    destruct d; destruct W; simpl; simpl in obs; intuition.
    - cut (tu'⇓).
      + refine (U.termination_closed_under_antireductionStar _).
        eauto using evaln_to_evalStar.
      + apply obs; clear obs.
        rewrite -> (S_Observe_TerminatingN_evaln (lev W') es).
        assert (obs : Observe (S W) (S.TerminatingN ts)) by (simpl; intuition).
        refine (S_Observe_TerminatingN_lt _ obs).
        unfold lev in *.
        enough (min i j ≤ i) by omega.
        auto using le_min_l.
    - refine (S.termination_closed_under_antireductionStar _ _).
      + refine (S.evaln_to_evalStar es).
      + apply obs; clear obs.
        assert (obs : Observe (S W) (U.TerminatingN tu)) by (simpl; intuition).
        rewrite -> (U_Observe_TerminatingN_evaln (lev W') eu).
        refine (U_Observe_TerminatingN_lt _ obs).
        unfold lev in *.
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
    destruct (valrel_implies_OfType vr) as [[_ ots] _].
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
  
  Lemma termrel_zero {d τ ts tu} : termrel d 0 τ ts tu.
  Proof.
    intros Cs Cu cr eCs eCu. eauto using obs_zero.
  Qed.

  Lemma termrel_antired {ts ts' tu tu' W d τ i j} W' :
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

  Lemma termrel_antired' {ts ts' tu tu' W d τ i j} W' :
    S.evaln ts ts' i →
    U.evaln tu tu' j → 
    tu' ≠ wrong →
    W' ≤ W →
    lev W' + min i j ≥ lev W →
    termrel d W' τ ts' tu' →
    termrel d W τ ts tu.
  Proof.
    intros es eu nw.
    apply termrel_antired; try assumption.
    intros C eC.
    induction eu; eauto using evaln; econstructor; eauto using evaln.
    apply eval_ctx; try assumption.
    intro eq; depind eu; intuition.
    destruct H0 as [C'|C' eq']; destruct C'; simpl in eq; destruct H0; inversion eq; intuition.
  Qed.

  Lemma valrel_in_termrel {ts tu W d τ} :
    valrel d W τ ts tu → termrel d W τ ts tu.
  Proof.
    intros vr Cs Cu eCs eCu contrel.
    apply contrel; auto.
  Qed.
    
  Ltac crush :=
    repeat match goal with 
      | [ H: exists tub', ?tu = U.abs tub' |- U.Value ?tu ] => destruct H as [? ?]; subst
      | [ |- exists ts₁' ts₂' tu₁' tu₂', S.pair ?ts₁ ?ts₂ = LR.S.pair ts₁' ts₂' ∧ U.pair ?tu₁ ?tu₂ = LR.U.pair tu₁' tu₂' ∧ _ ] => exists ts₁; exists ts₂; exists tu₁; exists tu₂
           end;
    cbn;
    intuition.

  Lemma OfTypeUtlc_implies_Value {τ tu} :
    OfTypeUtlc τ tu →
    U.Value tu.
  Proof.
    revert tu; induction τ;
    intros tu ot; unfold OfTypeUtlc in ot; subst; crush; subst; crush.
    - destruct ot as [tu₁ [tu₂ [equ [ot₁ ot₂]]]].
      subst; crush.
    - destruct H as [tu' [eq' ot']].
      subst; crush.
    - destruct H as [tu' [eq' ot']].
      subst; crush.
  Qed. 

  Lemma OfType_implies_Value {τ ts tu} :
    OfType τ ts tu →
    S.Value ts ∧ U.Value tu.
  Proof.
    unfold OfType, OfTypeStlc, OfTypeUtlc.
    intros ot; destruct_conjs;
    eauto using OfTypeUtlc_implies_Value.
  Qed.

  Lemma valrel_implies_Value {d w τ ts tu} :
    valrel d w τ ts tu →
    S.Value ts ∧ U.Value tu.
  Proof.
    intros vr.
    rewrite -> valrel_fixp in vr.
    destruct vr as [ot _].
    exact (OfType_implies_Value ot).
  Qed.

  Lemma extend_envrel {d w Γ γs γu τ ts tu} :
    valrel d w τ ts tu →
    envrel d w Γ γs γu →
    envrel d w (Γ p▻ τ) (γs↑ >=> beta1 ts) (γu↑ >=> beta1 tu).
  Proof.
    intros vr er x τ' xτ'.
    depind xτ'; intuition. 
    replace ((γs↑ >=> beta1 ts) (S i)) with (γs i). 
    replace ((γu↑ >=> beta1 tu) (S i)) with (γu i).
    now refine (er _ _ xτ').
    + cbn; rewrite <- ap_liftSub; 
      rewrite -> liftSub_wkm;
      rewrite -> apply_wkm_beta1_cancel; intuition.
    + cbn; rewrite <- ap_liftSub; 
      rewrite -> liftSub_wkm;
      rewrite -> apply_wkm_beta1_cancel; intuition.
  Qed.

  Lemma termrel_ectx {d w τ₁ τ₂ ts Cs tu Cu} (eCs : S.ECtx Cs) (eCu : U.ECtx Cu) :
    termrel d w τ₁ ts tu →
    (forall w' (fw' : w' ≤ w) vs vu, valrel d w' τ₁ vs vu → termrel d w' τ₂ (S.pctx_app vs Cs) (U.pctx_app vu Cu)) →
    termrel d w τ₂ (S.pctx_app ts Cs) (U.pctx_app tu Cu).
  Proof.
    intros tr cr Cs' Cu' eCs' eCu' cr'.
    rewrite <- S.pctx_cat_app.
    rewrite <- U.pctx_cat_app.
    refine (tr (S.pctx_cat Cs Cs') (U.pctx_cat Cu Cu') _ _ _); eauto using S.ectx_cat, U.ectx_cat.
    intros w' fw' vs vu vr.
    destruct (valrel_implies_Value vr) as [vvs vvu].
    rewrite -> S.pctx_cat_app.
    rewrite -> U.pctx_cat_app.
    refine (cr w' fw' vs vu vr Cs' Cu' eCs' eCu' _).
    refine (contrel_mono fw' cr').
  Qed.


End ClosedLR.

Section OpenLR.

  Lemma compat_var {Γ d n τ i} :
    ⟪ i : τ p∈ Γ ⟫ →
    ⟪ Γ ⊩ S.var i ⟦ d , n ⟧ U.var i : τ ⟫.
  Proof.
    intros iτ. constructor.
    - crushTyping.
      eauto using repEmulCtx_works.
    - intros ? _ ? ? er.
      apply valrel_in_termrel.
      refine (er _ _ iτ).
  Qed.

End OpenLR.
      