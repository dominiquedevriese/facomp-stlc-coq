Require Import Common.Common.
Require Import LogRel.LemmasPseudoType.
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
      [ replace (n + 0) with n by omega
      | replace (n + S n') with (S n + n') by omega ];
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
    destruct n';
      [ replace (n + 0) with n by omega
      | replace (n + S n') with (S n + n') by omega ];
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

  Local Ltac crush :=
    crushOfType;
    repeat
      (cbn in *;
       subst*;
       repeat crushUtlcSyntaxMatchH;
       repeat crushStlcSyntaxMatchH;
       destruct_conjs;
       intuition).

  Lemma valrel_mono {d W τ ts tu W'} :
    W' ≤ W → valrel d W τ ts tu → valrel d W' τ ts tu.
  Proof with subst; intuition.
    rewrite -> ?valrel_fixp.
    revert ts tu W' W.
    induction τ;  unfold valrel';
    intros ts tu W' W fw [ot hyp];
    split; eauto; cbn in *.
    - (* ptarr _ _ *)
      intros W'' fw'.
      apply hyp; try omega.
    - (* ptprod *)
      crush.
    - (* ptsum *)
      crush.
    - (* pEmulDV n p *)
      destruct n; [ assumption | idtac ].
      destruct hyp as [[eqs eqp]|[ts' hyp]];
        [ now left
        | right; exists ts'].
      repeat (destruct hyp as [[eqs hyp]|hyp]; [ left | right]);
        crush; destruct ts'; crush; destruct tu; crush.
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
    U.ctxevaln tu tu' j →
    W' ≤ W →
    lev W' + min i j ≥ lev W →
    termrel d W' τ ts' tu' →
    termrel d W τ ts tu.
  Proof.
    intros es eu fw sge tr.
    unfold termrel, termrel'.
    intros Cs Cu ecs ecu cr.
    refine (obs_antired _ _ fw sge _); eauto using S.evaln_ctx, U.ctxevaln_ctx.
    apply tr; auto. 
    refine (contrel_mono fw cr).
  Qed.

  Lemma termrel_antired_star {ts ts' tu tu' W d τ} :
    clos_refl_trans_1n S.Tm S.eval ts ts' →
    U.ctxevalStar tu tu' →
    termrel d W τ ts' tu' →
    termrel d W τ ts tu.
  Proof.
    intros es eu tr.
    destruct (evalTrans_to_stepRel es) as [i esi].
    destruct (evalTrans_to_stepRel eu) as [j euj].
    refine (termrel_antired W esi euj _ _ tr); omega.
  Qed.

  (* Lemma termrel_antired' {ts ts' tu tu' W d τ i j} W' : *)
  (*   S.evaln ts ts' i → *)
  (*   U.evaln tu tu' j →  *)
  (*   tu' ≠ wrong → *)
  (*   W' ≤ W → *)
  (*   lev W' + min i j ≥ lev W → *)
  (*   termrel d W' τ ts' tu' → *)
  (*   termrel d W τ ts tu. *)
  (* Proof. *)
  (*   intros es eu nw. *)
  (*   apply termrel_antired; try assumption. *)
  (*   induction eu; eauto using evaln; econstructor; eauto using evaln. *)
  (*   apply eval_ctx; try assumption. *)
  (*   intro eq; depind eu; intuition. *)
  (*   destruct H0 as [C'|C' eq']; destruct C'; simpl in eq; destruct H0; inversion eq; intuition. *)
  (* Qed. *)

  Lemma valrel_in_termrel {ts tu W d τ} :
    valrel d W τ ts tu → termrel d W τ ts tu.
  Proof.
    intros vr Cs Cu eCs eCu contrel.
    apply contrel; auto.
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

  Lemma termrel_ectx' {d w τ₁ τ₂ ts Cs tu ts' tu' Cu} :
    termrel d w τ₁ ts tu →
    (forall w' (fw' : w' ≤ w) vs vu, valrel d w' τ₁ vs vu → termrel d w' τ₂ (S.pctx_app vs Cs) (U.pctx_app vu Cu)) →
    ts' = S.pctx_app ts Cs →
    tu' = U.pctx_app tu Cu →
    S.ECtx Cs → U.ECtx Cu →
    termrel d w τ₂ ts' tu'.
  Proof.
    intros; subst; eauto using termrel_ectx.
  Qed.

End ClosedLR.

Section ValrelInversion.
  Local Ltac crush :=
    repeat
      (simpl;
       try assumption;
       crushOfType;
       repeat crushTyping;
       repeat crushStlcSyntaxMatchH;
       repeat crushUtlcSyntaxMatchH;
       repeat crushUtlcScopingMatchH;
       try subst;
       destruct_conjs;
       repeat match goal with 
                  [ |- _ ∧ _ ] => split
              end;
       eauto 
      ); try omega.

  Lemma valrel_ptprod_inversion {d w τ₁ τ₂ vs vu} :
    valrel d w (ptprod τ₁ τ₂) vs vu →
    exists vs₁ vs₂ vu₁ vu₂,
      (vs = S.pair vs₁ vs₂ ∧ vu = U.pair vu₁ vu₂ ∧ 
       OfType τ₁ vs₁ vu₁ ∧
       OfType τ₂ vs₂ vu₂ ∧
       ∀ w', w' < w → valrel d w' τ₁ vs₁ vu₁ ∧ valrel d w' τ₂ vs₂ vu₂).
  Proof.
    intros vr.
    destruct (valrel_implies_Value vr) as [vvs vvu].
    destruct (OfType_inversion_ptprod (valrel_implies_OfType vr))
      as (ts1' & tu1' & ts2' & tu2' & Hvs & Hvu & oft1 & oft2).
    exists ts1', ts2', tu1', tu2'; do 4 (split; auto).
    rewrite -> valrel_fixp in vr; subst vs vu.
    unfold valrel' in vr; crush.
  Qed.

  Lemma valrel_ptsum_inversion {d w τ₁ τ₂ vs vu} :
    valrel d w (ptsum τ₁ τ₂) vs vu →
    exists vs' vu',
      (vs = S.inl vs' ∧ vu = U.inl vu' ∧ 
       OfType τ₁ vs' vu' ∧
       ∀ w', w' < w → valrel d w' τ₁ vs' vu') ∨
      (vs = S.inr vs' ∧ vu = U.inr vu' ∧ 
       OfType τ₂ vs' vu' ∧
       ∀ w', w' < w → valrel d w' τ₂ vs' vu').
  Proof.
    intros vr.
    rewrite -> valrel_fixp in vr; destruct vr as [oft sumrel];
    cbn in *; apply OfType_inversion_ptsum in oft;
    destruct oft as (tsb & tub & Hvs); intuition; crush.
    - exists tsb, tub; crush.
    - exists tsb, tub; crush.
  Qed.

  Lemma valrel_ptarr_inversion {d w τ₁ τ₂ vs vu} :
    valrel d w (ptarr τ₁ τ₂) vs vu →
    ∃ tsb tub,
      vs = S.abs (repEmul τ₁) tsb ∧ vu = U.abs tub ∧
      ⟪ empty ▻ repEmul τ₁ ⊢ tsb : repEmul τ₂ ⟫ ∧
      ∀ w' vs' vu',
        w' < w → valrel d w' τ₁ vs' vu' →
        termrel d w' τ₂ (tsb[beta1 vs']) (tub[beta1 vu']).
  Proof.
    intros vr.
    destruct (valrel_implies_Value vr) as [vvs vvu].
    destruct (OfType_inversion_ptarr (valrel_implies_OfType vr))
      as (tsb & tub & Hvs & Hvu & wtsb).
    exists tsb, tub; do 2 (split; auto).
    rewrite -> valrel_fixp in vr; subst vs vu.
    unfold valrel' in vr; unfold termrel; crush.
  Qed.
End ValrelInversion.
      

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
      