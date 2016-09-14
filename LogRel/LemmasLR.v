Require Import Common.Common.
Require Import UVal.UVal.
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

  Lemma S_Observe_Terminating_value {n ts} :
    S.Value ts → Observe (S n) (S.TerminatingN ts).
  Proof.
    intros vts. simpl. eauto using S.values_terminateN.
  Qed.

  Lemma U_Observe_Terminating_value {n tu} :
    U.Value tu → Observe (S n) (U.TerminatingN tu).
  Proof.
    intros vtu. simpl. eauto using U.values_terminateN.
  Qed.

  Lemma obs_value {d n ts tu} :
    S.Value ts → U.Value tu → Obs d n ts tu.
  Proof.
    intros vs vu.
    destruct d; simpl; intros _; 
    eauto using S.values_terminate, U.values_terminate.
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
  
  Lemma S_ObserveTerminatingN_xor_evaln {t t' n} :
    S.evaln t t' n → False ↔ Observe n (S.TerminatingN t).
  Proof.
    destruct n; simpl in *; intuition; eauto using S.TerminatingN_xor_evaln.
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
    

  Lemma U_ObserveTerminatingN_xor_evaln {t t' n} :
    U.evaln t t' n → False ↔ Observe n (U.TerminatingN t).
  Proof.
    destruct n; simpl in *; intuition; eauto using U.TerminatingN_xor_evaln.
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

  Lemma S_ObserveTerminating_Value {w vs} :
    S.Value vs →
    Observe (S w) (S.TerminatingN vs).
  Proof.
    intros vvs; simpl.
    apply S.values_terminateN; trivial.
  Qed.
    
End Obs.

Section ClosedLR.
  Lemma valrel_implies_OfType {d W τ ts tu} :
    valrel d W τ ts tu → OfType τ ts tu.
  Proof.
    rewrite -> valrel_fixp. unfold valrel'. intuition.
  Qed.

  Lemma envrel_triv {d w γs γu} :
    envrel d w pempty γs γu.
  Proof.
    unfold envrel.
    intros i τ i_τ.
    depind i_τ.
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

  Lemma contrel_triv {d w τ} :
    contrel d w τ S.phole U.phole.
  Proof.
    unfold contrel, contrel'; intros w' fw ts tu vr; simpl.
    destruct (valrel_implies_Value vr).
    apply obs_value; trivial.
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

  Lemma termrel_adequacy_lt {w m ts tu τ} :
    termrel dir_lt w τ ts tu →
    S.TerminatingN ts m →
    lev w > m →
    U.Terminating tu.
  Proof.
    intros tr term ineq.
    specialize (tr S.phole U.phole I I contrel_triv).
    simpl in tr. unfold lev in *.
    destruct (le_inv_plus ineq) as [r eq]; subst.
    apply tr.
    apply (S.TerminatingN_lt term); omega.
  Qed.

  Lemma termrel_adequacy_gt {w m tu ts τ} :
    termrel dir_gt w τ ts tu →
    U.TerminatingN tu m →
    lev w > m →
    S.Terminating ts.
  Proof.
    intros tr term ineq.
    specialize (tr S.phole U.phole I I contrel_triv).
    simpl in tr. unfold lev in *.
    destruct (le_inv_plus ineq) as [r eq]; subst.
    apply tr.
    apply (U.TerminatingN_lt term); omega.
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

  Lemma adequacy_lt {n m ts tu τ} :
    ⟪ pempty ⊩ ts ⟦ dir_lt , n ⟧ tu : τ ⟫ →
    S.TerminatingN ts m → 
    n > m →
    U.Terminating tu.
  Proof.
    intros lr term ineq.
    destruct lr as [ty lr].
    set (w := n).
    assert (le_w : lev w ≤ n) by (unfold lev, w; omega).
    assert (er : envrel dir_lt w pempty (idm S.Tm) (idm U.UTm)) by apply envrel_triv.
    pose proof (lr w le_w (idm S.Tm) (idm U.UTm) er) as tr.
    rewrite -> ?ap_id in tr.
    eapply (termrel_adequacy_lt tr term); trivial.
  Qed.

  Lemma adequacy_gt {n m tu ts τ} :
    ⟪ pempty ⊩ ts ⟦ dir_gt , n ⟧ tu : τ ⟫ →
    U.TerminatingN tu m → 
    n > m →
    S.Terminating ts.
  Proof.
    intros lr term ineq.
    destruct lr as [ty lr].
    set (w := n).
    assert (le_w : lev w ≤ n) by (unfold lev, w; omega).
    assert (er : envrel dir_lt w pempty (idm S.Tm) (idm U.UTm)) by apply envrel_triv.
    pose proof (lr w le_w (idm S.Tm) (idm U.UTm) er) as tr.
    rewrite -> ?ap_id in tr.
    eapply (termrel_adequacy_gt tr term); trivial.
  Qed.

End OpenLR.

Ltac crushLRMatch :=
  match goal with
      [ |- _ ∧ _ ] => split
    | [ |- context[ lev ]] => unfold lev
    | [ H : context[ lev ] |- _ ] => unfold lev in *
    | [ |- ⟪ _ ⊩ _ ⟦ _ , _ ⟧ _ : _ ⟫ ] => (unfold OpenLRN; split)
    | [ H : ⟪ _ ⊩ _ ⟦ _ , _ ⟧ _ : _ ⟫ |- _ ] => (unfold OpenLRN in H; destruct_conjs)
    | [ H : valrel ?d _ ?τ ?ts ?tu |- termrel ?d _ ?τ ?ts ?tu ] => apply valrel_in_termrel
    | [ |- termrel _ _ _ (S.abs _ _) (U.abs _) ] => apply valrel_in_termrel
    | [ |- termrel _ _ _ S.unit U.unit ] => apply valrel_in_termrel
    | [ |- termrel _ _ _ S.false U.false ] => apply valrel_in_termrel
    | [ |- termrel _ _ _ S.true U.true ] => apply valrel_in_termrel
    | [ H : valrel ?d ?w ?τ ?ts ?tu |- valrel ?d ?w' ?τ ?ts ?tu ] => (refine (valrel_mono _ H); try omega)
    | [ H : envrel ?d ?w ?τ ?ts ?tu |- envrel ?d ?w' ?τ ?ts ?tu ] => (refine (envrel_mono _ H); try omega)
    | [ |- envrel ?d ?w (?Γ p▻ ?τ) (?γs↑ >=> beta1 ?ts) (?γu↑ >=> beta1 ?tu) ] => refine (extend_envrel _ _)
    | [ H : valrel _ _ ?τ ?ts ?tu |- OfType ?τ ?ts ?tu ] => refine (valrel_implies_OfType H)
    | [ |- valrel _ _ _ _ _] => rewrite -> valrel_fixp in |- *; unfold valrel' in |- *
    | [ |- S.ECtx (S.pctx_cat _ _) ] => apply S.ectx_cat
    | [ |- U.ECtx (U.pctx_cat _ _) ] => apply U.ectx_cat
  end.

Section UVal.
  Lemma valrel_unk {d w n p vu} :
    p = imprecise → Value vu →
    valrel d w (pEmulDV n p) (unkUVal n) vu.
  Proof.
    intros eq vvu; subst.
    repeat crushLRMatch.
    - unfold OfType, OfTypeStlc, OfTypeUtlc; split; simpl;
      eauto using unkUVal_Value, unkUValT.
    - destruct n; [|left]; eauto.
  Qed.

  Lemma valrel_inUnit {d w n p vs vu} :
    vs = S.unit ∧ vu = U.unit →
    valrel d w (pEmulDV (S n) p) (inUnit n vs) vu.
  Proof.
    destruct 1 as [? ?]; subst.
    repeat crushLRMatch.
    - assert (⟪ empty ⊢ S.unit : tunit ⟫) by constructor.
      unfold OfType, OfTypeStlc, OfTypeUtlc; split; simpl;
      eauto using inUnit_Value, inUnitT.
    - right. exists S.unit. left. eauto.
  Qed.

  Lemma valrel_inBool {d w n p vs vu} :
    (vs = S.true ∧ vu = U.true) ∨ (vs = S.false ∧ vu = U.false) →
    valrel d w (pEmulDV (S n) p) (inBool n vs) vu.
  Proof.
    intros eqs;
    repeat crushLRMatch.
    - assert (⟪ empty ⊢ vs : tbool ⟫);
      destruct eqs as [[? ?]|[? ?]]; subst; try constructor;
      unfold OfType, OfTypeStlc, OfTypeUtlc; simpl;
      eauto using inBool_Value, inBoolT.
    - right. exists vs. right. left. eauto.
  Qed.
End UVal.