Require Import UVal.UVal.
Require Import Utlc.LemmasScoping.
Require Import Utlc.SpecSyntax.
Require Import Stlc.SpecSyntax.
Require Import Stlc.StlcOmega.
Require Import Stlc.Inst.
Require Import Stlc.SpecTyping.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.LemmasTyping.
Require Import Stlc.LemmasEvaluation.
Require Import Stlc.CanForm.
Require Import Db.Lemmas.
Require Import Db.WellScoping.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.
Require Import LogRel.LemmasIntro.
Require Import LogRel.LemmasInversion.
Require Import LogRel.LemmasPseudoType.
Require Import LogRel.PseudoType.
Require Import BackTrans.UpgradeDowngrade.
Require Import Omega.


Section Intro.
  Definition inUnitDwn_pctx (n : nat) := papp₂ (downgrade n 1) (inUnit_pctx n).
  Definition inUnitDwn (n : nat) (t : Tm) := pctx_app t (inUnitDwn_pctx n).
  Definition inBoolDwn_pctx (n : nat) := papp₂ (downgrade n 1) (inBool_pctx n).
  Definition inBoolDwn (n : nat) (t : Tm) := pctx_app t (inBoolDwn_pctx n).
  Definition inProdDwn_pctx (n : nat) := papp₂ (downgrade n 1) (inProd_pctx n).
  Definition inProdDwn (n : nat) (t : Tm) := pctx_app t (inProdDwn_pctx n).
  Definition inArrDwn_pctx (n : nat) := papp₂ (downgrade n 1) (inArr_pctx n).
  Definition inArrDwn (n : nat) (t : Tm) := pctx_app t (inArrDwn_pctx n).
  Definition inSumDwn_pctx (n : nat) := papp₂ (downgrade n 1) (inSum_pctx n).
  Definition inSumDwn (n : nat) (t : Tm) := pctx_app t (inSumDwn_pctx n).
End Intro.

Section IntroTypes.
  Lemma inUnitDwn_pctx_T {n Γ} : ⟪ ⊢ inUnitDwn_pctx n : Γ , tunit → Γ , UVal n ⟫.
  Proof.
    unfold inUnitDwn_pctx.
    eauto using upgrade_T1, downgrade_T1 with typing uval_typing.
  Qed.

  Lemma inUnitDwn_T {n t Γ} : ⟪ Γ ⊢ t : tunit ⟫ → ⟪ Γ ⊢ inUnitDwn n t : UVal n ⟫.
  Proof.
    unfold inUnitDwn.
    eauto using inUnitDwn_pctx_T with typing.
  Qed.


  Lemma inBoolDwn_pctx_T {n Γ} : ⟪ ⊢ inBoolDwn_pctx n : Γ , tbool → Γ , UVal n ⟫.
  Proof.
    unfold inBoolDwn_pctx.
    eauto using upgrade_T1, downgrade_T1 with typing uval_typing.
  Qed.

  Lemma inBoolDwn_T {n t Γ} : ⟪ Γ ⊢ t : tbool ⟫ → ⟪ Γ ⊢ inBoolDwn n t : UVal n ⟫.
  Proof.
    unfold inBoolDwn.
    eauto using inBoolDwn_pctx_T with typing.
  Qed.

  Lemma inProdDwn_pctx_T {n Γ} : ⟪ ⊢ inProdDwn_pctx n : Γ , UVal n × UVal n → Γ , UVal n ⟫.
  Proof.
    unfold inProdDwn_pctx.
    eauto using upgrade_T1, downgrade_T1 with typing uval_typing.
  Qed.

  Lemma inProdDwn_T {n t Γ} : ⟪ Γ ⊢ t : UVal n × UVal n ⟫ → ⟪ Γ ⊢ inProdDwn n t : UVal n ⟫.
  Proof.
    unfold inProdDwn.
    eauto using inProdDwn_pctx_T with typing.
  Qed.

  Lemma inSumDwn_pctx_T {n Γ} : ⟪ ⊢ inSumDwn_pctx n : Γ , UVal n ⊎ UVal n → Γ , UVal n ⟫.
  Proof.
    unfold inSumDwn_pctx.
    eauto using upgrade_T1, downgrade_T1 with typing uval_typing.
  Qed.

  Lemma inSumDwn_T {n t Γ} : ⟪ Γ ⊢ t : UVal n ⊎ UVal n ⟫ → ⟪ Γ ⊢ inSumDwn n t : UVal n ⟫.
  Proof.
    unfold inSumDwn.
    eauto using inSumDwn_pctx_T with typing.
  Qed.

  Lemma inArrDwn_pctx_T {n Γ} : ⟪ ⊢ inArrDwn_pctx n : Γ , (UVal n ⇒ UVal n) → Γ , UVal n ⟫.
  Proof.
    unfold inArrDwn_pctx.
    eauto using upgrade_T1, downgrade_T1 with typing uval_typing.
  Qed.

  Lemma inArrDwn_T {n t Γ} : ⟪ Γ ⊢ t : UVal n ⇒ UVal n ⟫ → ⟪ Γ ⊢ inArrDwn n t : UVal n ⟫.
  Proof.
    unfold inArrDwn.
    eauto using inArrDwn_pctx_T with typing.
  Qed.
End IntroTypes.

Hint Resolve inUnitDwn_T : uval_typing.
Hint Resolve inBoolDwn_T : uval_typing.
Hint Resolve inProdDwn_T : uval_typing.
Hint Resolve inSumDwn_T : uval_typing.
Hint Resolve inArrDwn_T : uval_typing.

Section IntroProps.
  Lemma termrel_inUnitDwn {d w n p vs vu} :
    dir_world_prec n w d p →
    valrel d w ptunit vs vu →
    termrel d w (pEmulDV n p) (inUnitDwn n vs) vu.
  Proof.
   intros dwp vr. 
   unfold inUnitDwn.
   apply downgrade_works'; trivial.
   replace (n + 1) with (S n) by omega.
   apply valrel_inUnit'; trivial.
  Qed.

  Lemma termrel_inBoolDwn {d w n p vs vu} :
    dir_world_prec n w d p →
    valrel d w ptbool vs vu →
    termrel d w (pEmulDV n p) (inBoolDwn n vs) vu.
  Proof.
   intros dwp vr. 
   unfold inBoolDwn.
   apply downgrade_works'; trivial.
   replace (n + 1) with (S n) by omega.
   apply valrel_inBool'; trivial.
  Qed.

  Lemma termrel_inProdDwn {d w n p vs vu} :
    dir_world_prec n w d p →
    valrel d w (ptprod (pEmulDV n p) (pEmulDV n p)) vs vu →
    termrel d w (pEmulDV n p) (inProdDwn n vs) vu.
  Proof.
   intros dwp vr. 
   unfold inProdDwn.
   apply downgrade_works'; trivial.
   replace (n + 1) with (S n) by omega.
   apply valrel_inProd''; trivial.
  Qed.

  Lemma termrel_inSumDwn {d w n p vs vu} :
    dir_world_prec n w d p →
    valrel d w (ptsum (pEmulDV n p) (pEmulDV n p)) vs vu →
    termrel d w (pEmulDV n p) (inSumDwn n vs) vu.
  Proof.
   intros dwp vr. 
   unfold inProdDwn.
   apply downgrade_works'; trivial.
   replace (n + 1) with (S n) by omega.
   apply valrel_inSum''; trivial.
  Qed.

  Lemma termrel_inArrDwn {d w n p vs vu} :
    dir_world_prec n w d p →
    valrel d w (ptarr (pEmulDV n p) (pEmulDV n p)) vs vu →
    termrel d w (pEmulDV n p) (inArrDwn n vs) vu.
  Proof.
   intros dwp vr. 
   unfold inArrDwn.
   apply downgrade_works'; trivial.
   replace (n + 1) with (S n) by omega.
   apply valrel_inArr; trivial.
  Qed.
End IntroProps.

Section Destruct.
  Definition caseUnitUp (n : nat) (t : Tm) := caseUnit n (app (upgrade n 1) t).
  Definition caseBoolUp (n : nat) (t : Tm) := caseBool n (app (upgrade n 1) t).
  Definition caseProdUp (n : nat) (t : Tm) := caseProd n (app (upgrade n 1) t).
  Definition caseSumUp (n : nat) (t : Tm) := caseSum n (app (upgrade n 1) t).
  Definition caseArrUp (n : nat) (t : Tm) := caseArr n (app (upgrade n 1) t).
  Definition caseUnitUp_pctx (n : nat) := papp₂ (S.abs (UVal n) (caseUnit n (app (upgrade n 1) (var 0)))) phole.
  Definition caseBoolUp_pctx (n : nat) := papp₂ (S.abs (UVal n) (caseBool n (app (upgrade n 1) (var 0)))) phole.
  Definition caseProdUp_pctx (n : nat) := papp₂ (S.abs (UVal n) (caseProd n (app (upgrade n 1) (var 0)))) phole.
  Definition caseSumUp_pctx (n : nat) := papp₂ (S.abs (UVal n) (caseSum n (app (upgrade n 1) (var 0)))) phole.
  Definition caseArrUp_pctx (n : nat) := papp₂ (S.abs (UVal n) (caseArr n (app (upgrade n 1) (var 0)))) phole.
End Destruct.

Section DestructTypes.
  Lemma caseUnitUp_T {n t Γ} : ⟪ Γ ⊢ t : UVal n ⟫ → ⟪ Γ ⊢ caseUnitUp n t : tunit ⟫.
  Proof.
    unfold caseUnitUp.
    eauto using upgrade_T1, downgrade_T1 with typing uval_typing.
  Qed.

  Lemma caseUnitUp_pctx_T {n Γ} : ⟪ ⊢ caseUnitUp_pctx n : Γ , UVal n → Γ , tunit ⟫.
  Proof.
    unfold caseUnitUp_pctx.
    eauto using caseUnitUp_T with typing.
  Qed.


  Lemma caseBoolUp_T {n t Γ} : ⟪ Γ ⊢ t : UVal n ⟫ → ⟪ Γ ⊢ caseBoolUp n t : tbool ⟫.
  Proof.
    unfold caseBoolUp.
    eauto using upgrade_T1, downgrade_T1 with typing uval_typing.
  Qed.

  Lemma caseBoolUp_pctx_T {n Γ} : ⟪ ⊢ caseBoolUp_pctx n : Γ , UVal n → Γ , tbool ⟫.
  Proof.
    unfold caseBoolUp_pctx.
    eauto using caseBoolUp_T with typing.
  Qed.

  Lemma caseProdUp_T {n t Γ} : ⟪ Γ ⊢ t : UVal n ⟫ → ⟪ Γ ⊢ caseProdUp n t : UVal n × UVal n ⟫.
  Proof.
    unfold caseProdUp.
    eauto using upgrade_T1, downgrade_T1 with typing uval_typing.
  Qed.

  Lemma caseProdUp_pctx_T {n Γ} : ⟪ ⊢ caseProdUp_pctx n : Γ , UVal n → Γ , UVal n × UVal n ⟫.
  Proof.
    unfold caseProdUp_pctx.
    eauto using caseProdUp_T with typing.
  Qed.

  Lemma caseSumUp_T {n t Γ} : ⟪ Γ ⊢ t : UVal n ⟫ → ⟪ Γ ⊢ caseSumUp n t : UVal n ⊎ UVal n ⟫.
  Proof.
    unfold caseSumUp.
    eauto using upgrade_T1, downgrade_T1 with typing uval_typing.
  Qed.

  Lemma caseSumUp_pctx_T {n Γ} : ⟪ ⊢ caseSumUp_pctx n : Γ , UVal n → Γ , UVal n ⊎ UVal n ⟫.
  Proof.
    unfold caseSumUp_pctx.
    eauto using caseSumUp_T with typing.
  Qed.

  Lemma caseArrUp_T {n t Γ} : ⟪ Γ ⊢ t : UVal n ⟫ → ⟪ Γ ⊢ caseArrUp n t : UVal n ⇒ UVal n ⟫.
  Proof.
    unfold caseArrUp.
    eauto using upgrade_T1, downgrade_T1 with typing uval_typing.
  Qed.

  Lemma caseArrUp_pctx_T {n Γ} : ⟪ ⊢ caseArrUp_pctx n : Γ , UVal n → Γ , UVal n ⇒ UVal n ⟫.
  Proof.
    unfold caseArrUp_pctx.
    eauto using caseArrUp_T with typing.
  Qed.

End DestructTypes.

Hint Resolve caseUnitUp_T : uval_typing.
Hint Resolve caseBoolUp_T : uval_typing.
Hint Resolve caseProdUp_T : uval_typing.
Hint Resolve caseSumUp_T : uval_typing.
Hint Resolve caseArrUp_T : uval_typing.
Hint Resolve caseUnitUp_pctx_T : uval_typing.
Hint Resolve caseBoolUp_pctx_T : uval_typing.
Hint Resolve caseProdUp_pctx_T : uval_typing.
Hint Resolve caseSumUp_pctx_T : uval_typing.
Hint Resolve caseArrUp_pctx_T : uval_typing.

Local Ltac crush :=
  repeat (
      repeat match goal with
                 [ H : _ ∧ _ |- _] => destruct H as [? ?]
               | [ H : valrel _ _ ptunit _ _ |- _] => apply valrel_ptunit_inversion in H
               | [ H : valrel _ _ ptbool _ _ |- _] => apply valrel_ptbool_inversion in H
               | [ H : valrel _ _ (ptprod _ _) _ _ |- _] => apply valrel_ptprod_inversion in H
               | [ H : valrel _ _ (ptsum _ _) _ _ |- _] => apply valrel_ptsum_inversion in H
               | [ H : valrel _ _ (ptarr _ _) _ _ |- _] => apply valrel_ptarr_inversion in H
               | [ |- U.ctxevalStar (U.seq U.unit ?t) _ ] => (eapply (evalStepStar t); [eapply U.eval₀_ctxeval; eauto using U.eval₀|idtac])
               | [ |- clos_refl_trans_1n UTm U.ctxeval U.unit _ ] => eapply rt1n_refl
             end; 
      repeat crushLRMatch;
      crushOfType;
      trivial;
      simpl);
  subst.

Section DestructProps.
  (* pff how to shorten the following? *)
  Lemma invert_valrel_pEmulDV_for_caseUValUnit {d w n p vs vu} :
    valrel d w (pEmulDV (S n) p) vs vu →
    (vs = (inUnit n S.unit) ∧ vu = U.unit ∧
            caseUnit n vs -->* S.unit) ∨
    (p = imprecise ∧ (caseUnit n vs) ⇑) ∨
    (vu ≠ U.unit ∧ (caseUnit n vs) ⇑).
  Proof.
    intros vr.
    apply invert_valrel_pEmulDV in vr.
    destruct vr as [[? ?] | (? & [ [? vr] | other_cases])]; 
      subst; unfold caseUnit.
    - right. left.
      eauto using divergence_closed_under_evalstar, caseUVal_eval_unk, stlcOmega_div.
    - left. destruct (valrel_ptunit_inversion vr); subst.
      change S.unit with ((var 0) [beta1 S.unit]) at 4.
      assert (S.Value S.unit) by crush.
      eauto using caseUVal_eval_unit. 
    - right. right.
      enough (vu ≠ U.unit ∧ caseUnit n vs -->* stlcOmega tunit) as (nunit & eval)
          by eauto using divergence_closed_under_evalstar, stlcOmega_div.
      destruct other_cases as [ [? vr] | [ [? vr] | [[? vr] | [? vr]]]];
      destruct (valrel_implies_Value vr); subst;
      crush;
      repeat match goal with
                 [ |- context [ ((stlcOmega ?tau) [?γ]) ] ]=> rewrite stlcOmega_sub
               | [ H : _ ∧ _ |- _ ]=> destruct H
               | [ H : ∃ _, _ |- _ ]=> destruct H
               | [ H : _ ∨ _ |- _ ]=> destruct H
               | [ |- caseUnit _ _ -->* stlcOmega tunit   ] => 
                (replace (stlcOmega tunit) with ((stlcOmega tunit )[ beta1 x ]) by eapply stlcOmega_sub;
                 eauto using caseUVal_eval_bool, caseUVal_eval_prod, caseUVal_eval_sum, caseUVal_eval_arr)
             end;
      subst; inversion 1.
  Qed.

  Lemma termrel_caseUValUnit {d w n p vs vu}:
    dir_world_prec n w d p →
    valrel d w (pEmulDV (S n) p) vs vu →
    termrel d w ptunit (caseUnit n vs) (U.seq vu U.unit).
  Proof.
    unfold caseUnit.
    intros dwp vr.
    destruct (valrel_implies_Value vr).
    apply invert_valrel_pEmulDV_for_caseUValUnit in vr.
    destruct vr as [(? & ? & ?)|[(? & ?)|(? & ?)]].
    - subst.
      eapply termrel_antired_star.
      + eapply caseUVal_eval_unit; crush.
      + eapply evalToStar.
        eapply U.eval₀_ctxeval.
        eauto with eval.
      + simpl; crush.
    - subst; eapply dwp_imprecise in dwp; subst.
      eapply (termrel_div_lt H2).
    - apply (termrel_div_wrong H2).
      right.
      eauto using evalToStar, U.eval₀_to_eval with eval.
  Qed.

  Lemma invert_valrel_pEmulDV_for_caseUValBool {d w n p vs vu} :
    valrel d w (pEmulDV (S n) p) vs vu →
    (∃ vs', vs = (inBool n vs') ∧ 
                caseBool n vs -->* vs' ∧
                valrel d w ptbool vs' vu) ∨
    (p = imprecise ∧ (caseBool n vs) ⇑) ∨
    (vu ≠ U.true ∧ vu ≠ U.false ∧ (caseBool n vs) ⇑).
  Proof.
    intros vr.
    apply invert_valrel_pEmulDV in vr.
    destruct vr as [[? ?] | (vs' & cases)]; 
      subst; unfold caseBool.
    - right. left.
      eauto using divergence_closed_under_evalstar, caseUVal_eval_unk, stlcOmega_div.
    - assert (cases' : (vs = inBool n vs' ∧ valrel d w ptbool vs' vu)
                       ∨ (vs = inUnit n vs' ∧ valrel d w ptunit vs' vu)
                       ∨ (vs = inProd n vs' ∧ valrel d w (ptprod (pEmulDV n p) (pEmulDV n p)) vs' vu)
                       ∨ (vs = inSum n vs' ∧ valrel d w (ptsum (pEmulDV n p) (pEmulDV n p)) vs' vu)
                       ∨ vs = inArr n vs' ∧ valrel d w (ptarr (pEmulDV n p) (pEmulDV n p)) vs' vu)
        by (destruct cases as [?|[?|?]]; auto).
      destruct cases' as [[? vr] | other_cases].
      + left. destruct (valrel_ptbool_inversion vr); subst;
        exists vs';
        change vs' with ((var 0) [beta1 vs']) at 4;
        assert (S.Value vs') by (destruct H0; subst; crush);
        eauto using caseUVal_eval_bool. 
      + right. right.
        enough (vu ≠ U.true ∧ vu ≠ U.false ∧ caseBool n vs -->* stlcOmega tbool) as (? & ? & ?)
            by eauto using divergence_closed_under_evalstar, stlcOmega_div.
        destruct other_cases as [ [? vr] | [ [? vr] | [[? vr] | [? vr]]]];
          destruct (valrel_implies_Value vr); subst;
          crush;
          repeat match goal with
                     [ |- context [ ((stlcOmega ?tau) [?γ]) ] ]=> rewrite stlcOmega_sub
                   | [ H : _ ∧ _ |- _ ]=> destruct H
                   | [ H : ∃ _, _ |- _ ]=> destruct H
                   | [ H : _ ∨ _ |- _ ]=> destruct H
                   | [ |- caseBool _ (_ _ ?vs') -->* stlcOmega tbool   ] => 
                     (replace (stlcOmega tbool) with ((stlcOmega tbool )[ beta1 vs' ]) by eapply stlcOmega_sub;
                      eauto using caseUVal_eval_unit, caseUVal_eval_bool, caseUVal_eval_prod, caseUVal_eval_sum, caseUVal_eval_arr)
                 end;
          subst; try inversion 1.
  Qed.

  (* Lemma termrel_caseUValBool {d w n p vs vu}: *)
  (*   dir_world_prec n w d p → *)
  (*   valrel d w (pEmulDV (S n) p) vs vu → *)
  (*   termrel d w ptbool (caseBool n vs) (U.ite vu U.true U.false). *)
  (* Proof. *)
  (*   unfold caseBool. *)
  (*   intros dwp vr. *)
  (*   destruct (valrel_implies_Value vr). *)
  (*   apply invert_valrel_pEmulDV_for_caseUValBool in vr. *)
  (*   destruct vr as [(? & ? & ?)|[(? & ?)|(? & ?)]]. *)
  (*   - subst. *)
  (*     eapply termrel_antired_star. *)
  (*     + eapply caseUVal_eval_bool; crush. *)
  (*     + eapply evalToStar. *)
  (*       eapply U.eval₀_ctxeval. *)
  (*       eauto with eval. *)
  (*     + simpl; crush. *)
  (*   - subst; eapply dwp_imprecise in dwp; subst. *)
  (*     eapply (termrel_div_lt H2). *)
  (*   - apply (termrel_div_wrong H2). *)
  (*     right. *)
  (*     eauto using evalToStar, U.eval₀_to_eval with eval. *)
  (* Qed. *)

End DestructProps.