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
  Definition inUnitDwn (n : nat) (t : Tm) := app (downgrade n 1) (inUnit n t).
  Definition inBoolDwn (n : nat) (t : Tm) := app (downgrade n 1) (inBool n t).
  Definition inProdDwn (n : nat) (t : Tm) := app (downgrade n 1) (inProd n t).
  Definition inArrDwn (n : nat) (t : Tm) := app (downgrade n 1) (inArr n t).
  Definition inSumDwn (n : nat) (t : Tm) := app (downgrade n 1) (inSum n t).
End Intro.

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
  Definition caseUnitDwn (n : nat) (t : Tm) := caseUnit n (app (downgrade n 1) t).
  Definition caseBoolDwn (n : nat) (t : Tm) := caseBool n (app (downgrade n 1) t).
  Definition caseProdDwn (n : nat) (t : Tm) := caseProd n (app (downgrade n 1) t).
  Definition caseSumDwn (n : nat) (t : Tm) := caseSum n (app (downgrade n 1) t).
  Definition caseArrDwn (n : nat) (t : Tm) := caseArr n (app (downgrade n 1) t).
End Destruct.

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

End DestructProps.