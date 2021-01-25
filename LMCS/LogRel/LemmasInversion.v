Require Import Common.Common.
Require Import LogRel.PseudoType.
Require Import LogRel.LemmasPseudoType.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.
Require Import LogRel.LemmasIntro.
Require Import Stlc.SpecSyntax.
Require Import Stlc.CanForm.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.LemmasEvaluation.
Require Import Stlc.LemmasTyping.
Require Import Stlc.SpecTyping.
Require Import Utlc.SpecSyntax.
Require Import Utlc.SpecEvaluation.
Require Import Utlc.LemmasEvaluation.
Require Import Utlc.Inst.
Require Import UVal.UVal.

Require Import Omega.
Require Import Min.

Section ValrelInversion.

  Local Ltac crush :=
    repeat
      (cbn in * |-; cbn;
       try assumption;
       crushOfType;
       repeat crushTyping;
       repeat crushStlcSyntaxMatchH;
       repeat crushUtlcSyntaxMatchH;
       repeat crushUtlcScopingMatchH;
       repeat crushDbSyntaxMatchH;
       try subst;
       destruct_conjs;
       repeat match goal with
                  [ |- _ ∧ _ ] => split
              end;
       eauto
      ); 
    try discriminate;
    eauto with eval;
    try omega.

  Lemma valrel_ptunit_inversion {d w vs vu} :
    valrel d w ptunit vs vu →
    vs = S.unit ∧ vu = U.unit.
  Proof.
    rewrite valrel_fixp; unfold valrel'.
    tauto.
  Qed.

  Lemma valrel_ptbool_inversion {d w vs vu} :
    valrel d w ptbool vs vu →
    (vs = S.true ∧ vu = U.true) ∨ (vs = S.false ∧ vu = U.false).
  Proof.
    rewrite valrel_fixp; unfold valrel'.
    crush.
  Qed.

  Lemma valrel_ptprod_inversion {d w τ₁ τ₂ vs vu} :
    valrel d w (ptprod τ₁ τ₂) vs vu →
    exists vs₁ vs₂ vu₁ vu₂,
      (vs = S.pair vs₁ vs₂ ∧ vu = U.pair vu₁ vu₂ ∧
       OfType τ₁ vs₁ vu₁ ∧
       OfType τ₂ vs₂ vu₂ ∧
       ∀ w', w' < w → valrel d w' τ₁ vs₁ vu₁ ∧ valrel d w' τ₂ vs₂ vu₂).
  Proof.
    intros vr.
    destruct (OfType_inversion_ptprod (valrel_implies_OfType vr))
      as (ts1' & tu1' & ts2' & tu2' & Hvs & Hvu & oft1 & oft2).
    exists ts1', ts2', tu1', tu2'; 
    rewrite -> valrel_fixp in vr; 
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
    apply OfType_inversion_ptsum in oft;
    destruct oft as (tsb & tub & Hvs); intuition; crush;
    exists tsb, tub; crush.
  Qed.

  Lemma valrel_ptarr_inversion {d w τ₁ τ₂ vs vu} :
    valrel d w (ptarr τ₁ τ₂) vs vu →
    ∃ tsb tub,
      vs = S.abs (repEmul τ₁) tsb ∧ vu = U.abs tub ∧
      ⟪ empty ▻ repEmul τ₁ ⊢ tsb : repEmul τ₂ ⟫ ∧
      ⟨ 1 ⊢ tub ⟩ ∧
      ∀ w' vs' vu',
        w' < w → valrel d w' τ₁ vs' vu' →
        termrel d w' τ₂ (tsb[beta1 vs']) (tub[beta1 vu']).
  Proof.
    intros vr.
    destruct (valrel_implies_Value vr) as [? ?].
    destruct (OfType_inversion_ptarr (valrel_implies_OfType vr))
      as (tsb & tub & ? & ? & ?).
    exists tsb, tub; crush.
    rewrite -> valrel_fixp in vr.
    unfold valrel' in vr; unfold termrel; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_zero {dir w p vs vu} :
    valrel dir w (pEmulDV 0 p) vs vu →
    OfType (pEmulDV 0 p) vs vu ∧ vs = S.unit ∧ p = imprecise.
  Proof.
    intros vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    tauto.
  Qed.

  Lemma invert_valrel_pEmulDV_unk {dir w n p vu} :
    valrel dir w (pEmulDV (S n) p) (S.inl S.unit) vu →
    p = imprecise.
  Proof.
    intros vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as [_ [[? ?] |[? [(? & ? & ?)| [[? ?] |[[? ?]|[[? ?]|[? ?]]]]]]]];
      crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inUnit' {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p) (inUnit n vs) vu →
    vs = S.unit ∧ vu = U.unit.
  Proof.
    intros vr.
    rewrite valrel_fixp in vr.
    unfold valrel' in vr.
    destruct vr as [_ [[? ?] |[? [(? & ? & ?)| [[? ?] |[[? ?]|[[? ?]|[? ?]]]]]]]];
      crush; inversion H; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inUnit {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p) (inUnit n vs) vu →
    valrel dir w ptunit vs vu.
  Proof.
    intros vr.
    destruct (invert_valrel_pEmulDV_inUnit' vr); subst.
    apply valrel_unit.
  Qed.

  Lemma invert_valrel_pEmulDV_inBool' {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p) (inBool n vs) vu →
    (vs = S.true ∧ vu = U.true) ∨ (vs = S.false ∧ vu = U.false).
  Proof.
    intros vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as [_ [[? ?] |[? [(? & ? & ?)| [[? ?] |[[? ?]|[[? ?]|[? ?]]]]]]]];
      crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inBool {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p) (inBool n vs) vu →
    valrel dir w ptbool vs vu.
  Proof.
    intros vr.
    destruct (invert_valrel_pEmulDV_inBool' vr) as [[? ?]|[? ?]]; subst;
    auto using valrel_true, valrel_false.
  Qed.

  Lemma invert_valrel_pEmulDV_inProd' {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p) (inProd n vs) vu →
    ∃ vs₁ vs₂ vu₁ vu₂, vs = S.pair vs₁ vs₂ ∧ vu = U.pair vu₁ vu₂ ∧
                       (∀ w', w' < w → valrel dir w' (pEmulDV n p) vs₁ vu₁) ∧
                       (∀ w', w' < w → valrel dir w' (pEmulDV n p) vs₂ vu₂).
  Proof.
    intros vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as [[[vv ty] vvu] [[? ?] |[? [(? & ? & ?)| [[? ?] |[[? ?]|[[? ?]|[? ?]]]]]]]]; simpl in *; crush.
    assert (S.Value (inProd n x)) by crush.
    stlcCanForm.
    exists x0, x1, H0, H1; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inProd {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p) (inProd n vs) vu →
    valrel dir w (ptprod (pEmulDV n p) (pEmulDV n p)) vs vu.
  Proof.
    intros vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    destruct (invert_valrel_pEmulDV_inProd' vr) as (? & ? & ? & ? & ? & ? & ? & ?); subst.
    apply valrel_pair''; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inSum' {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p) (inSum n vs) vu →
    ∃ vs' vu', ((vs = S.inl vs' ∧ vu = U.inl vu') ∨ (vs = S.inr vs' ∧ vu = U.inr vu')) ∧
               (∀ w', w' < w → valrel dir w' (pEmulDV n p) vs' vu').
  Proof.
    intros vr.
    rewrite valrel_fixp in vr; unfold valrel' in vr.
    destruct vr as [[[vv ty] vvu] [[? ?] |[? [(? & ? & ?)| [[? ?] |[[? ?]|[[? ?]|[? ?]]]]]]]]; crush.
    assert (S.Value (inSum n x)) by crush.
    unfold sum_rel in H0; simpl in H0.
    stlcCanForm; 
      destruct H1 as [[? ?]|[? ?]]; crush;
      exists x0, H0; crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inSum {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p) (inSum n vs) vu →
    valrel dir w (ptsum (pEmulDV n p) (pEmulDV n p)) vs vu.
  Proof.
    intros vr.
    destruct (valrel_implies_OfType vr) as [[? ?] [? ?]].
    destruct (invert_valrel_pEmulDV_inSum' vr) as (? & ? & [[? ?]|[? ?]] & ?); 
      subst; [apply valrel_inl''| apply valrel_inr'']; 
      crush.
  Qed.

  Lemma invert_valrel_pEmulDV_inArr {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p) (inArr n vs) vu →
    valrel dir w (ptarr (pEmulDV n p) (pEmulDV n p)) vs vu.
  Proof.
    rewrite valrel_fixp; unfold valrel'.
    intros vr.
    destruct vr as [[[? ?] ?] [[? ?] |[? [(? & ? & ?)| [[? ?] |[[? ?]|[[? ?]|[? [? ?]]]]]]]]]; crush;
    stlcCanForm; crush.
  Qed. 

  Lemma invert_valrel_pEmulDV {dir w n p vs vu} :
    valrel dir w (pEmulDV (S n) p) vs vu →
    (vs = unkUVal (S n) ∧ p = imprecise) ∨
    ∃ vs',
      (vs = inUnit n vs' ∧ valrel dir w ptunit vs' vu) ∨
      (vs = inBool n vs' ∧ valrel dir w ptbool vs' vu) ∨
      (vs = inProd n vs' ∧ valrel dir w (ptprod (pEmulDV n p) (pEmulDV n p)) vs' vu) ∨
      (vs = inSum n vs' ∧ valrel dir w (ptsum (pEmulDV n p) (pEmulDV n p)) vs' vu) ∨
      (vs = inArr n vs' ∧ valrel dir w (ptarr (pEmulDV n p) (pEmulDV n p)) vs' vu).
  Proof.
    intros vr.
    destruct (valrel_implies_OfType vr) as [[? ?] _].
    simpl in H0.
    canonUVal.
    - left; crush.
      exact (invert_valrel_pEmulDV_unk vr).
    - right. exists x. left. crush.
      exact (invert_valrel_pEmulDV_inUnit vr).
    - right. exists x. right. left. crush.
      exact (invert_valrel_pEmulDV_inBool vr).
    - right. exists x. right. right. left. crush.
      exact (invert_valrel_pEmulDV_inProd vr).
    - right. exists x. right. right. right. left. crush.
      exact (invert_valrel_pEmulDV_inSum vr).
    - right. exists x. right. right. right. right. crush.
      exact (invert_valrel_pEmulDV_inArr vr).
  Qed.

End ValrelInversion.

Ltac invert_valrel_pEmulDV :=
  match goal with
      [ H : valrel _ _ (pEmulDV (S _) _) _ _ |- _ ] =>
      destruct (invert_valrel_pEmulDV H)
               as [[? ?]|(? & [(?&?)|[(?&?)|[(?&?)|[(?&?)|(?&?)]]]])]
  end.
