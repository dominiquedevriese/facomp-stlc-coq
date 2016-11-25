Require Stlc.SpecSyntax.
Require Utlc.SpecSyntax.
Require Import Stlc.SpecTyping.
Require Import Stlc.LemmasTyping.
Require Import Stlc.CanForm.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.LemmasEvaluation.
Require Import Utlc.SpecScoping.
Require Import Utlc.LemmasScoping.
Require Import Utlc.LemmasScoping.
Require Import Utlc.DecideEval.
Require Import UVal.UVal.
Require Import LogRel.PseudoType.
Require Import LogRel.LemmasPseudoType.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.
Require Import Omega.
Require Import Db.Lemmas.
Require Import Utlc.Fix.

Local Ltac crushLRMatch :=
  match goal with
    | [ |- _ ∧ _ ] => split
    | [ H : valrel _ _ ?τ ?ts ?tu   |- OfType ?τ ?ts ?tu ] => refine (valrel_implies_OfType H)
    | [ H : valrel ?d _ ?τ ?ts ?tu  |- termrel ?d _ ?τ ?ts ?tu ] => apply valrel_in_termrel
    | [ H : valrel ?d ?w ?τ ?ts ?tu |- valrel ?d ?w' ?τ ?ts ?tu ] => refine (valrel_mono _ H); omega
    | [ H : valrel _ _ _ ?ts _ |- S.Value ?ts ] => refine (proj1 (valrel_implies_Value H))
    | [ H : valrel _ _ _ _ ?tu |- U.Value ?tu ] => refine (proj2 (valrel_implies_Value H))
    | [ H : OfType _ ?ts _ |- S.Value ?ts ] => refine (proj1 (OfType_implies_Value H))
    | [ H : OfType _ _ ?tu |- U.Value ?tu ] => refine (proj2 (OfType_implies_Value H))
    | [ |- valrel _ _ _ _ _] => rewrite -> valrel_fixp; unfold valrel'
    | [ |- context[ lev ]] => unfold lev
    | [ H : context[ lev ] |- _ ] => unfold lev in *
  end.

Local Ltac crush :=
  repeat
    (try assumption;
     simpl;
     destruct_conjs;
     subst*;
     repeat crushLRMatch;
     crushOfType;
     crushTyping;
     crushUtlcScoping;
     trivial
    ); try omega; eauto.

Section ValueRelation.

  (* Lambda abstraction *)
  Lemma valrel_lambda {d τ' τ ts tu w} :
    OfType (ptarr τ' τ) (S.abs (repEmul τ') ts) (U.abs tu) →
    (∀ w' vs vu, w' < w → valrel d w' τ' vs vu → termrel d w' τ (ts [beta1 vs]) (tu [beta1 vu])) →
    valrel d w (ptarr τ' τ) (S.abs (repEmul τ') ts) (U.abs tu).
  Proof.
    intros ot hyp. crush.
    intros; apply hyp; crush.
  Qed.

  (* Unit *)
  Lemma valrel_unit {d w} :
    valrel d w ptunit S.unit U.unit.
  Proof. crush. Qed.

  (* True *)
  Lemma valrel_true {d w} :
    valrel d w ptbool S.true U.true.
  Proof. crush. Qed.

  (* False *)
  Lemma valrel_false {d w} :
    valrel d w ptbool S.false U.false.
  Proof. crush. Qed.

  (* Pair *)
  Lemma valrel_pair'' {d w τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    OfType τ₁ ts₁ tu₁ →
    OfType τ₂ ts₂ tu₂ →
    (forall w', w' < w → valrel d w' τ₁ ts₁ tu₁) →
    (forall w', w' < w → valrel d w' τ₂ ts₂ tu₂) →
    valrel d w (ptprod τ₁ τ₂) (S.pair ts₁ ts₂) (U.pair tu₁ tu₂).
  Proof. 
    crush.
  Qed.

  Lemma valrel_pair' {d w τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    valrel d w τ₁ ts₁ tu₁ →
    valrel d w τ₂ ts₂ tu₂ →
    valrel d (S w) (ptprod τ₁ τ₂) (S.pair ts₁ ts₂) (U.pair tu₁ tu₂).
  Proof. crush. Qed.

  Lemma valrel_pair {d w τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    valrel d w τ₁ ts₁ tu₁ →
    valrel d w τ₂ ts₂ tu₂ →
    valrel d w (ptprod τ₁ τ₂) (S.pair ts₁ ts₂) (U.pair tu₁ tu₂).
  Proof. crush. Qed.

  Lemma valrel_0_pair {d τ₁ τ₂ vs₁ vu₁ vs₂ vu₂} :
    OfType τ₁ vs₁ vu₁ →
    OfType τ₂ vs₂ vu₂ →
    valrel d 0 (ptprod τ₁ τ₂) (S.pair vs₁ vs₂) (U.pair vu₁ vu₂).
  Proof. crush. Qed.

  (* Inl *)
  Lemma valrel_0_inl {d τ₁ τ₂ vs vu} :
    OfType τ₁ vs vu →
    valrel d 0 (ptsum τ₁ τ₂) (S.inl vs) (U.inl vu).
  Proof. crush. Qed.

  Lemma valrel_inl {d w τ₁ τ₂ vs vu} :
    valrel d w τ₁ vs vu →
    valrel d w (ptsum τ₁ τ₂) (S.inl vs) (U.inl vu).
  Proof. crush. Qed.

  Lemma valrel_inl' {d w τ₁ τ₂ vs vu} :
    valrel d w τ₁ vs vu →
    valrel d (S w) (ptsum τ₁ τ₂) (S.inl vs) (U.inl vu).
  Proof. crush. Qed.

  Lemma valrel_inl'' {d w τ₁ τ₂ vs vu} :
    OfType τ₁ vs vu →
    (∀ w', w' < w → valrel d w' τ₁ vs vu) →
    valrel d w (ptsum τ₁ τ₂) (S.inl vs) (U.inl vu).
  Proof. crush. Qed.

  (* Inr *)
  Lemma valrel_0_inr {d τ₁ τ₂ vs vu} :
    OfType τ₂ vs vu →
    valrel d 0 (ptsum τ₁ τ₂) (S.inr vs) (U.inr vu).
  Proof. crush. Qed.

  Lemma valrel_inr {d w τ₁ τ₂ vs vu} :
    valrel d w τ₂ vs vu →
    valrel d w (ptsum τ₁ τ₂) (S.inr vs) (U.inr vu).
  Proof. crush. Qed.

  Lemma valrel_inr' {d w τ₁ τ₂ vs vu} :
    valrel d w τ₂ vs vu →
    valrel d (S w) (ptsum τ₁ τ₂) (S.inr vs) (U.inr vu).
  Proof. crush. Qed.

  Lemma valrel_inr'' {d w τ₁ τ₂ vs vu} :
    OfType τ₂ vs vu →
    (∀ w', w' < w → valrel d w' τ₂ vs vu) →
    valrel d w (ptsum τ₁ τ₂) (S.inr vs) (U.inr vu).
  Proof. crush. Qed.

  Lemma valrel_unk {d w n p vu} :
    p = imprecise → U.Value vu → ⟨ 0 ⊢ vu ⟩ →
    valrel d w (pEmulDV n p) (unkUVal n) vu.
  Proof.
    intros eq vvu cvu; subst.
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
      eauto using inUnit_Value, inUnitT, wsUTm.
    - right. exists S.unit. left. eauto.
  Qed.

  Lemma valrel_inUnit' {d w n p vs vu} :
    valrel d w ptunit vs vu →
    valrel d w (pEmulDV (S n) p) (inUnit n vs) vu.
  Proof.
    intros vr.
    rewrite valrel_fixp in vr.
    destruct vr as [_ vr].
    simpl in vr.
    apply valrel_inUnit.
    crush.
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
      eauto using inBool_Value, inBoolT, wsUTm.
    - right. exists vs. right. left. eauto.
  Qed.

  Lemma valrel_inBool' {d w n p vs vu} :
    valrel d w ptbool vs vu →
    valrel d w (pEmulDV (S n) p) (inBool n vs) vu.
  Proof.
    intros vr.
    rewrite valrel_fixp in vr.
    destruct vr as [_ vr].
    simpl in vr.
    apply valrel_inBool.
    crush.
  Qed.
    
  Lemma valrel_inProd {d w n p vs₁ vs₂ vu₁ vu₂} :
    OfType (pEmulDV n p) vs₁ vu₁ →
    OfType (pEmulDV n p) vs₂ vu₂ →
    (forall w', w' < w → valrel d w' (pEmulDV n p) vs₁ vu₁) →
    (forall w', w' < w → valrel d w' (pEmulDV n p) vs₂ vu₂) →
    valrel d w (pEmulDV (S n) p) (inProd n (S.pair vs₁ vs₂)) (U.pair vu₁ vu₂).
  Proof.
    intros ot₁ ot₂ vr₁ vr₂.
    destruct (OfType_implies_Value ot₁).
    destruct (OfType_implies_Value ot₂).
    repeat crushLRMatch.
    - unfold OfType, OfTypeStlc, OfTypeUtlc in *; crush. 
    - right. exists (S.pair vs₁ vs₂). right. right. left.
      crush.
  Qed.

  Lemma valrel_inProd' {d w n p vs₁ vs₂ vu₁ vu₂} :
    (valrel d w (pEmulDV n p) vs₁ vu₁) →
    (valrel d w (pEmulDV n p) vs₂ vu₂) →
    valrel d (S w) (pEmulDV (S n) p) (inProd n (S.pair vs₁ vs₂)) (U.pair vu₁ vu₂).
  Proof.
    intros vr₁ vr₂.
    eapply valrel_inProd; crush.
 Qed.

  Lemma valrel_inProd'' {d w n p vs vu} :
    valrel d w (ptprod (pEmulDV n p) (pEmulDV n p)) vs vu →
    valrel d w (pEmulDV (S n) p) (inProd n vs) vu.
  Proof.
    intros vr.
    rewrite valrel_fixp in vr.
    destruct vr as [val vr].
    simpl in vr; unfold prod_rel in vr.
    destruct vs; try contradiction.
    destruct vu; try contradiction.
    destruct val as ((? & ?) & (? & ? & ?)).
    destruct vr as (? & ?).
    simpl in H0.
    stlcCanForm.
    destruct H as (? & ?).
    inversion H6; subst.
    eapply valrel_inProd; crushOfType; crushUtlcScoping; auto.
  Qed.

  Lemma valrel_inSum {d w n p vs vs' vu vu'} :
    OfType (pEmulDV n p) vs vu →
    (forall w', w' < w → valrel d w' (pEmulDV n p) vs vu) →
    (vs' = S.inl vs ∧ vu' = U.inl vu) ∨ (vs' = S.inr vs ∧ vu' = U.inr vu) →
    valrel d w (pEmulDV (S n) p) (inSum n vs') vu'.
  Proof.
    intros ot vr eqs. 
    destruct (OfType_implies_Value ot).
    assert (S.Value vs') by (destruct eqs as [[? ?]|[? ?]]; crush).
    assert (U.Value vu') by (destruct eqs as [[? ?]|[? ?]]; crush).
    assert ⟪ empty ⊢ vs' : UVal n ⊎ UVal n ⟫
      by (destruct eqs as [[? ?]|[? ?]]; crush).
    assert ⟨ 0 ⊢ vu' ⟩
           by (destruct eqs as [[? ?]|[? ?]]; crush).
    crush.
    right. exists vs'. right. right. right. left.
    destruct eqs as [[? ?]|[? ?]]; crush.
  Qed.

  Lemma valrel_inSum' {d w n p vs vs' vu vu'} :
    (valrel d w (pEmulDV n p) vs vu) →
    (vs' = S.inl vs ∧ vu' = U.inl vu) ∨ (vs' = S.inr vs ∧ vu' = U.inr vu) →
    valrel d (S w) (pEmulDV (S n) p) (inSum n vs') vu'.
  Proof.
    intros vr₁ eqs.
    refine (valrel_inSum _ _ eqs); crush.
  Qed.

  Lemma valrel_inSum'' {d w n p vs vu} :
    valrel d w (ptsum (pEmulDV n p) (pEmulDV n p)) vs vu →
    valrel d w (pEmulDV (S n) p) (inSum n vs) vu.
  Proof.
   intros vr. 
   rewrite valrel_fixp in vr.
   destruct vr as [val vr].
   destruct val as ((? & ?) & ? & ?).
   simpl in H0.
   stlcCanForm;
     simpl in vr; unfold sum_rel in vr;
     destruct vu; try contradiction;
     eapply valrel_inSum; auto;
     crush;
     eauto using inSum_T with typing.
  Qed.

  Lemma valrel_inArr {d w n p vs vu} :
    valrel d w (ptarr (pEmulDV n p) (pEmulDV n p)) vs vu →
    valrel d w (pEmulDV (S n) p) (inArr n vs) vu.
  Proof.
    intros vr.
    crush.
    - destruct (valrel_implies_OfType vr) as [[_ ?] _].
      eauto using inArr_T with typing.
    - destruct (valrel_implies_OfType vr) as (_ & ? & _).
      auto.
    - right. exists vs. do 4 right.
      rewrite valrel_fixp in vr; destruct vr as [[_ ?] vrarr].
      crush.
  Qed.
End ValueRelation.

Ltac valrelIntro :=
  match goal with
    | |- valrel _ _ (ptarr ?τ _) (S.abs (repEmul ?τ) _) (U.abs _) => eapply valrel_lambda
    | |- valrel _ _ ptunit S.unit U.unit => apply valrel_unit
    | |- valrel _ _ ptbool S.true U.true => apply valrel_true
    | |- valrel _ _ ptbool S.false U.false => apply valrel_false
    | |- valrel _ ?w (ptprod _ _) (S.pair _ _) (U.pair _ _) =>
      match w with
        | O   => apply valrel_0_pair
        | S _ => apply valrel_pair'
        | _   => apply valrel_pair
      end
    | |- valrel _ ?w (ptsum _ _) (S.inl _) (U.inl _) =>
      match w with
        | O   => apply valrel_0_inl
        | S _ => apply valrel_inl'
        | _   => apply valrel_inl
      end
    | |- valrel _ ?w (ptsum _ _) (S.inr _) (U.inr _) =>
      match w with
        | O   => apply valrel_0_inr
        | S _ => apply valrel_inr'
        | _   => apply valrel_inr
      end
    | [ H : valrel ?d _ ?τ ?ts ?tu |- valrel ?d _ ?τ ?ts ?tu ] =>
      refine (valrel_mono _ H); try omega
  end.

Section TermRelation.

  (* Eval context *)
  Lemma termrel_ectx {d w τ₁ τ₂ ts Cs tu Cu} (eCs : S.ECtx Cs) (eCu : U.ECtx Cu) :
    termrel d w τ₁ ts tu →
    (∀ w' (fw' : w' ≤ w) vs vu, valrel d w' τ₁ vs vu → termrel d w' τ₂ (S.pctx_app vs Cs) (U.pctx_app vu Cu)) →
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
    (∀ w' (fw' : w' ≤ w) vs vu, valrel d w' τ₁ vs vu → termrel d w' τ₂ (S.pctx_app vs Cs) (U.pctx_app vu Cu)) →
    ts' = S.pctx_app ts Cs →
    tu' = U.pctx_app tu Cu →
    S.ECtx Cs → U.ECtx Cu →
    termrel d w τ₂ ts' tu'.
  Proof.
    intros; subst; eauto using termrel_ectx.
  Qed.

  (* Application *)
  Lemma valrel_app {d w τ₁ τ₂ vs₁ vs₂ vu₁ vu₂} :
    valrel d w (ptarr τ₁ τ₂) vs₁ vu₁ →
    valrel d w τ₁ vs₂ vu₂ →
    termrel d w τ₂ (S.app vs₁ vs₂) (U.app vu₁ vu₂).
  Proof.
    (* destruct assumptions *)
    intros vr₁ vr₂.
    rewrite -> valrel_fixp in vr₁.
    destruct vr₁ as [ot hyp]; subst; cbn in hyp.
    apply OfType_inversion_ptarr in ot.
    destruct ot as (tsb & tub & eqs & equ & _); subst.
    destruct (valrel_implies_Value vr₂) as [vvs₂ vvu₂].

    (* beta-reduce *)
    assert (es : S.eval (S.app (S.abs (repEmul τ₁) tsb) vs₂) (tsb [beta1 vs₂])) by
        (refine (S.eval_ctx₀ S.phole _ I); refine (S.eval_beta vvs₂)).
    assert (es1 : S.evaln (S.app (S.abs (repEmul τ₁) tsb) vs₂) (tsb [beta1 vs₂]) 1) by
        (unfold S.evaln; eauto with eval; omega).
    assert (eu : U.ctxeval (U.app (U.abs tub) vu₂) (tub [beta1 vu₂])) by
        (refine (U.mkCtxEval U.phole _ _ I _); refine (U.eval_beta vvu₂)).
    assert (eu1 : U.ctxevaln (U.app (U.abs tub) vu₂) (tub [beta1 vu₂]) 1) by
        (unfold U.ctxevaln; eauto with eval).
    destruct w; try apply termrel_zero.
    refine (termrel_antired w es1 eu1 _ _ _); unfold lev in *; simpl; try omega.

    (* use assumption for function body *)
    eapply hyp; try omega; eauto using valrel_mono.
  Qed.

  Lemma termrel_app {d w τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    termrel d w (ptarr τ₁ τ₂) ts₁ tu₁ →
    (∀ w', w' ≤ w → termrel d w' τ₁ ts₂ tu₂) →
    termrel d w τ₂ (S.app ts₁ ts₂) (U.app tu₁ tu₂).
  Proof.
    intros tr₁ tr₂.
    change (S.app _ _) with (S.pctx_app ts₁ (S.papp₁ S.phole ts₂)).
    change (U.app _ _) with (U.pctx_app tu₁ (U.papp₁ U.phole tu₂)).
    refine (termrel_ectx _ _ tr₁ _); crush.
    destruct (valrel_implies_Value H) as [vvs vvu].
    change (S.app _ _) with (S.pctx_app ts₂ (S.papp₂ vs S.phole)).
    change (U.app _ _) with (U.pctx_app tu₂ (U.papp₂ vu U.phole)).
    refine (termrel_ectx _ _ (tr₂ w' fw')  _); crush.
    refine (valrel_app _ H0); crush.
  Qed.

  Lemma termrel_ite {d w τ ts₁ ts₂ ts₃ tu₁ tu₂ tu₃} :
    termrel d w ptbool ts₁ tu₁ →
    (∀ w', w' ≤ w → termrel d w' τ ts₂ tu₂) →
    (∀ w', w' ≤ w → termrel d w' τ ts₃ tu₃) →
    termrel d w τ (S.ite ts₁ ts₂ ts₃) (U.ite tu₁ tu₂ tu₃).
  Proof.
    intros tr₁ tr₂ tr₃.

    (* first evaluate ts₁ and tu₁ *)
    change (S.ite _ _ _) with (S.pctx_app ts₁ (S.pite₁ S.phole ts₂ ts₃)).
    change (U.ite _ _ _) with (U.pctx_app tu₁ (U.pite₁ U.phole tu₂ tu₃)).
    refine (termrel_ectx _ _ tr₁ _); crush.

    (* then evaluate the if-statement *)
    rewrite -> valrel_fixp in H.
    destruct H as [ot [[? ?]|[? ?]]]; subst; clear ot.
    - assert (S.eval (S.ite S.true ts₂ ts₃) ts₂) by
          (apply (S.eval_ctx₀ S.phole); try refine (S.eval_ite_true _ _); simpl; intuition).
      assert (esn : S.evaln (S.ite S.true ts₂ ts₃) ts₂ 1) by (unfold S.evaln; eauto with eval).
      assert (U.ctxeval (U.ite U.true tu₂ tu₃) tu₂) by
          (apply (U.mkCtxEval U.phole); try refine (U.eval_ite_true _ _); simpl; intuition).
      assert (eun : U.ctxevaln (U.ite U.true tu₂ tu₃) tu₂ 1) by (unfold U.ctxevaln; eauto with eval).
      refine (termrel_antired w' esn eun _ _ _); crush.
    - assert (S.eval (S.ite S.false ts₂ ts₃) ts₃) by
          (apply (S.eval_ctx₀ S.phole); try refine (S.eval_ite_false _ _); simpl; intuition).
      assert (esn : S.evaln (S.ite S.false ts₂ ts₃) ts₃ 1) by (unfold S.evaln; eauto with eval).
      assert (U.ctxeval (U.ite U.false tu₂ tu₃) tu₃) by
          (apply (U.mkCtxEval U.phole); try refine (U.eval_ite_false _ _); simpl; intuition).
      assert (eun : U.ctxevaln (U.ite U.false tu₂ tu₃) tu₃ 1) by (unfold U.ctxevaln; eauto with eval).
      refine (termrel_antired w' esn eun _ _ _); crush.
  Qed.

  (* Pair *)
  Lemma termrel_pair {d w τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    termrel d w τ₁ ts₁ tu₁ →
    (∀ w', w' ≤ w → termrel d w' τ₂ ts₂ tu₂) →
    termrel d w (ptprod τ₁ τ₂) (S.pair ts₁ ts₂) (U.pair tu₁ tu₂).
  Proof.
    intros tr₁ tr₂.
    change (S.pair _ _) with (S.pctx_app ts₁ (S.ppair₁ S.phole ts₂)).
    change (U.pair _ _) with (U.pctx_app tu₁ (U.ppair₁ U.phole tu₂)).
    refine (termrel_ectx _ _ tr₁ _); crush.
    destruct (valrel_implies_Value H) as [vvs₂ vvu₂].
    change (S.pair _ _) with (S.pctx_app ts₂ (S.ppair₂ vs S.phole)).
    change (U.pair _ _) with (U.pctx_app tu₂ (U.ppair₂ vu U.phole)).
    refine (termrel_ectx _ _ (tr₂ w' fw')  _); crush.
    eauto using valrel_in_termrel, valrel_mono, valrel_pair.
  Qed.

  (* Proj₁ *)
  Lemma termrel_proj₁ {d w τ₁ τ₂ ts tu} :
    termrel d w (ptprod τ₁ τ₂) ts tu →
    termrel d w τ₁ (S.proj₁ ts) (U.proj₁ tu).
  Proof.
    intros tr.

    (* first evaluate ts and tu *)
    change (S.proj₁ _) with (S.pctx_app ts (S.pproj₁ S.phole)).
    change (U.proj₁ _) with (U.pctx_app tu (U.pproj₁ U.phole)).
    refine (termrel_ectx _ _ tr _); crush.

    (* then evaluate the projection *)
    rewrite -> valrel_fixp in H.
    destruct H as [ot hyp]; subst; cbn in hyp.
    apply OfType_inversion_ptprod in ot.
    destruct ot as (vs₁ & vu₁ & vs₂ & vu₂ & ? & ? & ot₁ & ot₂); subst.
    destruct (OfType_implies_Value ot₁) as [vvs₁ vvs₂].
    destruct (OfType_implies_Value ot₂) as [vvu₁ vvu₂].
    destruct hyp as [vr₁ vr₂].

    assert (S.eval (S.proj₁ (S.pair vs₁ vs₂)) vs₁) by
        (apply (S.eval_ctx₀ S.phole); try refine (S.eval_proj₁ _ _); simpl; intuition).
    assert (esn : S.evaln (S.proj₁ (S.pair vs₁ vs₂)) vs₁ 1) by (unfold S.evaln; eauto with eval).
    assert (U.ctxeval (U.proj₁ (U.pair vu₁ vu₂)) vu₁) by
        (apply (U.mkCtxEval U.phole); try refine (U.eval_proj₁ _); simpl; intuition).
    assert (eun : U.ctxevaln (U.proj₁ (U.pair vu₁ vu₂)) vu₁ 1) by (unfold U.ctxevaln; eauto with eval).
    destruct w'; try apply termrel_zero.
    refine (termrel_antired w' esn eun _ _ _); crush.

    (* then conclude *)
    apply valrel_in_termrel.
    apply vr₁; intuition; omega.
  Qed.

  (* Proj₂ *)
  Lemma termrel_proj₂ {d w τ₁ τ₂ ts tu} :
    termrel d w (ptprod τ₁ τ₂) ts tu →
    termrel d w τ₂ (S.proj₂ ts) (U.proj₂ tu).
  Proof.
    intros tr.

    (* first reduce ts and tu *)
    change (S.proj₂ _) with (S.pctx_app ts (S.pproj₂ S.phole)).
    change (U.proj₂ _) with (U.pctx_app tu (U.pproj₂ U.phole)).
    refine (termrel_ectx _ _ tr _); crush.

    (* then evaluate the projection *)
    rewrite -> valrel_fixp in H.
    destruct H as [ot hyp]; subst; cbn in hyp.
    apply OfType_inversion_ptprod in ot.
    destruct ot as (vs₁ & vu₁ & vs₂ & vu₂ & ? & ? & ot₁ & ot₂); subst.
    destruct (OfType_implies_Value ot₁) as [vvs₁ vvs₂].
    destruct (OfType_implies_Value ot₂) as [vvu₁ vvu₂].
    destruct hyp as [vr₁ vr₂].

    assert (S.eval (S.proj₂ (S.pair vs₁ vs₂)) vs₂) by
        (apply (S.eval_ctx₀ S.phole); try refine (S.eval_proj₂ _ _); simpl; intuition).
    assert (esn : S.evaln (S.proj₂ (S.pair vs₁ vs₂)) vs₂ 1) by (unfold S.evaln; eauto with eval).
    assert (U.ctxeval (U.proj₂ (U.pair vu₁ vu₂)) vu₂) by
        (apply (U.mkCtxEval U.phole); try refine (U.eval_proj₂ _); simpl; intuition).
    assert (eun : U.ctxevaln (U.proj₂ (U.pair vu₁ vu₂)) vu₂ 1)
      by (unfold U.ctxevaln; eauto with eval).
    destruct w'; try apply termrel_zero.
    refine (termrel_antired w' esn eun _ _ _); crush.

    apply valrel_in_termrel.
    apply vr₂; crush.
  Qed.

  (* Inl *)
  Lemma termrel_inl {d w τ₁ τ₂ ts tu} :
    termrel d w τ₁ ts tu →
    termrel d w (ptsum τ₁ τ₂) (S.inl ts) (U.inl tu).
  Proof.
    intros tr.
    change (S.inl ts) with (S.pctx_app ts (S.pinl S.phole)).
    change (U.inl tu) with (U.pctx_app tu (U.pinl U.phole)).
    refine (termrel_ectx _ _ tr _); crush.
    apply valrel_in_termrel; crush.
  Qed.

  (* Inr *)
  Lemma termrel_inr {d w τ₁ τ₂ ts tu} :
    termrel d w τ₂ ts tu →
    termrel d w (ptsum τ₁ τ₂) (S.inr ts) (U.inr tu).
  Proof.
    intros tr.
    change (S.inr ts) with (S.pctx_app ts (S.pinr S.phole)).
    change (U.inr tu) with (U.pctx_app tu (U.pinr U.phole)).
    refine (termrel_ectx _ _ tr _); crush.
    apply valrel_in_termrel; crush.
  Qed.

  (* Caseof *)
  Lemma termrel_caseof {d w τ τ₁ τ₂ ts₁ ts₂ ts₃ tu₁ tu₂ tu₃} :
    termrel d w (ptsum τ₁ τ₂) ts₁ tu₁ →
    (∀ w' vs₁ vu₁, w' < w → valrel d w' τ₁ vs₁ vu₁ → termrel d w' τ (ts₂ [beta1 vs₁]) (tu₂ [ beta1 vu₁])) →
    (∀ w' vs₂ vu₂, w' < w → valrel d w' τ₂ vs₂ vu₂ → termrel d w' τ (ts₃ [beta1 vs₂]) (tu₃ [ beta1 vu₂])) →
    termrel d w τ (S.caseof ts₁ ts₂ ts₃) (U.caseof tu₁ tu₂ tu₃).
  Proof.
    intros tr₁ tr₂ tr₃.

    (* first evaluate ts₁ and tu₁ *)
    change (S.caseof _ _ _) with (S.pctx_app ts₁ (S.pcaseof₁ S.phole ts₂ ts₃)).
    change (U.caseof _ _ _) with (U.pctx_app tu₁ (U.pcaseof₁ U.phole tu₂ tu₃)).
    refine (termrel_ectx _ _ tr₁ _); crush.

    (* then evaluate the caseof *)
    rewrite -> valrel_fixp in H.
    destruct H as [ot hyp]; subst; cbn in hyp.
    apply OfType_inversion_ptsum in ot.
    destruct ot as (vs' & vu' & [(? & ? & ot)|[(? & ?)|[(? & ?)|(? & ? & ot)]]]);
      subst; cbn in *; try contradiction;
      destruct (OfType_implies_Value ot) as [vvs vvu]; clear ot.
    - assert (S.eval (S.caseof (S.inl vs') ts₂ ts₃) (ts₂ [beta1 vs'])) by
          (apply (S.eval_ctx₀ S.phole); try refine (S.eval_case_inl _); simpl; intuition).
      assert (esn : S.evaln (S.caseof (S.inl vs') ts₂ ts₃) (ts₂ [beta1 vs']) 1) by (unfold S.evaln; eauto with eval).
      assert (U.ctxeval (U.caseof (U.inl vu') tu₂ tu₃) (tu₂ [beta1 vu'])) by
          (apply (U.mkCtxEval U.phole); try refine (U.eval_case_inl _ _); simpl; intuition).
      assert (eun : U.ctxevaln (U.caseof (U.inl vu') tu₂ tu₃) (tu₂ [beta1 vu']) 1) by (unfold U.ctxevaln; eauto with eval).
      destruct w'; try apply termrel_zero.
      refine (termrel_antired w' esn eun _ _ _); crush.
    - assert (S.eval (S.caseof (S.inr vs') ts₂ ts₃) (ts₃ [beta1 vs'])) by
          (apply (S.eval_ctx₀ S.phole); try refine (S.eval_case_inr _); simpl; intuition).
      assert (esn : S.evaln (S.caseof (S.inr vs') ts₂ ts₃) (ts₃ [beta1 vs']) 1) by (unfold S.evaln; eauto with eval).
      assert (U.ctxeval (U.caseof (U.inr vu') tu₂ tu₃) (tu₃ [beta1 vu'])) by
          (apply (U.mkCtxEval U.phole); try refine (U.eval_case_inr _ _); simpl; intuition).
      assert (eun : U.ctxevaln (U.caseof (U.inr vu') tu₂ tu₃) (tu₃ [beta1 vu']) 1) by (unfold U.ctxevaln; eauto with eval).
      destruct w'; try apply termrel_zero.
      refine (termrel_antired w' esn eun _ _ _); crush.
  Qed.

  (* Seq *)
  Lemma termrel_seq {d w τ ts₁ ts₂ tu₁ tu₂} :
    termrel d w ptunit ts₁ tu₁ →
    (∀ w', w' ≤ w → termrel d w' τ ts₂ tu₂) →
    termrel d w τ (S.seq ts₁ ts₂) (U.seq tu₁ tu₂).
  Proof.
    intros tr₁ tr₂.

    (* first evaluate ts₁ and tu₁ *)
    change (S.seq _ _) with (S.pctx_app ts₁ (S.pseq₁ S.phole ts₂)).
    change (U.seq _ _) with (U.pctx_app tu₁ (U.pseq₁ U.phole tu₂)).
    refine (termrel_ectx _ _ tr₁ _); crush.

    (* then reduce to ts₂ and tu₂ *)
    rewrite -> valrel_fixp in H.
    destruct H as [ot [eq₁ eq₂]]; subst.
    assert (S.eval (S.seq S.unit ts₂) ts₂) by
        (apply (S.eval_ctx₀ S.phole); try refine (S.eval_seq_next _); simpl; intuition).
    assert (esn : S.evaln (S.seq S.unit ts₂) ts₂ 1) by (unfold S.evaln; eauto with eval).

    (* assert (∀ Cu, U.ECtx Cu → U.eval (U.pctx_app (U.seq U.unit tu₂) Cu) (U.pctx_app tu₂ Cu)) by  *)
    (*     (intros Cu eCu; apply (U.eval_ctx₀ Cu); try refine (U.eval_seq_next _); simpl; intuition). *)
    (* assert (eun : ∀ Cu, U.ECtx Cu → U.evaln (U.pctx_app (U.seq U.unit tu₂) Cu) (U.pctx_app tu₂ Cu) 1) by eauto using U.evaln. *)

    (* attempt at using evalMax instead of doing manual labor *)
    pose (e := evalMax 2 (U.seq U.unit (var 0)) nil (idm UTm · tu₂) I).

    refine (termrel_antired w' esn e _ _ _); try omega.

    (* conclude *)
    apply tr₂; intuition.
  Qed.

  (* Fixt *)
  Lemma termrel_fix' {d w τ₁ τ₂ vs vu} :
    valrel d w (ptarr (ptarr τ₁ τ₂) (ptarr τ₁ τ₂)) vs vu →
    termrel d w (ptarr τ₁ τ₂) (S.fixt (repEmul τ₁) (repEmul τ₂) vs) (U.ufix₁ vu).
  Proof.
    (* well-founded induction on w *)
    revert w vs vu.
    refine (well_founded_ind lt_wf
                             (fun w =>
                                ∀ vs vu,
                                  valrel d w (ptarr (ptarr τ₁ τ₂) (ptarr τ₁ τ₂)) vs vu →
                                  termrel d w (ptarr τ₁ τ₂) (S.fixt (repEmul τ₁) (repEmul τ₂) vs) (U.ufix₁ vu)) _).
    intros w indHyp vs vu.

    (* destruct valrel assumption *)
    intros vr.
    rewrite -> valrel_fixp in vr.
    destruct vr as [ot hyp]; cbn in hyp.
    apply OfType_inversion_ptarr in ot.
    destruct ot as (tsb & tub & ? & ? & ?); crush.

    (* evaluate *)
    assert (es : S.fixt (repEmul τ₁) (repEmul τ₂) (S.abs (repEmul (ptarr τ₁ τ₂)) tsb) --> tsb [beta1 (S.abs (repEmul τ₁) (S.app (S.fixt (repEmul τ₁) (repEmul τ₂) (S.abs (repEmul τ₁ ⇒ repEmul τ₂) tsb[wkm↑])) (S.var 0)))]) by (refine (eval_ctx₀ S.phole _ _); constructor).
    assert (es1 : S.evaln (S.fixt (repEmul τ₁) (repEmul τ₂) (S.abs (repEmul (ptarr τ₁ τ₂)) tsb)) (tsb [beta1 (S.abs (repEmul τ₁) (S.app (S.fixt (repEmul τ₁) (repEmul τ₂) (S.abs (repEmul τ₁ ⇒ repEmul τ₂) tsb[wkm↑])) (S.var 0)))])  1) by
        (unfold S.evaln; eauto with eval; omega).
    assert (es2 : U.ctxevaln (U.ufix₁ (U.abs tub)) (tub[beta1 (U.abs (U.app (U.ufix₁ (U.abs tub[wkm↑])) (U.var 0)))]) 2) by
        (eauto using U.ufix₁_evaln' with eval).
    destruct w; try apply termrel_zero.
    refine (termrel_antired w es1 es2 _ _ _); unfold lev in *; simpl; try omega.
    clear es es1 es2.

    (* use the assumption about tsb and tub we extracted from vr *)
    refine (hyp w _ _ _ _); try omega.

    (* prove valrel for values being substituted into tsb and tub *)
    rewrite -> valrel_fixp.
    unfold valrel'; cbn; split; intros.
    - (* first the OfType relation *)
      crush.
      eapply ufix₁_ws.
      crush.
    - (* prove the termrel of the body of the abstractions *)
      refine (termrel_app (τ₁ := τ₁) (τ₂ := τ₂)_ _); crush.
      change (abs (tub[wkm↑][wkm↑][(beta1 tu')↑↑])) with ((abs tub)[wkm][wkm][(beta1 tu')↑]).
      change (S.abs _ _) with  ((S.abs (repEmul τ₁ ⇒ repEmul τ₂) tsb)[wkm][(beta1 ts')]).
      rewrite <- apply_wkm_comm.
      rewrite -> ?apply_wkm_beta1_cancel.
      change (U.app _ _) with (U.ufix₁ (abs tub)).
      (* the goal is now what we set out to prove initially but in a strictly
             later world, so we can use the induction hypothesis from our
             well-founded induction on worlds *)
      refine (indHyp _ _ _ _ _); crush.
      (* why do I need to call crush again? *)
      eapply hyp; crush.
  Qed.

  Lemma termrel_fix {d w τ₁ τ₂ ts tu} :
    termrel d w (ptarr (ptarr τ₁ τ₂) (ptarr τ₁ τ₂)) ts tu →
    termrel d w (ptarr τ₁ τ₂) (S.fixt (repEmul τ₁) (repEmul τ₂) ts) (U.app U.ufix tu).
  Proof.
    intros tr.

    (* first normalize ts and tu *)
    change (S.fixt _ _ _) with (S.pctx_app ts (S.pfixt (repEmul τ₁) (repEmul τ₂) S.phole)).
    change (U.app _ _) with (U.pctx_app tu (U.papp₂ U.ufix U.phole)).
    refine (termrel_ectx _ _ tr _); crush.
    destruct (valrel_implies_Value H) as [vvs vvu].

    (* next, reduce (U.app U.ufix tu) by one step in the conclusion *)
    assert (es1 : S.evaln (S.fixt (repEmul τ₁) (repEmul τ₂) vs) (S.fixt (repEmul τ₁) (repEmul τ₂) vs) 0) by
        (unfold S.evaln; eauto with eval).
    assert (es2 : U.ctxevaln (U.app U.ufix vu) (U.ufix₁ vu) 1)
      by (unfold U.ctxevaln; eauto using U.ufix_eval₁' with eval).
    refine (termrel_antired w' es1 es2 _ _ _); unfold lev in *; simpl; try omega.

    (* then defer to valrel_fix *)
    apply termrel_fix'; crush.
  Qed.

End TermRelation.
