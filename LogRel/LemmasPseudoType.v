Require Import Stlc.CanForm.
Require Import Stlc.LemmasTyping.
Require Export LogRel.PseudoType.
Require Import UVal.UVal.

Section OfType.

  Local Ltac crush :=
    unfold OfType, OfTypeStlc; intros;
    repeat
      (subst;
       stlcCanForm;
       crushTyping;
       destruct_conjs;
       repeat
         match goal with
           | H: False |- _ => elim H
           | H: True  |- _ => clear H
           | H: _ ∧ _ |- _ => destruct  H
           | H: match ?tu with _ => _ end |- _ =>
             destruct tu eqn: ?; cbn in H
           | H: _ ∨ _ |- _ => destruct  H
           | [ |- _ ∧ _ ] => split
         end); eauto 20.

  Lemma OfType_unit : OfType ptunit S.unit U.unit.
  Proof. crush. Qed.

  Lemma OfType_true : OfType ptbool S.true U.true.
  Proof. crush. Qed.

  Lemma OfType_false : OfType ptbool S.false U.false.
  Proof. crush. Qed.

  Lemma OfType_inl {τ₁ τ₂ ts tu} :
    OfType τ₁ ts tu →
    OfType (ptsum τ₁ τ₂) (S.inl ts) (U.inl tu).
  Proof. crush. Qed.

  Lemma OfType_inr {τ₁ τ₂ ts tu} :
    OfType τ₂ ts tu →
    OfType (ptsum τ₁ τ₂) (S.inr ts) (U.inr tu).
  Proof. crush. Qed.

  Lemma OfType_pair {τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    OfType τ₁ ts₁ tu₁ →
    OfType τ₂ ts₂ tu₂ →
    OfType (ptprod τ₁ τ₂) (S.pair ts₁ ts₂) (U.pair tu₁ tu₂).
  Proof. crush. Qed.

  Lemma OfType_lambda {τ₁ τ₂ tsb tub} :
    ⟪ empty ⊢ S.abs (repEmul τ₁) tsb : repEmul τ₁ ⇒ repEmul τ₂ ⟫ →
    OfType (ptarr τ₁ τ₂) (S.abs (repEmul τ₁) tsb) (U.abs tub).
  Proof. crush. Qed.

  Lemma OfType_inversion_ptunit {ts tu} :
    OfType ptunit ts tu →
    ts = S.unit ∧ tu = U.unit.
  Proof. crush. Qed.

  Lemma OfType_inversion_ptbool {ts tu} :
    OfType ptbool ts tu →
    ts = S.true ∧ tu = U.true ∨
    ts = S.true ∧ tu = U.false ∨
    ts = S.false ∧ tu = U.true ∨
    ts = S.false ∧ tu = U.false.
  Proof. crush. Qed.

  Lemma OfType_inversion_ptsum {τ₁ τ₂ ts tu} :
    OfType (ptsum τ₁ τ₂) ts tu →
    ∃ ts' tu',
      ts = S.inl ts' ∧ tu = U.inl tu' ∧ OfType τ₁ ts' tu' ∨
      ts = S.inl ts' ∧ tu = U.inr tu' ∨
      ts = S.inr ts' ∧ tu = U.inl tu' ∨
      ts = S.inr ts' ∧ tu = U.inr tu' ∧ OfType τ₂ ts' tu'.
  Proof. crush. Qed.

  Lemma OfType_inversion_ptprod {τ₁ τ₂ ts tu} :
    OfType (ptprod τ₁ τ₂) ts tu →
    ∃ ts₁ tu₁ ts₂ tu₂,
      ts = S.pair ts₁ ts₂ ∧
      tu = U.pair tu₁ tu₂ ∧
      OfType τ₁ ts₁ tu₁ ∧
      OfType τ₂ ts₂ tu₂.
  Proof. crush. Qed.

  Lemma OfType_inversion_ptarr {τ₁ τ₂ ts tu} :
    OfType (ptarr τ₁ τ₂) ts tu →
    ∃ ts' tu',
      ts = S.abs (repEmul τ₁) ts' ∧
      tu = U.abs tu' ∧
      ⟪ empty ▻ repEmul τ₁ ⊢ ts' : repEmul τ₂ ⟫.
  Proof. crush. Qed.

  Lemma OfType_inversion_pEmulDV {n p ts tu} :
    OfType (pEmulDV n p) ts tu →
    S.Value ts ∧ U.Value tu ∧
    ⟪ empty ⊢ ts : UVal n ⟫.
  Proof. crush. Qed.

  Lemma OfTypeUtlc_implies_Value {τ tu} :
    OfTypeUtlc τ tu →
    U.Value tu.
  Proof.
    revert tu.
    induction τ; crush.
  Qed.

  Lemma OfType_implies_Value {τ ts tu} :
    OfType τ ts tu →
    S.Value ts ∧ U.Value tu.
  Proof.
    unfold OfType, OfTypeStlc.
    intros ot; destruct_conjs;
    eauto using OfTypeUtlc_implies_Value.
  Qed.

End OfType.

Ltac crushOfType :=
  repeat
    match goal with
      | H: OfType ptunit _ _ |- _ => apply OfType_inversion_ptunit in H
      | H: OfType ptbool _ _ |- _ => apply OfType_inversion_ptbool in H
      | H: OfType (ptsum _ _) _ _ |- _ => apply OfType_inversion_ptsum in H
      | H: OfType (ptprod _ _) _ _ |- _ => apply OfType_inversion_ptprod in H
      | H: OfType (ptarr _ _) _ _ |- _ => apply OfType_inversion_ptarr in H
      | H: OfType (pEmulDV _ _) _ _ |- _ => apply OfType_inversion_pEmulDV in H
      | [ |- OfType ptunit S.unit U.unit ] => apply OfType_unit
      | [ |- OfType ptbool S.true U.true ] => apply OfType_true
      | [ |- OfType ptbool S.false U.false ] => apply OfType_false
      | [ |- OfType (ptsum _ _) (S.inl _) (U.inl _)] => apply OfType_inl
      | [ |- OfType (ptsum _ _) (S.inr _) (U.inr _)] => apply OfType_inr
      | [ |- OfType (ptprod _ _) (S.pair _ _) (U.pair _ _) ] => apply OfType_pair
      | [ |- OfType (ptarr _ _) (S.abs _ _) (U.abs _) ] => apply OfType_lambda
    end.
