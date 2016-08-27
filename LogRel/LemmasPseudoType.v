Require Import Stlc.LemmasTyping.
Require Export LogRel.PseudoType.

Section OfType.

  Local Ltac solveOfType :=
    unfold OfType, OfTypeStlc; intros;
    repeat
      match goal with
        | [ |- _ ∧ _ ] => split
      end;
    crushTyping.

  Lemma OfType_unit : OfType ptunit S.unit U.unit.
  Proof. solveOfType. Qed.

  Lemma OfType_true : OfType ptbool S.true U.true.
  Proof. solveOfType. Qed.

  Lemma OfType_false : OfType ptbool S.false U.false.
  Proof. solveOfType. Qed.

  Lemma OfType_inl {τ₁ τ₂ ts tu} :
    OfType τ₁ ts tu →
    OfType (ptsum τ₁ τ₂) (S.inl ts) (U.inl tu).
  Proof. solveOfType. Qed.

  Lemma OfType_inr {τ₁ τ₂ ts tu} :
    OfType τ₂ ts tu →
    OfType (ptsum τ₁ τ₂) (S.inr ts) (U.inr tu).
  Proof. solveOfType. Qed.

  Lemma OfType_pair {τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    OfType τ₁ ts₁ tu₁ →
    OfType τ₂ ts₂ tu₂ →
    OfType (ptprod τ₁ τ₂) (S.pair ts₁ ts₂) (U.pair tu₁ tu₂).
  Proof. solveOfType. Qed.

  Lemma OfType_lambda {τ₁ τ₂ tsb tub} :
    ⟪ empty ⊢ S.abs (repEmul τ₁) tsb : repEmul τ₁ ⇒ repEmul τ₂ ⟫ →
    OfType (ptarr τ₁ τ₂) (S.abs (repEmul τ₁) tsb) (U.abs tub).
  Proof. solveOfType. Qed.


  Lemma OfTypeUtlc_implies_Value {τ tu} :
    OfTypeUtlc τ tu →
    U.Value tu.
  Proof.
    revert tu.
    induction τ; cbn; intros;
    repeat
      (try
         match goal with
           | H: False |- _ => elim H
           | H: True  |- _ => clear H
           | H: _ ∧ _ |- _ => destruct  H
           | H: match ?tu with _ => _ end |- _ =>
             destruct tu eqn: ?; cbn in H
           | H: _ ∨ _ |- _ => destruct  H
         end;
       cbn; subst; auto).
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
      | [ |- OfType ptunit S.unit U.unit ] => apply OfType_unit
      | [ |- OfType ptbool S.true U.true ] => apply OfType_true
      | [ |- OfType ptbool S.false U.false ] => apply OfType_false
      | [ |- OfType (ptsum _ _) (S.inl _) (U.inl _)] => apply OfType_inl
      | [ |- OfType (ptsum _ _) (S.inr _) (U.inr _)] => apply OfType_inr
      | [ |- OfType (ptprod _ _) (S.pair _ _) (U.pair _ _) ] => apply OfType_pair
      | [ |- OfType (ptarr _ _) (S.abs _ _) (U.abs _) ] => apply OfType_lambda
    end.
