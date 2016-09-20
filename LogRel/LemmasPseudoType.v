Require Import Stlc.CanForm.
Require Import Stlc.LemmasTyping.
Require Export LogRel.PseudoType.
Require Import UVal.UVal.

Section RepEmul.
  Lemma repEmul_embed_leftinv τ :
    repEmul (embed τ) = τ.
  Proof.
    induction τ; simpl; try f_equal; intuition.
  Qed.

  Lemma repEmulCtx_embedCtx_leftinv Γ :
    repEmulCtx (embedCtx Γ) = Γ.
  Proof.
    induction Γ; simpl; try f_equal; eauto using repEmul_embed_leftinv.
  Qed.

End RepEmul.

Ltac crushRepEmulEmbed :=
  match goal with
      [ |- context[ repEmul( embed ?τ) ] ] => rewrite -> (repEmul_embed_leftinv τ)
    | [ |- context[ repEmulCtx( embedCtx ?Γ) ] ] => rewrite -> (repEmulCtx_embedCtx_leftinv Γ)
  end.

Lemma getevar_repEmulCtx {i τ Γ} :
  ⟪ i : τ ∈ repEmulCtx Γ ⟫ →
  exists τ', ⟪ i : τ' p∈ Γ ⟫ ∧ τ = repEmul τ'.
Proof.
  revert i. induction Γ as [|Γ IHΓ τ'']; 
  inversion 1; [idtac| destruct (IHΓ _ H4) as [? [? ?]]];
  eauto using GetEvarP.
Qed.

Section OfType.

  Local Ltac crush :=
    unfold OfType, OfTypeStlc, OfTypeUtlc; intros;
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

  Lemma OfType_lambda {τ₁ τ₂ τ₁' tsb tub} :
    τ₁' = repEmul τ₁ →
    ⟪ empty ⊢ S.abs (repEmul τ₁) tsb : repEmul τ₁ ⇒ repEmul τ₂ ⟫ →
    OfType (ptarr τ₁ τ₂) (S.abs τ₁' tsb) (U.abs tub).
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

  Lemma OfTypeUtlc_inversion_ptarr {τ₁ τ₂ tu} :
    OfTypeUtlc (ptarr τ₁ τ₂) tu →
    ∃ tu', tu = U.abs tu'.
  Proof. crush. Qed.

  Lemma OfTypeUtlc_inversion_ptprod {τ₁ τ₂ tu} :
    OfTypeUtlc (ptprod τ₁ τ₂) tu →
    ∃ tu₁ tu₂, tu = U.pair tu₁ tu₂ ∧ OfTypeUtlc τ₁ tu₁ ∧ OfTypeUtlc τ₂ tu₂.
  Proof. crush. Qed.

  Lemma OfTypeUtlc_inversion_ptsum {τ₁ τ₂ tu} :
    OfTypeUtlc (ptsum τ₁ τ₂) tu →
    ∃ tu', (tu = U.inl tu' ∧ OfTypeUtlc τ₁ tu') ∨
           (tu = U.inr tu' ∧ OfTypeUtlc τ₂ tu').
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

  Lemma OfType_pEmulDV {n p ts tu} :
    S.Value ts ∧ U.Value tu ∧
    ⟪ empty ⊢ ts : UVal n ⟫ → 
    OfType (pEmulDV n p) ts tu.
  Proof. crush. Qed.

End OfType.

Ltac crushOfType :=
  repeat
    match goal with
      | [ H: OfType ptunit _ _ |- _ ] => apply OfType_inversion_ptunit in H
      | [ H: OfType ptbool _ _ |- _ ] => apply OfType_inversion_ptbool in H
      | [ H: OfType (ptsum _ _) _ _ |- _ ] => apply OfType_inversion_ptsum in H
      | [ H: OfType (ptprod _ _) _ _ |- _ ] => apply OfType_inversion_ptprod in H
      | [ H: OfType (ptarr _ _) _ _ |- _ ] => apply OfType_inversion_ptarr in H
      | [ H: OfTypeUtlc (ptarr _ _) _ |- _ ] => apply OfTypeUtlc_inversion_ptarr in H
      | [ H: OfTypeUtlc (ptprod _ _) _ |- _ ] => apply OfTypeUtlc_inversion_ptprod in H
      | [ H: OfTypeUtlc (ptsum _ _) _ |- _ ] => apply OfTypeUtlc_inversion_ptsum in H
      | [ H: OfType (pEmulDV _ _) _ _ |- _ ] => apply OfType_inversion_pEmulDV in H
      (* | [ H: OfTypeUtlc (ptprod _ _) ?t  |- _ ] => destruct t; cbn in H; try discriminate *)
      (* | [ H: OfTypeUtlc (ptsum _ _) ?t  |- _ ] => destruct t; cbn in H; try discriminate *)
      (* | [ H: OfTypeUtlc ptbool ?t  |- _ ] =>  change (OfTypeUtlc ptbool t) with (t = U.true ∨ t = U.false) in H *)
      (* | [ H: OfTypeUtlc ptunit ?t  |- _ ] => change (OfTypeUtlc ptunit t) with (t = U.unit) in H; subst t *)
      (* | [ H: OfTypeUtlc (ptarr _ _) ?t  |- _ ] => destruct t; cbn in H; try discriminate *)
      | [ |- OfType ptunit S.unit U.unit ] => apply OfType_unit
      | [ |- OfType ptbool S.true U.true ] => apply OfType_true
      | [ |- OfType ptbool S.false U.false ] => apply OfType_false
      | [ |- OfType (ptsum _ _) (S.inl _) (U.inl _)] => apply OfType_inl
      | [ |- OfType (ptsum _ _) (S.inr _) (U.inr _)] => apply OfType_inr
      | [ |- OfType (ptprod _ _) (S.pair _ _) (U.pair _ _) ] => apply OfType_pair
      | [ |- OfType (ptarr _ _) (S.abs _ _) (U.abs _) ] => apply OfType_lambda
      | [ |- OfType (pEmulDV _ _) _ _ ] => apply OfType_pEmulDV
    end.
