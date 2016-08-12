Require Export Db.Lemmas.
Require Export Utlc.SpecSyntax.
Require Export Utlc.SpecEvaluation.

Local Ltac crush :=
  intros;
  repeat
    (cbn in *;
     eauto with eval;
     repeat crushDbSyntaxMatchH;
     repeat crushUtlcSyntaxMatchH;
     (* repeat crushDbLemmasMatchH; *)
     repeat crushDbLemmasRewriteH;
     try subst);
  try discriminate;
  eauto.

Section EvaluationContexts.

  Lemma pctx_app_sub' C :
    ∀ (ζ: Sub UTm) t,
      (pctx_app t C)[ζ] =
      pctx_app t[foldlDom up (depthlPCtx C) ζ] C[ζ].
  Proof. induction C; crush. Qed.

  Lemma pctx_app_sub C :
    ∀ (ζ: Sub UTm) t,
      (pctx_app t C)[ζ] =
      pctx_app t[ζ ↑⋆ depthPCtx C] C[ζ].
  Proof. induction C; crush. Qed.

  Lemma pctx_cat_app (t : UTm) (C₁ C₂ : PCtx) :
    pctx_app t (pctx_cat C₁ C₂) = pctx_app (pctx_app t C₁) C₂.
  Proof.
    induction C₂; crush.
  Qed.

  Lemma ectx_cat (C₁ C₂: PCtx) :
    ECtx C₁ → ECtx C₂ → ECtx (pctx_cat C₁ C₂).
  Proof. induction C₂; crush. Qed.

  Lemma value_sub t (v: Value t) :
    ∀ (ζ: Sub UTm), Value t[ζ].
  Proof. induction t; crush. Qed.
  Hint Resolve value_sub.

  Lemma ectx_sub C (ectx_C: ECtx C) :
    ∀ (ζ: Sub UTm), ECtx C[ζ].
  Proof. induction C; crush. Qed.
  Hint Resolve ectx_sub.

End EvaluationContexts.

(* The following doesn't hold here: C[wrong] evaluates to wrong in single step *)
(* Lemma eval_ctx {C t t'}  : t --> t' -> ECtx C -> pctx_app t C --> pctx_app t' C. *)
(* Proof. *)
(*   induction 1. *)
(*   rewrite <- ?pctx_cat_app in *. *)
(*   eauto using ectx_cat with eval. *)
(* Qed. *)

Section Values.

  Lemma value_pctx_inversion {C} (eC: ECtx C) :
    ∀ t, Value (pctx_app t C) → Value t.
  Proof. induction C; cbn in *; intuition. Qed.

  Lemma ectx_wrong_not_value {C} : ECtx C -> ¬ (Value (pctx_app wrong C)).
  Proof.
    intros ec val.
    apply value_pctx_inversion in val; crush.
  Qed.

  Lemma values_are_eval₀_normal {t t'} :
    Value t → t -->₀ t' → False.
  Proof. inversion 2; crush. Qed.

  Lemma values_are_normal {t : UTm} : Value t → normal t.
  Proof.
    intros vt; induction 1 as [? ? ? r'];
      apply value_pctx_inversion in vt;
      eauto using values_are_eval₀_normal.
  Qed.
  Global Arguments values_are_normal {_} _ {_} _.

End Values.

Section Termination.

  Lemma TerminatingI' (t: UTm) (vt: Value t) :
    ∀ t', t --> t' → t'⇓.
  Proof. intros t' r; elim (values_are_normal vt r). Qed.

  Lemma TerminatingIV' (t: UTm) (vt: Value t) :
    ∀ t' n, t --> t' → t'⇓_n.
  Proof. intros t' n r; elim (values_are_normal vt r). Qed.

  Lemma values_terminate (t: UTm) (vt: Value t) :
    t ⇓.
  Proof. constructor; eauto using TerminatingI'. Qed.

  Lemma values_terminateN (t: UTm) (vt: Value t) :
    ∀ n, t ⇓_ n.
  Proof. constructor; eauto. Qed.

  Lemma TerminatingDN (t: UTm) n (m: t ⇓_ (S n)) :
    ∀ t' : UTm, t --> t' → t'⇓_n.
  Proof. depind m; eauto using TerminatingIV'. Qed.

  Lemma TerminatingN_Terminating {t : UTm} {n} : t ⇓_ n -> t ⇓.
  Proof. induction 1;
    eauto using Terminating, values_terminate with eval.
  Qed.

End Termination.

Section SubstEval.

  Hint Resolve value_sub.
  Hint Resolve ectx_sub.

  Lemma eval₀_closed_under_substitution {t1 t2} (r: t1 -->₀ t2) :
    ∀ (ζ: Sub UTm), t1[ζ] -->₀ t2[ζ].
  Proof.
    induction r; crush; eauto with eval; unfold not in *;
    constructor; crush;
    match goal with
      | [|- ?t[?ζ] ≠ _] =>
        destruct t eqn: ?
    end; crush.
  Qed.

  Lemma eval_closed_under_substitution {t1 t2} (r: t1 --> t2) (ζ: Sub UTm) :
    t1[ζ] --> t2[ζ].
  Proof.
    induction r as [C t₁' t₂' e];
    rewrite -> ?pctx_app_sub; constructor;
      auto using eval₀_closed_under_substitution.
  Qed.

End SubstEval.

Section InductionPrinciples.

  Lemma eval_ind' (P : UTm → UTm → Prop)
    (f : ∀ t₁ t₂ : UTm, Value t₁ → Value t₂ → (∀ t : UTm, t₁ ≠ abs t) → P (app t₁ t₂) wrong)
    (f0 : ∀ t₁ t₂ : UTm, Value t₂ → P (app (abs t₁) t₂) t₁[beta1 t₂])
    (f1 : ∀ t₁ t₂ t₃ : UTm, Value t₁ → t₁ ≠ true → t₁ ≠ false → P (ite t₁ t₂ t₃) wrong)
    (f2 : ∀ t₁ t₂ : UTm, P (ite true t₁ t₂) t₁)
    (f3 : ∀ t₁ t₂ : UTm, P (ite false t₁ t₂) t₂)
    (f4 : ∀ t : UTm, Value t → (∀ t₁ t₂ : UTm, t ≠ pair t₁ t₂) → P (proj₁ t) wrong)
    (f5 : ∀ t₁ t₂ : UTm, Value t₁ → Value t₂ → P (proj₁ (pair t₁ t₂)) t₁)
    (f6 : ∀ t : UTm, Value t → (∀ t₁ t₂ : UTm, t ≠ pair t₁ t₂) → P (proj₂ t) wrong)
    (f7 : ∀ t₁ t₂ : UTm, Value t₁ → Value t₂ → P (proj₂ (pair t₁ t₂)) t₂)
    (f8 : ∀ t t₁ t₂ : UTm, Value t → (∀ t' : UTm, t ≠ inl t') → (∀ t' : UTm, t ≠ inr t') → P (caseof t t₁ t₂) wrong)
    (f9 : ∀ t t₁ t₂ : UTm, Value t → P (caseof (inl t) t₁ t₂) t₁[beta1 t])
    (f10 : ∀ t t₁ t₂ : UTm, Value t → P (caseof (inr t) t₁ t₂) t₂[beta1 t])
    (f11 : ∀ t₁ t₂ : UTm, Value t₁ → P (seq t₁ t₂) t₂)
    (f12 : ∀ t₁ t₁' t₂ : UTm, t₁ --> t₁' → P t₁ t₁' → P (app t₁ t₂) (app t₁' t₂))
    (f13 : ∀ t₁ t₂ t₂' : UTm, Value t₁ → t₂ --> t₂' → P t₂ t₂' → P (app t₁ t₂) (app t₁ t₂'))
    (f14 : ∀ t₁ t₁' t₂ t₃ : UTm, t₁ --> t₁' → P t₁ t₁' → P (ite t₁ t₂ t₃) (ite t₁' t₂ t₃))
    (f15 : ∀ t₁ t₁' t₂ : UTm, t₁ --> t₁' → P t₁ t₁' → P (pair t₁ t₂) (pair t₁' t₂))
    (f16 : ∀ t₁ t₂ t₂' : UTm, Value t₁ → t₂ --> t₂' → P t₂ t₂' → P (pair t₁ t₂) (pair t₁ t₂'))
    (f17 : ∀ t₁ t₁' : UTm, t₁ --> t₁' → P t₁ t₁' → P (proj₁ t₁) (proj₁ t₁'))
    (f18 : ∀ t₁ t₁' : UTm, t₁ --> t₁' → P t₁ t₁' → P (proj₂ t₁) (proj₂ t₁'))
    (f19 : ∀ t₁ t₁' : UTm, t₁ --> t₁' → P t₁ t₁' → P (inl t₁) (inl t₁'))
    (f20 : ∀ t₁ t₁' : UTm, t₁ --> t₁' → P t₁ t₁' → P (inr t₁) (inr t₁'))
    (f21 : ∀ t₁ t₁' t₂ t₃ : UTm, t₁ --> t₁' → P t₁ t₁' → P (caseof t₁ t₂ t₃) (caseof t₁' t₂ t₃))
    (f22 : ∀ t₁ t₁' t₂ : UTm, t₁ --> t₁' → P t₁ t₁' → P (seq t₁ t₂) (seq t₁' t₂)) :
    ∀ t t', t --> t' → P t t'.
  Proof.
    induction 1 as [C t t' r' eC]; crush.
    revert eC t t' r'.
    induction C; cbn in *; intuition.
    induction r'; cbn in *; intuition.
  Qed.

End InductionPrinciples.

Local Ltac crushEval :=
  repeat
  match goal with
    | [ V: Value (pctx_app _ ?C), E: ECtx ?C |- _ ] =>
      apply (value_pctx_inversion E) in V; cbn in V
    | H: _ = _ → False |- _ =>
      elim (H eq_refl)
    | H: ∀ _, _ = _ → False |- _ =>
      elim (H _ eq_refl)
    | H: ∀ _ _, _ = _ → False |- _ =>
      elim (H _ _ eq_refl)
    | [r: ?t -->₀ _ |- _] =>
      let v := fresh "v" in
      assert (v: Value t) by (cbn; eauto);
        elim (values_are_eval₀_normal v r)
    | [r: ?t --> _ |- _] =>
      let v := fresh "v" in
      assert (v: Value t) by (cbn; eauto);
        elim (values_are_normal v r)
  end.

Section Determinism.

  Lemma eval₀_deterministic {t₀ t₁ t₂} :
    t₀ -->₀ t₁ → t₀ -->₀ t₂ → t₁ = t₂.
  Proof.
    induction 1; inversion 1; crush;
    unfold not in * |-; crushEval.
  Qed.

  Lemma eval_deterministic {t₀ t₁ t₂} :
    t₀ --> t₁ → t₀ --> t₂ → t₁ = t₂.
  Proof.
    intros r₁; revert t₂.
    induction r₁ using eval_ind'; intros ? r₂;
    match type of r₂ with
      | ?s --> ?t =>
        let Heqs := fresh in
        let Heqt := fresh in
        remember s eqn: Heqs; revert Heqs;
        remember t eqn: Heqt; revert Heqt
    end;
    induction r₂ using eval_ind';
    intros; repeat crushUtlcSyntaxMatchH;
    try discriminate; subst*;
    unfold not in * |-; crushEval;
    eauto using eval₀ with eval.
  Qed.

End Determinism.
