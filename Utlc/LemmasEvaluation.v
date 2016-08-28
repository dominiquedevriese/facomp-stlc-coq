Require Export Db.Lemmas.
Require Export Utlc.SpecSyntax.
Require Export Utlc.SpecEvaluation.
Require Import Common.Common.

Local Ltac crush :=
  intros;
  repeat
    (cbn in *;
     eauto with eval;
     repeat crushDbSyntaxMatchH;
     repeat crushUtlcSyntaxMatchH;
     repeat crushUtlcEvaluationMatchH;
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

  Lemma pctx_cat_assoc (C₁ C₂ C₃ : PCtx) :
    pctx_cat (pctx_cat C₁ C₂) C₃ = pctx_cat C₁ (pctx_cat C₂ C₃).
  Proof.
    induction C₃; crush.
  Qed.

  Lemma pctx_cat_phole_leftzero C : pctx_cat phole C = C.
  Proof.
    induction C; crush.
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

Lemma eval_ctx {C t t'}  : t --> t' → t' ≠ wrong → ECtx C → pctx_app t C --> pctx_app t' C.
Proof.
  induction 1; intuition.
  rewrite <- ?pctx_cat_app in *.
  eauto using ectx_cat with eval.
Qed.

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
    intros vt; induction 1 as [? ? ? r'|?];
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
    induction r as [C t₁' t₂' e|C];
    rewrite -> ?pctx_app_sub; constructor;
      auto using eval₀_closed_under_substitution.
    destruct C; crush.
  Qed.

End SubstEval.

Section Determinacy.

  Lemma eval₀_determinacy {t₀ t₁ t₂} :
    t₀ -->₀ t₁ → t₀ -->₀ t₂ → t₁ = t₂.
  Proof.
    induction 1; inversion 1; subst; trivial;
    match goal with
      | H: ?x ≠ ?x |- _ => elim (H eq_refl)
      | H: ∀ _, _ ≠ _ |- _ => elim (H _ eq_refl)
      | H: ∀ _ _, _ ≠ _ |- _ => elim (H _ _ eq_refl)
    end.
  Qed.

  Ltac strengthenHyp :=
    match goal with
      (* Value inversion *)
      | [H: _ ∧ _               |- _] => destruct H
      | [H: False               |- _] => elim H
      (* Mismatched disequality assupmtions of evaluation *)
      | [H: ?x ≠ ?x             |- _] => elim H
      | [H: ∀ _, _ ≠ _          |- _] => elim (H _ eq_refl)
      | [H: ∀ _ _, _ ≠ _        |- _] => elim (H _ _ eq_refl)
      (* Eval₀ normal form reduction *)
      | [H: wrong        -->₀ _ |- _] => inversion H
      | [H: var _        -->₀ _ |- _] => inversion H
      | [H: abs _        -->₀ _ |- _] => inversion H
      | [H: unit         -->₀ _ |- _] => inversion H
      | [H: true         -->₀ _ |- _] => inversion H
      | [H: false        -->₀ _ |- _] => inversion H
      | [H: inl _        -->₀ _ |- _] => inversion H
      | [H: inr _        -->₀ _ |- _] => inversion H
      | [H: pair _ _     -->₀ _ |- _] => inversion H
      | [V: Value ?t, H: ?t -->₀ _ |- _] =>
        elim (values_are_eval₀_normal V H)
      (* Value strengthening *)
      | [V: Value (pctx_app _ ?C), E: ECtx ?C |- _] =>
        apply (value_pctx_inversion E) in V; cbn in V
      (* Strengthen with eval₀ determinacy. *)
      | [H1: ?s -->₀ ?t, H2: ?s -->₀ ?u |- _] =>
        pose proof (eval₀_determinacy H1 H2);
          clear H2; subst t
    end.

  Ltac invertEval₀ :=
    match goal with
      | [H: app _ _      -->₀ _ |- _] => inversion H; clear H
      | [H: proj₁ _      -->₀ _ |- _] => inversion H; clear H
      | [H: proj₂ _      -->₀ _ |- _] => inversion H; clear H
      | [H: ite _ _ _    -->₀ _ |- _] => inversion H; clear H
      | [H: caseof _ _ _ -->₀ _ |- _] => inversion H; clear H
      | [H: seq _ _      -->₀ _ |- _] => inversion H; clear H
    end.

  Ltac destructECtx :=
    match goal with
      | [E: ECtx ?C, H: pctx_app _ ?C = _ |- _] =>
        is_var C; destruct C
      | [E: ECtx ?C, H: _ = pctx_app _ ?C |- _] =>
        is_var C; destruct C
    end.

  Ltac crush :=
    repeat
      (try discriminate;
       repeat strengthenHyp;
       repeat crushUtlcSyntaxMatchH;
       cbn in *|-; subst*); eauto.

  Lemma determinacy_help1 {t₁ t₁' t₂ t₂' t} (r₁: t₁ -->₀ t₁') (r₂: t₂ -->₀ t₂') :
    ∀ {C₁ C₂}, ECtx C₁ → ECtx C₂ →
      t = pctx_app t₁ C₁ →
      t = pctx_app t₂ C₂ →
      pctx_app t₁' C₁ = pctx_app t₂' C₂.
  Proof.
    induction t; intros;
    (* First look at the decisions encoded in the evaluation contexts. Try as
       fast as possible to get rid of cases where one context indicates that
       the other is reducing a normal form. *)
    destruct C₁; crush;
    destruct C₂; crush;
    (* Handle the cases where both contexts actually do the same thing. *)
    cbn; f_equal; eauto;
    (* Only inconsistent cases from here on. *)
    exfalso;
    (* One of the contexts is empty while the other one is non-empty. Take
       a look at what the empty context is reducing. We got one layer of
       datatype information from the non-empty context which we use to find
       the reduction. *)
    try invertEval₀; crush;
    (* From the inversion of the reduction we learn that the non-empty context
       must in fact be a normal-form which is impossible. Find the non-empty
       context again and give it a final blow. *)
    try destructECtx; crush.
  Qed.

  Lemma determinacy_help2 {t₁ t₁' t} (e₁: t₁ -->₀ t₁') :
    ∀ {C₁ C₂},
      t = pctx_app t₁ C₁ →
      t = pctx_app wrong C₂ →
      ECtx C₁ → ECtx C₂ →
      False.
  Proof.
    induction t; intros; crush;
    destruct C₂; crush;
    destruct C₁; crush;
    inversion e₁; crush;
    destruct C₂; crush.
  Qed.

  Lemma determinacy {t t₁ t₂} :
    t --> t₁ → t --> t₂ → t₁ = t₂.
  Proof.
    do 2 inversion 1.
    - eapply determinacy_help1; eauto.
    - exfalso; eapply determinacy_help2; eauto.
    - exfalso; eapply determinacy_help2; eauto.
    - reflexivity.
  Qed.

End Determinacy.

Section Termination'.

  Lemma termination_closed_under_antireduction {t t'} :
    t --> t' → t' ⇓ → t ⇓.
  Proof.
    intros e term. constructor. intros t'' e'.
    assert (t' = t'') by exact (determinacy e e').
    subst; assumption.
  Qed.

  Lemma termination_closed_under_antireductionStar {t t'} :
    t -->* t' → t' ⇓ → t ⇓.
  Proof.
    intros e term.
    induction e; eauto using termination_closed_under_antireduction.
  Qed.
End Termination'.

Section CtxEval.
  Lemma ctxeval_eval {t t'} : ctxeval t t' → t --> t'.
  Proof.
    destruct 1.
    refine (eval_ctx₀ _ _ _); assumption.
  Qed.

  Lemma ctxevaln_evaln {t t' n} : ctxevaln t t' n → evaln t t' n.
  Proof.
  Admitted.

  (* The following implication is actually an equivalence, but we don't need that. *)
  Lemma ctxeval_eval_ctx {t t'} : ctxeval t t' → forall Cu, ECtx Cu → pctx_app t Cu --> pctx_app t' Cu.
  Proof.
    destruct 1; intros; rewrite <- ?pctx_cat_app; eauto using ectx_cat with eval.
  Qed.

  Lemma extend_ctxeval tu tu' Cu : ECtx Cu → ctxeval tu tu' → ctxeval (pctx_app tu Cu) (pctx_app tu' Cu).
  Proof.
    intros eCu ce. 
    induction ce.
    rewrite <- ?pctx_cat_app.
    eauto using ctxeval, ectx_cat.
  Qed.
End CtxEval.

Section EvalN.
  Lemma evaln_to_evalStar {t t' n} :
    evaln t t' n → t -->* t'.
  Proof.
    induction 1; crush.
  Qed.

  Lemma evaln_to_evalPlus {t t' n} :
    evaln t t' (S n) → t -->+ t'.
  Proof.
    induction 1; crush.
  Qed.

  Lemma TerminatingN_eval {t t' n } :
    t --> t' → t' ⇓_ n ↔ t ⇓_ (S n).
  Proof.
    intros e. constructor.
    - intros term. apply TerminatingIS. intros t'' e'.
      replace t'' with t' by apply (determinacy e e').
      assumption.
    - intro term. refine (TerminatingDN _ _ term _ e).
  Qed.

  Lemma TerminatingN_evaln {t t' n } n' :
    evaln t t' n → t' ⇓_ n' ↔ t ⇓_ (n + n').
  Proof.
    induction 1; eauto using iff_refl, iff_trans, TerminatingN_eval. 
  Qed.

  Lemma TerminatingN_lt {t n n'} :
    TerminatingN t n → n ≤ n' → TerminatingN t n'.
  Proof.
    intros term. revert n'.
    induction term; [ constructor; auto | idtac].
    intros n' le.
    destruct (S_le le); destruct_conjs; subst.
    apply TerminatingIS.
    auto.
  Qed.

  Lemma ctxevaln_ctx {t t' n} :
    ctxevaln t t' n -> forall C, ECtx C → evaln (pctx_app t C) (pctx_app t' C) n.
  Proof.
    intros ec.
    induction 1; eauto using eval_ctx with eval.
  Qed.
End EvalN.