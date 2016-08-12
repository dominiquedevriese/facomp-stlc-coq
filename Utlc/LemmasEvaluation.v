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
