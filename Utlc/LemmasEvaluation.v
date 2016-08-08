Require Export Db.Lemmas.
Require Export Utlc.SpecSyntax.
Require Export Utlc.SpecEvaluation.
Require Export Coq.Program.Tactics.

Section SubstEval.

  Lemma pctx_app_sub' C :
    ∀ (ζ: Sub UTm) t,
      (pctx_app t C)[ζ] =
      pctx_app t[foldlDom up (depthlPCtx C) ζ] C[ζ].
  Proof. induction C; crushUtlc. Qed.

  Hint Rewrite <- ups_dunion : infrastructure.
  Lemma pctx_app_sub C :
    ∀ (ζ: Sub UTm) t,
      (pctx_app t C)[ζ] =
      pctx_app t[ζ ↑⋆ depthPCtx C] C[ζ].
  Proof. induction C; crushUtlc. Qed.
  Hint Rewrite pctx_app_sub : infrastructure.

  Lemma value_sub t (v: Value t) :
    ∀ (ζ: Sub UTm), Value t[ζ].
  Proof. induction t; crushUtlc. Qed.
  Hint Resolve value_sub.

  Lemma ectx_sub C (ectx_C: ECtx C) :
    ∀ (ζ: Sub UTm), ECtx C[ζ].
  Proof. induction C; crushUtlc. Qed.
  Hint Resolve ectx_sub.

  Lemma eval_closed_under_substitution {t1 t2} (r: t1 --> t2) :
    ∀ (ζ: Sub UTm), t1[ζ] --> t2[ζ].
  Proof.
    induction r; crushUtlc; eauto with eval; unfold not in *.
    - constructor; destruct C; crushUtlc.
    - constructor; destruct t₁; crushUtlc.
    - constructor; destruct t₁; crushUtlc.
    - constructor; destruct t; crushUtlc.
    - constructor; destruct t; crushUtlc.
    - constructor; destruct t; crushUtlc.
  Qed.

End SubstEval.
