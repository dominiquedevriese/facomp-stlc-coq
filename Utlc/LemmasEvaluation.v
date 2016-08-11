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

Section SubstEval.

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

  Lemma value_sub t (v: Value t) :
    ∀ (ζ: Sub UTm), Value t[ζ].
  Proof. induction t; crush. Qed.
  Hint Resolve value_sub.

  Lemma ectx_sub C (ectx_C: ECtx C) :
    ∀ (ζ: Sub UTm), ECtx C[ζ].
  Proof. induction C; crush. Qed.
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
    induction r as [C t₁' t₂' e|C]; rewrite -> ?pctx_app_sub.
    - constructor; eauto using eval₀_closed_under_substitution.
    - constructor; induction C; crush.
  Qed.

End SubstEval.

Lemma ectx_cat (C₁ C₂: PCtx) :
  ECtx C₁ → ECtx C₂ → ECtx (pctx_cat C₁ C₂).
Proof.
  induction C₂; simpl; intros; destruct_conjs; auto.
Qed.

Lemma pctx_cat_app (t : UTm) (C₁ C₂ : PCtx) :
  pctx_app t (pctx_cat C₁ C₂) = pctx_app (pctx_app t C₁) C₂.
Proof.
  induction C₂; crush.
Qed.

(* The following doesn't hold here: C[wrong] evaluates to wrong in single step *)
(* Lemma eval_ctx {C t t'}  : t --> t' -> ECtx C -> pctx_app t C --> pctx_app t' C. *)
(* Proof. *)
(*   induction 1. *)
(*   rewrite <- ?pctx_cat_app in *. *)
(*   eauto using ectx_cat with eval. *)
(* Qed. *)

Lemma ectx_wrong_not_value {C} : ECtx C -> not (Value (pctx_app wrong C)).
Proof.
  intros ec val.
  induction C; crush.
Qed.

Definition normal' (t : UTm) := ∀ t', ¬ (t --> t').
Lemma values_are_normal' {t : UTm} : Value t -> normal' t.
Proof.
  intros vt t' r; revert vt.
  induction r as [C ? ? r'|C]; crush.
  - induction C; crush.
    inversion r'; crush.
  - now apply ectx_wrong_not_value in vt.
Qed.

Lemma values_are_normal {t : UTm} : Value t -> normal t.
Proof.
  generalize @values_are_normal'.
  unfold normal, normal', not.
  intros ? ? (); eauto.
Qed.

Lemma TerminatingDN (t: UTm) n (m: t ⇓_ (S n)) :
  ∀ t', t --> t' → TerminatingN t' n.
Proof. 
  depind m; intros t' e'; eauto using values_are_normal.
  exfalso.
  refine (values_are_normal H _); exists t'; auto.
Qed.


Lemma TerminatingN_Terminating {t : UTm} {n} : t ⇓_ n -> t ⇓.
Proof.
  induction 1; constructor; try assumption.
  intros t' e'. exfalso. refine (values_are_normal H _).
  exists t'. auto.
Qed.