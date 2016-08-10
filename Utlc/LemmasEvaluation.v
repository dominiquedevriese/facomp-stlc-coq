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

  Lemma eval₀_closed_under_substitution {t1 t2} (r: t1 -->₀ t2) :
    ∀ (ζ: Sub UTm), t1[ζ] -->₀ t2[ζ].
  Proof.
    induction r; crushUtlc; eauto with eval; unfold not in *. 
    - constructor; destruct t₁; crushUtlc.
    - constructor; destruct t₁; crushUtlc.
    - constructor; destruct t; crushUtlc.
    - constructor; destruct t; crushUtlc.
    - constructor; destruct t; crushUtlc.
  Qed.

  Lemma eval_closed_under_substitution {t1 t2} (r: t1 --> t2) (ζ: Sub UTm) :
    t1[ζ] --> t2[ζ].
  Proof.
    induction r as [C t₁' t₂' e₀|C]; rewrite -> ?pctx_app_sub.
    - assert (t₁'[ζ ↑⋆ depthPCtx C] -->₀ t₂'[ζ ↑⋆ depthPCtx C]); eauto using eval₀_closed_under_substitution with eval. 
    - constructor; induction C; crushUtlc.  
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
  induction C₂; crushUtlc.
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
  induction C; crushUtlc.
Qed.

Lemma values_are_normal {t : UTm} : Value t -> normal t.
Proof.
  intros  vt.
  induction t; simpl in vt; try match goal with [ H : False |- _ ] => destruct H end; try eauto; intro et'; destruct et' as [t' et'];
  depind et'; induction C; crushUtlc;
  repeat try match goal with 
      | [ H : abs _ -->₀ _ |- _] => depind H
      | [ H : unit -->₀ _ |- _] => depind H
      | [ H : true -->₀ _ |- _] => depind H
      | [ H : false -->₀ _ |- _] => depind H
      | [ H : pair _ _ -->₀ _ |- _] => depind H
      | [ H : inl _ -->₀ _ |- _] => depind H
      | [ H : inr _ -->₀ _ |- _] => depind H
      | [ H : pair _ _ = pair _ _ |- _] => inversion H; clear H; subst
      | [ H : inl _ = inl _ |- _] => inversion H; clear H; subst
      | [ H : inr _ = inr _ |- _] => inversion H; clear H; subst
      | [ H : _ ∧ _ |- _] => destruct_conjs
      | [ H : Value (pctx_app wrong _) |- _] => exfalso; refine (ectx_wrong_not_value _ H); auto
  end.
  - apply IHt1; [assumption| exists (pctx_app t' C); eauto with eval].
  - apply IHt2; [assumption| exists (pctx_app t' C); eauto with eval].
  - apply IHt; [assumption| exists (pctx_app t' C); eauto with eval].
  - apply IHt; [assumption| exists (pctx_app t' C); eauto with eval].
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