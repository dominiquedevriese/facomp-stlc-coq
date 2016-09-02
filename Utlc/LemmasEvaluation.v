Require Export Db.Lemmas.
Require Export Utlc.SpecSyntax.
Require Export Utlc.SpecEvaluation.
Require Import Common.Common.
Require Import Common.Relations.

Require Import Omega.

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
     repeat match goal with
                [ |- _ ∧ _ ] => split
              | [ |- evaln ?t ?t 0 ] => eapply stepRel_zero
              | [ H : eval ?t ?t', H' : evaln ?t' ?t'' ?n |- evaln ?t ?t'' (S ?n) ] => refine (stepRel_step eval _ _ _ _ H H')
              | [ |- _ ≤ _ ] => omega
            end;
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

Section CtxEval.
  Lemma eval₀_ctxeval {t t'} : t -->₀ t' → ctxeval t t'.
  Proof.
    apply (mkCtxEval phole _ _ I).
  Qed.

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

  Lemma extend_ctxevalStar {tu tu'} Cu : ECtx Cu → ctxevalStar tu tu' → ctxevalStar (pctx_app tu Cu) (pctx_app tu' Cu).
  Proof.
    intros eCu ce. 
    unfold ctxevalStar.
    induction ce;
    eauto using extend_ctxeval with eval.
  Qed.

  Lemma extend_ctxevalStar' {tu1 tu2 tu1' tu2' Cu} : 
    ctxevalStar tu1 tu2 → 
    tu1' = pctx_app tu1 Cu →
    tu2' = pctx_app tu2 Cu →
    ECtx Cu → ctxevalStar tu1' tu2'.
  Proof.
    intros; subst; eauto using extend_ctxevalStar.
  Qed.
End CtxEval.

Section EvalN.
  Lemma evaln_to_evalStar {t t' n} :
    evaln t t' n → t -->* t'.
  Proof.
    induction 1; crush.
  Qed.

  Lemma evalStar_to_evaln {t t'} :
    t -->* t' → exists n, evaln t t' n.
  Proof.
    induction 1; 
    [exists 0|destruct IHclos_refl_trans_1n as (n & en); exists (S n)];
    crush.
  Qed.

  Lemma evaln_to_evalPlus {t t' n} :
    evaln t t' (S n) → t -->+ t'.
  Proof.
    inversion 1; subst;
      eauto using evalStepStarToPlus, evaln_to_evalStar.
  Qed.

  Lemma ctxevaln_ctx {t t' n} :
    ctxevaln t t' n -> forall C, ECtx C → evaln (pctx_app t C) (pctx_app t' C) n.
  Proof.
    intros ec C eC; unfold evaln.
    induction ec; eauto using ctxeval_eval_ctx with eval.
  Qed.

  Lemma evaln_split {t t' } n n':
    evaln t t' (n + n') → exists t'', evaln t t'' n ∧ evaln t'' t' n'.
  Proof.
    revert t; induction n.
    - intros; exists t; crush.
    - intros t esn; depind esn; clear IHesn.
      destruct (IHn t' esn) as (t3 & es1 & es2).
      exists t3; crush.
  Qed.
End EvalN.

Section Termination.

  Lemma TerminatingI' (t: UTm) (vt: Value t) :
    ∀ t', t --> t' → t'⇓.
  Proof. intros t' r; elim (values_are_normal vt r). Qed.

  Lemma TerminatingIV' (t: UTm) (vt: Value t) :
    ∀ t' n, t --> t' → t'⇓_n.
  Proof. intros t' n r; elim (values_are_normal vt r). Qed.

  Lemma values_terminate (t: UTm) (vt: Value t) :
    t ⇓.
  Proof. exists t; crush. Qed.

  Lemma values_terminateN (t: UTm) (vt: Value t) :
    ∀ n, t ⇓_ n.
  Proof.
    exists t, 0; crush.
  Qed.

  Lemma TerminatingN_Terminating {t : UTm} {n} : t ⇓_ n -> t ⇓.
  Proof. 
    destruct 1 as (v & m & vv & ineq & esm).
    exists v; eauto using evaln_to_evalStar with eval.
  Qed.

  Lemma Terminating_TerminatingN {t : UTm} : t ⇓ -> exists n, t ⇓_ n.
  Proof. 
    destruct 1 as (v & vv & es).
    destruct (evalStar_to_evaln es) as (n & esn).
    exists n; exists v, n; crush.
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

  Lemma TerminatingD (t: UTm) (m: t⇓) :
    ∀ t', t --> t' → Terminating t'.
  Proof. 
    destruct m as (v & vv & es). 
    intros t' e.
    depind es.
    - elim (values_are_normal vv e). 
    - rewrite -> (determinacy e H).
      exists z; crush.
  Qed.

  Lemma TerminatingDN (t: UTm) n (m: t ⇓_ (S n)) :
    ∀ t' : UTm, t --> t' → t'⇓_n.
  Proof. 
    destruct m as (v & m & vv & ineq & es). 
    intros t' e.
    depind es.
    - elim (values_are_normal vv e). 
    - rewrite -> (determinacy e H).
      assert (n0 ≤ n) by omega.
      exists t'', n0; crush.
  Qed.

  Lemma termination_closed_under_antireduction {t t'} :
    t --> t' → t' ⇓ → t ⇓.
  Proof.
    destruct 2 as (v & vv & es).
    exists v; eauto with eval.
  Qed.

  Lemma termination_closed_under_antireductionStar {t t'} :
    t -->* t' → t' ⇓ → t ⇓.
  Proof.
    intros e term.
    induction e; eauto using termination_closed_under_antireduction.
  Qed.

  Lemma TerminatingN_eval {t t' n } :
    t --> t' → t' ⇓_ n ↔ t ⇓_ (S n).
  Proof.
    intros e. constructor; 
      destruct 1 as (v & m & vv & ineq & esm).
    - exists v, (S m); crush.
    - destruct esm.
      + elim (values_are_normal vv e).
      + rewrite -> (determinacy e H).
        exists t'', n0; crush.
  Qed.

  Lemma TerminatingN_evaln {t t' n } n' :
    evaln t t' n → t' ⇓_ n' ↔ t ⇓_ (n + n').
  Proof.
    induction 1; eauto using iff_refl, iff_trans, TerminatingN_eval. 
  Qed.

  Lemma TerminatingN_xor_evaln {t t' n} :
    TerminatingN t n → evaln t t' (S n) → False.
  Proof.
    intros term essn.
    replace (S n) with (n + 1) in essn by omega.
    destruct (evaln_split n 1 essn) as (t'' & esn & es1).
    replace n with (n + 0) in term by omega.
    rewrite <- (TerminatingN_evaln 0 esn) in term.
    destruct term as (v & m & vv & ineq & es0).
    assert (m = 0) by omega; subst.
    inversion es0; subst. 
    depind es1.
    elim (values_are_normal vv H).
  Qed.


  Lemma TerminatingN_lt {t n n'} :
    TerminatingN t n → n ≤ n' → TerminatingN t n'.
  Proof.
    destruct 1 as (v & m & vv & ineq & esm).
    intros ineq'.
    exists v, m; crush.
  Qed.

End Termination'.

Section EvalInContext.
  Lemma eval_from_eval₀ {t t' t₀ t₀' C} :
    t₀ -->₀ t₀' →
    t = pctx_app t₀ C →
    t' = pctx_app t₀' C →
    ECtx C →
    t --> t'.
  Proof.
    intros; subst; eauto using eval_ctx₀.
  Qed.

  Lemma ctxeval_from_eval₀ {t t' t₀ t₀' C} :
    t₀ -->₀ t₀' →
    t = pctx_app t₀ C →
    t' = pctx_app t₀' C →
    ECtx C →
    ctxeval t t'.
  Proof.
    intros; subst; eauto using ctxeval.
  Qed.

End EvalInContext.

Ltac crushUtlcEvaluationMatchH2 :=
  match goal with
    | [ |- ECtx (pctx_cat _ _)] => eapply ectx_cat
  end.

Ltac inferContext :=
  simpl; try reflexivity;
  let rec inferC acc t t₀ :=
      match t with
        | t₀ => instantiate (1 := acc)
        | app ?t1 ?t2 => inferC (pctx_cat (papp₁ phole t2) acc) t1 t₀ + inferC (pctx_cat (papp₂ t1 phole) acc) t2 t₀
        | pair ?t1 ?t2 => inferC (pctx_cat (ppair₁ phole t2) acc) t1 t₀ + inferC (pctx_cat (ppair₂ t1 phole) acc) t2 t₀
        | seq ?t1 ?t2 => inferC (pctx_cat (pseq₁ phole t2) acc) t1 t₀
        | inl ?t1 => inferC (pctx_cat (pinl phole) acc) t1 t₀
        | inr ?t1 => inferC (pctx_cat (pinl phole) acc) t1 t₀
        | inr ?t1 => inferC (pctx_cat (pinl phole) acc) t1 t₀
        | ite ?t1 ?t2 ?t3 => inferC (pctx_cat (pite₁ phole t2 t3) acc) t1 t₀
        | caseof ?t1 ?t2 ?t3 => inferC (pctx_cat (pcaseof₁ phole t2 t3) acc) t1 t₀
        | proj₁ ?t1 => inferC (pctx_cat (pproj₁ phole) acc) t1 t₀
        | proj₂ ?t1 => inferC (pctx_cat (pproj₂ phole) acc) t1 t₀
        | pctx_app ?t1 (pctx_cat ?C1 ?C2) => inferC (pctx_app (pctx_app t1 C1) C2) t₀
        | pctx_app ?t1 ?C => inferC (pctx_cat C acc) t1 t₀
      end
  in repeat match goal with
              | [ |- ?t = pctx_app ?t₀ (pctx_cat ?C1 ?C2) ] => (rewrite -> ?pctx_cat_app)
              | [ |- pctx_app ?t0 ?C = pctx_app ?t' ?C ] => f_equal
              | [ |- ?t = pctx_app ?t₀ ?C ] => (inferC phole t t₀; rewrite -> ?pctx_cat_app; simpl; rewrite -> ?pctx_cat_app in *; reflexivity)
            end.
  
Lemma test_inferContext (t : UTm) (C' : PCtx): True.
Proof.
  assert (pctx_app (pair (inl t) unit) C' = pctx_app t (pctx_cat (ppair₁ (pinl phole) unit) C')).
  inferContext.
  trivial.
Qed.