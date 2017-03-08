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

Lemma eval₀_to_eval {t t'} : t -->₀ t' → t --> t'.
Proof.
  intros.
  eapply (eval_ctx₀ phole); crush.
Qed.

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
    pctx_cat C₁ (pctx_cat C₂ C₃) = pctx_cat (pctx_cat C₁ C₂) C₃.
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

  Lemma value_ectx_inv {C} (eC: ECtx C) :
    ∀ t, Value (pctx_app t C) → Value t.
  Proof. induction C; cbn in *; intuition. Qed.

  Lemma ectx_wrong_not_value {C} : ECtx C -> ¬ (Value (pctx_app wrong C)).
  Proof.
    intros ec val.
    apply value_ectx_inv in val; crush.
  Qed.

  Lemma values_are_eval₀_normal {t t'} :
    Value t → t -->₀ t' → False.
  Proof. inversion 2; crush. Qed.

  Lemma values_are_normal {t : UTm} : Value t → normal t.
  Proof.
    intros vt; induction 1 as [? ? ? r'|?];
      apply value_ectx_inv in vt;
      eauto using values_are_eval₀_normal.
  Qed.
  Global Arguments values_are_normal {_} _ {_} _.

  Lemma wrong_normal : normal wrong.
  Proof.
    intros t' e.
    depind e.
    - destruct C; crush.
      inversion H.
    - destruct C; crush.
  Qed.

  Corollary wrong_evalStar_inv {t} : wrong -->* t → t = wrong.
  Proof.
    intros es. depind es; crush.
    exfalso; eapply wrong_normal; crush.
  Qed.
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
    induction 1; econstructor; eauto using ctxeval_eval with eval.
  Qed.

  (* The following implication is actually an equivalence, but we don't need that. *)
  Lemma ctxeval_eval_ctx {t t'} : ctxeval t t' → forall Cu, ECtx Cu → pctx_app t Cu --> pctx_app t' Cu.
  Proof.
    destruct 1; intros; rewrite <- ?pctx_cat_app; eauto using ectx_cat with eval.
  Qed.

  Lemma ctxevaln_evaln_ctx {t t' n} : ctxevaln t t' n → forall Cu, ECtx Cu → evaln (pctx_app t Cu) (pctx_app t' Cu) n.
  Proof.
    induction 1; unfold evaln in *;
    econstructor; eauto using ctxeval_eval_ctx with eval.
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
        apply (value_ectx_inv E) in V; cbn in V
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

  Lemma determinacy_star {t t₁ t₂} :
    t -->* t₁ → t -->* t₂ → (t₁ -->* t₂ ∨ t₂ -->* t₁).
  Proof.
    intros es1 es2.
    pose proof es1 as es1'.
    induction es1; auto.
    destruct es2; auto.
    rewrite (determinacy H H0) in *.
    crush.
  Qed.
End Determinacy.

Section InvertECtxEq.

  Inductive EctxAppEq : ∀ (t : UTm) (C : PCtx) (t' : UTm) (C' : PCtx),  Prop :=
    | EctxAppEqLeft : ∀ t C C', ECtx C → EctxAppEq (pctx_app t C) C' t (pctx_cat C C')
    | EctxAppEqRight : ∀ t C C', ECtx C → EctxAppEq t (pctx_cat C C') (pctx_app t C) C'
    | ECtxValueLeft : ∀ t t' C C', Value t → EctxAppEq t C t' C'
    | ECtxValueRight : ∀ t t' C C', Value t' → EctxAppEq t C t' C'
  .

  Lemma ectxAppEqExtend {t C t' C'} C'' :
    EctxAppEq t C t' C' →
    EctxAppEq t (pctx_cat C C'') t' (pctx_cat C' C'').
  Proof.
    induction 1; rewrite <- ?pctx_cat_assoc; constructor; assumption.
  Qed.

  Lemma ectxAppEqExtendPAbs {t C t' C'} :
    EctxAppEq t C t' C' →
    EctxAppEq t (pabs C) t' (pabs C').
  Proof.
    eapply (ectxAppEqExtend (pabs phole)).
  Qed.

  Lemma ectxAppEqExtendPInl {t C t' C'} :
    EctxAppEq t C t' C' →
    EctxAppEq t (pinl C) t' (pinl C').
  Proof.
    eapply (ectxAppEqExtend (pinl phole)).
  Qed.

  Lemma ectxAppEqExtendPInr {t C t' C'} :
    EctxAppEq t C t' C' →
    EctxAppEq t (pinr C) t' (pinr C').
  Proof.
    eapply (ectxAppEqExtend (pinr phole)).
  Qed.

  Lemma ectxAppEqExtendPProj₁ {t C t' C'} :
    EctxAppEq t C t' C' →
    EctxAppEq t (pproj₁ C) t' (pproj₁ C').
  Proof.
    eapply (ectxAppEqExtend (pproj₁ phole)).
  Qed.

  Lemma ectxAppEqExtendPProj₂ {t C t' C'} :
    EctxAppEq t C t' C' →
    EctxAppEq t (pproj₂ C) t' (pproj₂ C').
  Proof.
    eapply (ectxAppEqExtend (pproj₂ phole)).
  Qed.

  Lemma ectxAppEqExtendPPair₁ {t C t' C' t₂} :
    EctxAppEq t C t' C' →
    EctxAppEq t (ppair₁ C t₂) t' (ppair₁ C' t₂).
  Proof.
    eapply (ectxAppEqExtend (ppair₁ phole t₂)).
  Qed.

  Lemma ectxAppEqExtendPPair₂ {t C t' C' t₁} :
    EctxAppEq t C t' C' →
    EctxAppEq t (ppair₂ t₁ C) t' (ppair₂ t₁ C').
  Proof.
    eapply (ectxAppEqExtend (ppair₂ t₁ phole)).
  Qed.

  Lemma ectxAppEqExtendPApp₁ {t C t' C' t₂} :
    EctxAppEq t C t' C' →
    EctxAppEq t (papp₁ C t₂) t' (papp₁ C' t₂).
  Proof.
    eapply (ectxAppEqExtend (papp₁ phole t₂)).
  Qed.

  Lemma ectxAppEqExtendPApp₂ {t C t' C' t₁} :
    EctxAppEq t C t' C' →
    EctxAppEq t (papp₂ t₁ C) t' (papp₂ t₁ C').
  Proof.
    eapply (ectxAppEqExtend (papp₂ t₁ phole)).
  Qed.

  Lemma ectxAppEqExtendPSeq₁ {t C t' C' t₂} :
    EctxAppEq t C t' C' →
    EctxAppEq t (pseq₁ C t₂) t' (pseq₁ C' t₂).
  Proof.
    eapply (ectxAppEqExtend (pseq₁ phole t₂)).
  Qed.

  Lemma ectxAppEqExtendPIte₁ {t C t' C' t₂ t₃} :
    EctxAppEq t C t' C' →
    EctxAppEq t (pite₁ C t₂ t₃) t' (pite₁ C' t₂ t₃).
  Proof.
    eapply (ectxAppEqExtend (pite₁ phole t₂ t₃)).
  Qed.

  Lemma ectxAppEqExtendPCaseof₁ {t C t' C' t₂ t₃} :
    EctxAppEq t C t' C' →
    EctxAppEq t (pcaseof₁ C t₂ t₃) t' (pcaseof₁ C' t₂ t₃).
  Proof.
    eapply (ectxAppEqExtend (pcaseof₁ phole t₂ t₃)).
  Qed.

  Lemma ectxAppEqPHoleRight {t C} : ECtx C → EctxAppEq t C (pctx_app t C) phole.
  Proof.
    change C with (pctx_cat C phole); eauto using EctxAppEq.
  Qed.

  Lemma ectxAppEqPHoleLeft {t C} : ECtx C → EctxAppEq (pctx_app t C) phole t C.
  Proof.
    change C with (pctx_cat C phole); eauto using EctxAppEq.
  Qed.

  Lemma pctx_app_eq t C t' C' :
    ECtx C → ECtx C' →
    pctx_app t C = pctx_app t' C' →
    EctxAppEq t C t' C'.
  Proof.
    revert t' C';
    induction C; intros t' C' eC eC' eq'; 
    [simpl in *; subst;
     eauto using ectxAppEqPHoleLeft, ectxAppEqPHoleRight, EctxAppEq
    |idtac..];
    (destruct C';
      [change (pctx_app t' phole) with t' in *; subst; 
       eauto using ectxAppEqPHoleLeft, ectxAppEqPHoleRight, EctxAppEq
      |idtac..]);
    crush;
    eauto using ectxAppEqExtendPAbs, ectxAppEqExtendPProj₂, ectxAppEqExtendPProj₁, ectxAppEqExtendPInr, ectxAppEqExtendPInl, ectxAppEqExtendPApp₁, ectxAppEqExtendPApp₂, ectxAppEqExtendPPair₁, ectxAppEqExtendPPair₂, ectxAppEqExtendPIte₁, ectxAppEqExtendPCaseof₁, ectxAppEqExtendPSeq₁;
    eauto using value_ectx_inv, ECtxValueRight, ECtxValueLeft.
  Qed.
End InvertECtxEq.

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

  Lemma Terminating_not_div_wrong {t} : 
    t ⇓ → (t ⇑ ∨ t -->* wrong) → False.
  Proof.
    intros term.
    destruct 1 as [div | termwrong]; auto.
    destruct term as (? & ? & ?).
    destruct (determinacy_star H0 termwrong).
    - depind H1; try contradiction.
      eapply (values_are_normal H H1).
    - depind H1; try contradiction.
      eapply (wrong_normal _ H1).
  Qed.    

  Lemma wrong_pctx_inv {C t} :
    pctx_app t C = wrong → t = wrong ∧ C = phole.
  Proof.
    induction C; crush.
  Qed.

  Lemma eval₀_ectx_inv C t (ec : ECtx C) {t' t''} :
    t'' -->₀ t' → t'' = pctx_app t C →
    Value t ∨ C = phole.
  Proof.
    induction 1;
    destruct C; crush; 
    try match goal with
            [ H : _ = pctx_app t C |- _ ] => 
            (assert (Value (pctx_app t C)) by (rewrite <- H; crush))
        end; eauto using value_ectx_inv.
  Qed. 

  Lemma eval_ectx_inv C t (ec : ECtx C) {t' t''} :
    t'' --> t' → pctx_app t C = t'' →
    Value t ∨
    (exists C', ECtx C' ∧ t = pctx_app wrong C' ∧ t' = wrong) ∨
    (exists t'', t' = pctx_app t'' C ∧ t --> t'').
  Proof.
    induction 1 as [C' t₀ t₀' e eC'|].
    - intros eq.
      pose proof (pctx_app_eq _ _ _ _ ec eC' eq) as inv.
      induction inv as [t C C' eC| t C C' eC| t t' C C' vt| t t' C C' vt'].
      + right; right.
        exists (pctx_app t₀' C);
        eauto using pctx_cat_app, eval_ctx₀.
      + destruct (eval₀_ectx_inv C t eC e eq_refl); crush;
        right; right.
        exists t₀';
        rewrite pctx_cat_phole_leftzero;
        split; crush.
        eapply (eval_ctx₀ phole); crush.
      + left; crush.
      + exfalso.
        eapply (values_are_normal vt');
        eapply (eval_ctx₀ phole); crush.
    - intros eq.
      pose proof (pctx_app_eq _ _ _ _ ec H eq) as inv.
      depind inv.
      + right; left.
        exists C; crush.
      + destruct (wrong_pctx_inv x); subst.
        right; left.
        exists phole; crush.
      + left; crush.
      + exfalso; crush.
  Qed.

  Lemma evalStar_ectx_inv C t (ec : ECtx C) v :
    pctx_app t C -->* v → Value v →
    (exists v', Value v' ∧ t -->* v' ∧ pctx_app v' C -->* v).
  Proof.
    intros es vv; depind es.
    - exists t; eauto using value_ectx_inv with eval.
    - destruct (eval_ectx_inv C t ec H eq_refl) as [vt|[[C' [eC' [? ?]]]|[t'' [eq e]]]]; subst.
      + exists t; crush.
      + rewrite -> (wrong_evalStar_inv es) in *.
        crush.
      + destruct (IHes t'' C ec eq_refl vv) as (v' & vv' & es1' & es2').
        exists v'; crush.
  Qed.
 
  Lemma inversion_termination_evalcontext C t (ec: ECtx C) :
    (pctx_app t C) ⇓ → t ⇓.
  Proof.
    destruct 1 as (v & vv & es).
    destruct (evalStar_ectx_inv C t ec v es) as (v' & vv' & es1 & es2); subst; crush.
    exists v'; crush.
  Qed.

  Corollary div_ectx {t C} :
    ECtx C → t ⇑ → (pctx_app t C) ⇑.
  Proof. eauto using inversion_termination_evalcontext. Qed.

  Lemma pctx_cat_phole {C C'} : C ≠ phole → pctx_cat C C' ≠ phole.
  Proof.
    induction C'; simpl; crush.
  Qed.

  Lemma eval_to_wrong_ectx {t C} (eC : ECtx C):
    t -->* wrong → (pctx_app t C) -->* wrong.
  Proof.
    intros es.
    depind es.
    - assert (phole_or_not : C = phole ∨ C ≠ phole)
        by (destruct C; [left|right..]; crush).
      destruct (phole_or_not); subst.
      + simpl; crush.
      + eapply evalToStar.
        eauto with eval.
    - induction H.
      + refine (evalStepStar _ _ (IHes _)); trivial.
        rewrite <- ?pctx_cat_app.
        eauto using ectx_cat with eval.
      + rewrite <- ?pctx_cat_app.
        eapply evalToStar.
        eauto using pctx_cat_phole, ectx_cat with eval.
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
    | [ |- ECtx phole ] => cbn
    | [ |- ECtx (pite₁ _ _ _) ] => cbn
    | [ |- ECtx (pinl _) ] => cbn
    | [ |- ECtx (pinr _) ] => cbn
    | [ |- ECtx (pproj₁ _) ] => cbn
    | [ |- ECtx (pproj₂ _) ] => cbn
    | [ |- ECtx (papp₁ _ _) ] => cbn
    | [ |- ECtx (papp₂ _ _) ] => cbn
    | [ |- ECtx (pcaseof₁ _ _ _) ] => (unfold ECtx; cbn)
  end.

Ltac inferContext :=
  cbn; try reflexivity;
  let rec inferC acc t t₀ :=
      match t with
        | t₀ => instantiate (1 := acc)
        | app ?t1 ?t2 => inferC (pctx_cat (papp₁ phole t2) acc) t1 t₀ + inferC (pctx_cat (papp₂ t1 phole) acc) t2 t₀
        | pair ?t1 ?t2 => inferC (pctx_cat (ppair₁ phole t2) acc) t1 t₀ + inferC (pctx_cat (ppair₂ t1 phole) acc) t2 t₀
        | seq ?t1 ?t2 => inferC (pctx_cat (pseq₁ phole t2) acc) t1 t₀
        | inl ?t1 => inferC (pctx_cat (pinl phole) acc) t1 t₀
        | inr ?t1 => inferC (pctx_cat (pinr phole) acc) t1 t₀
        | ite ?t1 ?t2 ?t3 => inferC (pctx_cat (pite₁ phole t2 t3) acc) t1 t₀
        | caseof ?t1 ?t2 ?t3 => inferC (pctx_cat (pcaseof₁ phole t2 t3) acc) t1 t₀
        | proj₁ ?t1 => inferC (pctx_cat (pproj₁ phole) acc) t1 t₀
        | proj₂ ?t1 => inferC (pctx_cat (pproj₂ phole) acc) t1 t₀
        | pctx_app t₀ ?C => instantiate (1 := pctx_cat C acc)
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