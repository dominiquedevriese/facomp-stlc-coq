Require Export Db.Lemmas.
Require Export Stlc.SpecSyntax.
Require Export Stlc.SpecEvaluation.
Require Export Coq.Program.Tactics.
Require Import Common.Common.
Require Import Common.Relations.

Require Import Omega.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     subst*);
  try discriminate;
  eauto with eval.

(* ** Evaluation contexts *)
Lemma ectx_cat (C₁ C₂: PCtx) :
  ECtx C₁ → ECtx C₂ → ECtx (pctx_cat C₁ C₂).
Proof.
  induction C₂; simpl; intros; destruct_conjs; auto.
Qed.

Lemma pctx_cat_app (t : Tm) (C₁ C₂ : PCtx) :
  pctx_app t (pctx_cat C₁ C₂) = pctx_app (pctx_app t C₁) C₂.
Proof.
  induction C₂; crush.
Qed.

Lemma eval_ctx C t t' (eC : ECtx C) :
  t --> t' -> pctx_app t C --> pctx_app t' C.
Proof.
  induction 1.
  rewrite <- ?pctx_cat_app in *.
  eauto using ectx_cat with eval.
Qed.

Lemma evalstar_ctx C t t' (eC: ECtx C) :
  t -->* t' → pctx_app t C -->* pctx_app t' C.
Proof. 
  induction 1; eauto using eval_ctx with eval.
Qed.

Lemma evalplus_ctx C t t' (eC: ECtx C) :
  t -->+ t' → pctx_app t C -->+ pctx_app t' C.
Proof. 
  induction 1; eauto using eval_ctx with eval.
Qed.

Lemma evaln_ctx {C t t' n} :
  ECtx C → evaln t t' n -> evaln (pctx_app t C) (pctx_app t' C) n.
Proof.
  intros ec.
  induction 1; eauto using eval_ctx with eval.
Qed.

Lemma inversion_termination_evalcontext C t (ec: ECtx C) :
  Terminating (pctx_app t C) → Terminating t.
Proof.
  intro term; depind term.
  constructor.
  eauto using eval_ctx.
Qed.

Lemma termination_closed_under_evalplus {t t'} :
  t -->+ t' → t⇓ → t'⇓.
Proof. intros e m; induction e; inversion m; auto. Qed.

Lemma termination_closed_under_evalstar {t t'} :
  t -->* t' → t⇓ → t'⇓.
Proof.
  intros e; destruct (inversion_evalStar e); subst;
    eauto using termination_closed_under_evalplus.
Qed.

Corollary divergence_closed_under_eval {t t'} :
  t --> t' → t'⇑ → t⇑.
Proof. eauto using TerminatingD with eval. Qed.

Corollary divergence_closed_under_evalplus {t t'} :
  t -->+ t' → t'⇑ → t⇑.
Proof. eauto using termination_closed_under_evalplus. Qed.

Corollary divergence_closed_under_evalstar {t t'} :
  t -->* t' → t'⇑ → t⇑.
Proof. eauto using termination_closed_under_evalstar. Qed.

Corollary divergence_closed_under_evalcontex t :
  t⇑ → ∀ p, ECtx p → (pctx_app t p)⇑.
Proof. eauto using inversion_termination_evalcontext. Qed.

(* Stronger induction principle *)
Lemma Terminating_ind' (P: Tm → Prop)
 (step: ∀ t,
   (∀ t', t -->+ t' → t'⇓) →
   (∀ t', t -->+ t' → P t') → P t) :
  ∀ t, t⇓ → P t.
Proof.
  pose proof @termination_closed_under_evalplus.
  intros t m.
  apply step; eauto.
  induction m; inversion 1; eauto.
Qed.

Lemma cycles_dont_terminate {t} :
  t -->+ t → t⇑.
Proof. induction 2 using Terminating_ind'; eauto. Qed.

Definition normal' (t : Tm) := ∀ t', ¬ (t --> t').
Lemma values_are_normal' {t : Tm} : Value t -> normal' t.
Proof. induction 2 using eval_ind'; crush. Qed.

Lemma values_are_normal {t : Tm} : Value t -> normal t.
Proof.
  generalize @values_are_normal'.
  unfold normal, normal', not.
  intros ? ? (); eauto.
Qed.

Ltac crushImpossibleEvals :=
  match goal with
          [ H : abs _ _ --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H); crush
        | [ H : true --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H); crush
        | [ H : false --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H); crush
        | [ H : unit --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H); crush
        | [ H : Value ?x, H' : ?x --> _ |- _ ] => exfalso; refine (values_are_normal' H _ H'); crush
        | [ Hx : Value ?x, Hy : Value ?y,  H' : pair ?x ?y --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H'); crush
        | [ Hx : Value ?x,  H' : inl ?x --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H'); crush
        | [ Hx : Value ?x,  H' : inr ?x --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H'); crush
  end.

Lemma TerminatingDN (t: Tm) n (m: t ⇓_ (S n)) :
  ∀ t', t --> t' → TerminatingN t' n.
Proof. 
  depind m; intros t' e'; eauto using values_are_normal.
  exfalso.
  refine (values_are_normal H _); exists t'; auto.
Qed.


Lemma TerminatingN_Terminating {t : Tm} {n} : t ⇓_ n -> t ⇓.
Proof.
  induction 1; constructor; try assumption.
  intros t' e'. exfalso. refine (values_are_normal H _).
  exists t'. auto.
Qed.

Lemma determinacy' {t t' t'' t'''} : t --> t' → t'' --> t''' → t = t'' → t' = t'''.
Proof.
  intros e₁.
  revert t'' t'''. 
  induction e₁ using eval_ind';
  induction 1 using eval_ind'; crush; try crushImpossibleEvals.
Qed.

Lemma determinacy {t t' t''} : t --> t' → t --> t'' → t' = t''.
Proof.
  eauto using determinacy'.
Qed.

Lemma termination_closed_under_antireduction {t t'} :
  t --> t' → t'⇓ → t⇓.
Proof.
  intros e m. constructor. intros t'' e'.
  rewrite <- (determinacy e e').
  assumption.
Qed.

Lemma termination_closed_under_antireductionStar {t t'} :
  t -->* t' → t'⇓ → t⇓.
Proof.
  intros e m. induction e. 
  - assumption.
  - eauto using termination_closed_under_antireduction.
Qed.

Lemma evaln_to_evalStar {t t' n} : evaln t t' n → t -->* t'.
Proof.
  induction 1; crush.
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

Lemma TerminatingN_eval {t t' n} :
  t --> t' → TerminatingN t' n ↔ TerminatingN t (S n).
Proof.
  intros e.
  constructor; intros term.
  - apply TerminatingIS.
    intros t'' e'.
    rewrite <- (determinacy e e').
    assumption.
  - depind term; try crushImpossibleEvals;
    eauto.
Qed.
    
Lemma TerminatingN_evaln {t t' n } n' :
  evaln t t' n → TerminatingN t' n' ↔ TerminatingN t (n + n').
Proof.
  induction 1; constructor; auto; intro term;
  change (S n + n') with (S (n + n')) in *;
  [rewrite <- (TerminatingN_eval H) | rewrite <- (TerminatingN_eval H) in term];
  apply IHevaln; auto.
Qed.

(* This should not hold. *)
Lemma terminatingn_app_unit_unit :
  TerminatingN (app unit unit) 1.
Proof.
  constructor 2; intros; exfalso.
  cut (∀ t t', t --> t' → t = app unit unit → False); eauto.
  clear.
  induction 1 using eval_ind'; crush;
    apply (@values_are_normal unit); crush.
Qed.

(* This should hold, but doesn't. *)
Lemma terminatingN_value {t n} :
  TerminatingN t n → ∃ v, t -->* v ∧ Value v.
Abort.

