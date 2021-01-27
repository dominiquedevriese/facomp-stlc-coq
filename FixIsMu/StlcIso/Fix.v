Require Import StlcIso.SpecSyntax.
Require Import StlcIso.SpecEvaluation.
Require Import StlcIso.LemmasEvaluation.
Require Import StlcIso.SpecTyping.
Require Import StlcIso.LemmasTyping.
(* Require Import StlcIso.SpecScoping. *)
(* Require Import StlcIso.LemmasScoping. *)
Require Import StlcIso.Inst.
Require Import Db.Lemmas.
Require Import Db.WellScoping.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasRewriteH;
     rewrite <- ?ap_liftSub, <- ?up_liftSub
     (* repeat crushStlcIsoScopingMatchH; *)
     (* repeat crushScopingMatchH *)
    );
  auto.

Definition ufix₁ (f : Tm) (τ1 τ2 : Ty) : Tm :=
  let t : Tm := abs (trec (tarr (tvar 0) (tarr τ1 τ2)[wkm])) (app f[wkm] (abs τ1 (app (app (unfold_ (var 1)) (var 1)) (var 0))))
  in app t (fold_ t).

Definition ufix (τ1 τ2 : Ty) : Tm :=
  abs (tarr (tarr τ1 τ2) (tarr τ1 τ2)) (ufix₁ (var 0) τ1 τ2).

Lemma ufix_eval₁' f (valf: Value f) {τ1 τ2} : ctxeval (app (ufix τ1 τ2) f) (ufix₁ f τ1 τ2).
Proof.
  unfold ufix, ufix₁.
  apply (mkCtxEval phole); crush; eapply eval_beta''; crush.
Qed.

Lemma ufix_eval₁ f (valf: Value f) {τ1 τ2} : app (ufix τ1 τ2) f  --> ufix₁ f τ1 τ2.
Proof.
  eauto using ufix_eval₁', ctxeval_eval.
Qed.

Lemma ufix₁_evaln' {t τ1 τ2} : ctxevaln (ufix₁ (abs (tarr τ1 τ2) t) τ1 τ2) (t[beta1 (abs τ1 (app (ufix₁ (abs (tarr τ1 τ2) t[wkm↑]) τ1 τ2) (var 0)))]) 2.
Proof.
  (* cut (ctxeval (ufix₁ (abs (tarr τ1 τ2) t) τ1 τ2) (app (abs τ1 t) (abs (tarr (tarr τ1 τ2) (tarr τ1 τ2)) (app (ufix₁ (abs t[wkm↑])) (var 0)))) /\ ctxeval (app (abs t) (abs (tarr (tarr τ1 τ2) (tarr τ1 τ2)) (app (ufix₁ (abs t[wkm↑])) (var 0)))) (t[beta1 (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))])). *)
  (* cut (ctxeval (ufix₁ (abs (tarr τ1 τ2) t) τ1 τ2) (app (abs τ1 t) (abs (tarr (tarr τ1 τ2) (tarr τ1 τ2)) (app (ufix₁ (abs t[wkm↑])) (var 0)))) /\ ctxeval (app (abs t) (abs (tarr (tarr τ1 τ2) (tarr τ1 τ2)) (app (ufix₁ (abs t[wkm↑])) (var 0)))) (t[beta1 (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))])). *)
Admitted.
  (* cut (ctxeval (ufix₁ (abs (tarr τ1 τ2) t) τ1 τ2) (app (abs τ1 t) (abs (tarr (tarr τ1 τ2) (tarr τ1 τ2)) (app (ufix₁ (abs t[wkm↑])) (var 0)))) /\ ctxeval (app (abs t) (abs (tarr (tarr τ1 τ2) (tarr τ1 τ2)) (app (ufix₁ (abs t[wkm↑])) (var 0)))) (t[beta1 (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))])). *)

  (* cut (ctxeval (ufix₁ (abs τ1 t) τ1 τ2) (app (abs τ1 t) (abs τ1 (app (ufix₁ (abs τ1 t[wkm↑]) τ1 τ2) (var 0)))) /\ *)
(*        ctxeval (app (abs τ1 t) (abs τ1 (app (ufix₁ (abs τ1 t[wkm↑]) τ1 τ2) (var 0)))) (t[beta1 (abs τ1 (app (ufix₁ (abs τ1 t[wkm↑]) τ1 τ2) (var 0)))])). *)
(* (*   - destruct 1. unfold ctxevaln; eauto with eval. *) *)
(*   - split. *)
(*     + unfold ufix₁. *)
(*       apply (mkCtxEval phole); crush. *)
(*       apply eval_beta''; crush. *)
(*     + apply (mkCtxEval phole); crush. *)
(*       apply eval_beta; crush. *)
(* Qed. *)

Lemma foo {Γ t τ τ'} :
  τ[beta1 (trec τ)] = τ' →
  ⟪ Γ i⊢ t : trec τ ⟫ →
  ⟪ Γ i⊢ unfold_ t : τ' ⟫.
Proof.
  intros. subst.
  constructor. assumption.
Qed.

Lemma ufix₁_typing {t τ₁ τ₂ Γ} :
  ⟪ Γ i⊢ t : tarr (tarr τ₁ τ₂) (tarr τ₁ τ₂) ⟫ →
  ⟪ Γ i⊢ ufix₁ t τ₁ τ₂ : tarr τ₁ τ₂ ⟫.
Proof.
  intros.
  unfold ufix₁.
  apply (@WtApp Γ _ _ (trec (tarr (tvar 0) (tarr τ₁ τ₂)[wkm])) (tarr τ₁ τ₂)).
  - apply (@WtAbs Γ _ _ (tarr τ₁ τ₂)).
    crushTyping.
    eapply foo.
    2: {
      constructor.
      constructor.
      constructor.
    }
    cbn.
    f_equal.
    f_equal.
    crushStlcSyntaxMatchH.
    apply apply_wkm_beta1_cancel.
    crushStlcSyntaxMatchH.
    apply apply_wkm_beta1_cancel.
  - constructor.
    cbn.
    constructor.
    repeat crushStlcSyntaxMatchH.
    rewrite ?apply_wkm_beta1_cancel.
    econstructor.
    eapply typing_sub.
    eassumption.
    auto with ws.
    constructor.
    repeat econstructor.
    crushTyping.
    eapply foo.
    2: {
      constructor.
      constructor.
      constructor.
    }
    cbn.
    f_equal.
    f_equal.
    crushStlcSyntaxMatchH.
    apply apply_wkm_beta1_cancel.
    crushStlcSyntaxMatchH.
    apply apply_wkm_beta1_cancel.
Qed.

Lemma ufix_typing {τ₁ τ₂ Γ} :
  ⟪ Γ i⊢ ufix τ₁ τ₂ : tarr (tarr (tarr τ₁ τ₂) (tarr τ₁ τ₂)) (tarr τ₁ τ₂) ⟫.
Proof.
  constructor.
  apply ufix₁_typing.
  crushTyping.
Qed.

(* Lemma ufix₁_evaln {t} : evaln (ufix₁ (abs t)) (t[beta1 (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))]) 2. *)
(* Proof. *)
(*   eauto using ufix₁_evaln', ctxevaln_evaln. *)
(* Qed. *)

(* Lemma ufix₁_eval {t} : ufix₁ (abs t) -->+ t[beta1 (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))]. *)
(* Proof. *)
(*   refine (evaln_to_evalPlus _). *)
(*   apply ufix₁_evaln. *)
(* Qed. *)

(* Lemma ufix_ws (γ : Dom) : *)
(*   ⟨ γ ⊢ ufix ⟩. *)
(* Proof. *)
(*   unfold ufix, ufix₁. *)
(*   crush. *)
(* Qed. *)

(* (* TODO: simplify using result about scoping under subst... *) *)
(* Lemma ufix₁_ws {γ t} : *)
(*   ⟨ γ ⊢ t ⟩ → ⟨ γ ⊢ ufix₁ t ⟩. *)
(* Proof. *)
(*   unfold ufix₁. *)
(*   crush. *)
(* Qed. *)

