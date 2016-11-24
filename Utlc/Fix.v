Require Import Utlc.SpecSyntax.
Require Import Utlc.SpecEvaluation.
Require Import Utlc.LemmasEvaluation.
Require Import Utlc.SpecScoping.
Require Import Utlc.LemmasScoping.
Require Import Utlc.Inst.
Require Import Db.Lemmas.
Require Import Db.WellScoping.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushUtlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasRewriteH;
     rewrite <- ?ap_liftSub, <- ?up_liftSub;
     repeat crushUtlcScopingMatchH;
     repeat crushScopingMatchH
    );
  auto.

Definition ufix₁ (f : UTm) : UTm :=
  let t : UTm := abs (app f[wkm] (abs (app (app (var 1) (var 1)) (var 0))))
  in app t t.

Definition ufix : UTm :=
  abs (ufix₁ (var 0)).

Lemma ufix_eval₁' f (valf: Value f) : ctxeval (app ufix f) (ufix₁ f).
Proof.
  unfold ufix, ufix₁.
  apply (mkCtxEval phole); crush; eapply eval_beta''; crush.
Qed.

Lemma ufix_eval₁ f (valf: Value f) : app ufix f --> ufix₁ f.
Proof.
  eauto using ufix_eval₁', ctxeval_eval.
Qed.

Lemma ufix₁_evaln' {t}  : ctxevaln (ufix₁ (abs t)) (t[beta1 (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))]) 2.
Proof.
  cut (ctxeval (ufix₁ (abs t)) (app (abs t) (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))) /\
       ctxeval (app (abs t) (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))) (t[beta1 (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))])).
  - destruct 1. unfold ctxevaln; eauto with eval.
  - split.
    + unfold ufix₁.
      apply (mkCtxEval phole); crush.
      apply eval_beta''; crush.
    + apply (mkCtxEval phole); crush.
      apply eval_beta; crush.
Qed.

Lemma ufix₁_evaln {t} : evaln (ufix₁ (abs t)) (t[beta1 (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))]) 2.
Proof.
  eauto using ufix₁_evaln', ctxevaln_evaln.
Qed.

Lemma ufix₁_eval {t} : ufix₁ (abs t) -->+ t[beta1 (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))].
Proof.
  refine (evaln_to_evalPlus _).
  apply ufix₁_evaln.
Qed.

Lemma ufix_ws (γ : Dom) :
  ⟨ γ ⊢ ufix ⟩.
Proof.
  unfold ufix, ufix₁.
  crush.
Qed.

(* TODO: simplify using result about scoping under subst... *)
Lemma ufix₁_ws {γ t} :
  ⟨ γ ⊢ t ⟩ → ⟨ γ ⊢ ufix₁ t ⟩.
Proof.
  unfold ufix₁.
  crush.
Qed.
