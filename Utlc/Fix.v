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

Lemma ufix_eval₁' f C (eC : ECtx C) (valf: Value f) : pctx_app (app ufix f) C --> pctx_app (ufix₁ f) C.
Proof.
  unfold ufix, ufix₁.
  apply (eval_ctx₀ C); auto.
  apply eval_beta''; crush.
Qed.

Lemma ufix_eval₁ f (valf: Value f) : app ufix f --> ufix₁ f.
Proof.
  apply (ufix_eval₁' _ phole); crush.
Qed.

Lemma ufix₁_evaln' {t} C (eC : ECtx C) : evaln (pctx_app (ufix₁ (abs t)) C) (pctx_app (t[beta1 (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))]) C) 2.
Proof.
  cut (pctx_app (ufix₁ (abs t)) C --> pctx_app (app (abs t) (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))) C /\
       pctx_app (app (abs t) (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))) C --> pctx_app (t[beta1 (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))]) C).
  - destruct 1. eauto using evaln with eval.
  - split.
    + unfold ufix₁.
      apply (eval_ctx₀ C); crush.
      apply eval_beta''; crush.
    + apply (eval_ctx₀ C); crush.
      apply eval_beta; crush.
Qed.

Lemma ufix₁_evaln {t} : evaln (ufix₁ (abs t)) (t[beta1 (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))]) 2.
Proof.
  apply (ufix₁_evaln' phole I).
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
