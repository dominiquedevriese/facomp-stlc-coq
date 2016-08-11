Require Import Utlc.SpecSyntax.
Require Import Utlc.SpecEvaluation.
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

Lemma ufix_eval₁ {f} (valf: Value f) : app ufix f --> ufix₁ f.
Proof.
  unfold ufix, ufix₁.
  apply eval_beta'; crush.
Qed.

Lemma ufix₁_eval {t} : ufix₁ (abs t) -->+ t[beta1 (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))].
Proof.
  cut (ufix₁ (abs t) --> app (abs t) (abs (app (ufix₁ (abs t[wkm↑])) (var 0))) /\
       app (abs t) (abs (app (ufix₁ (abs t[wkm↑])) (var 0))) --> t[beta1 (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))]).
  - destruct 1. eauto with eval.
  - split.
    + unfold ufix₁.
      apply eval_beta'; crush.
    + apply eval_beta'; constructor.
Qed.

Lemma ufix_ws (γ : Dom) :
  ⟨ γ ⊢ ufix ⟩.
Proof.
  unfold ufix, ufix₁.
  crush.
Qed.
