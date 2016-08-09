Require Import Utlc.SpecSyntax.
Require Import Utlc.SpecEvaluation.
Require Import Utlc.SpecScoping.
Require Import Utlc.LemmasScoping.
Require Import Utlc.Inst.
Require Import Db.Lemmas.
Require Coq.Setoids.Setoid.

Definition ufix₁ (f : UTm) : UTm :=
  let t : UTm := abs (app f[wkm] (abs (app (app (var 1) (var 1)) (var 0))))
  in app t t.

Definition ufix : UTm :=
  abs (ufix₁ (var 0)).

Lemma ufix_eval₁ {f} (valf: Value f) : app ufix f --> ufix₁ f.
Proof.
  unfold ufix, ufix₁.
  apply eval_beta'; crushUtlc.
  (* TODO(SK): Clean this up. *)
  apply ap_liftSub.
  apply ap_liftSub.
Qed.

Lemma ufix₁_eval {t} : ufix₁ (abs t) -->+ t[beta1 (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))].
Proof.
  cut (ufix₁ (abs t) --> app (abs t) (abs (app (ufix₁ (abs t[wkm↑])) (var 0))) /\
       app (abs t) (abs (app (ufix₁ (abs t[wkm↑])) (var 0))) --> t[beta1 (abs (app (ufix₁ (abs t[wkm↑])) (var 0)))]).
  - destruct 1. eauto with eval.
  - split.
    + apply eval_beta'; crushUtlc.
      (* TODO(SK): Clean these up. *)
      * rewrite <- (ap_id' UTm UTm) at 1.
        f_equal.
        extensionality i; destruct i; crushUtlc.
      * unfold ufix₁.
        rewrite <- ap_liftSub; crushUtlc; f_equal;
          extensionality i; destruct i; crushUtlc.
    + apply eval_beta; constructor.
Qed.

Lemma ufix_ws (γ : Dom) :
  ⟨ γ ⊢ ufix ⟩.
Proof.
  unfold ufix, ufix₁.
  crushUtlcScoping.
Qed.
