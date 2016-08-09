Require Import Utlc.SpecSyntax.
Require Import Utlc.SpecEvaluation.
Require Import Utlc.SpecScoping.
Require Import Utlc.LemmasScoping.
Require Import Db.Lemmas.

Definition ufix₁ (f : UTm) : UTm :=
  let t : UTm := abs (app (f[S]) (abs (app (app (var 1) (var 1)) (var 0))))
  in app t t.

Definition ufix : UTm :=
  abs (ufix₁ (var 0)).

Lemma ufix_eval₁ {f} : Value f -> app ufix f --> ufix₁ f.
Proof.
  intro valf. 
  replace (ufix₁ f) with ((ufix₁ (var 0)) [beta1 f]).
  - unfold ufix. eauto with eval.
  - unfold ufix₁. crushDb.
Qed.

Lemma ufix₁_eval {t} : ufix₁ (abs t) -->* t[beta1 (abs (app (ufix₁ ((abs t) [S])) (var 0)))].
Proof.
  cut (ufix₁ (abs t) --> app (abs t) (abs (app (ufix₁ ((abs t) [S])) (var 0))) /\ app (abs t) (abs (app (ufix₁ ((abs t) [S])) (var 0))) --> t[beta1 (abs (app (ufix₁ ((abs t) [S])) (var 0)))]).
  - destruct 1. eauto with eval.
  - split.
    + unfold ufix₁. 
      refine (eq_rect _ (fun t => (_ --> t)) _ _ _).
      * eapply eval_beta; constructor.
      * refine (f_equal2 app _ _).
        { rewrite <- ap_liftSub.
          refine (eq_trans (ap_comp (abs t) (⌈S⌉) (beta1 _)) _).
          refine (eq_trans (f_equal (fun s => (abs t)[s]) _) _).
          + refine (wkms_beta_cancel UTm 1 _).
          + eapply ap_id.
        } 
        { crushUtlc; repeat rewrite -> ap_comp; repeat rewrite <- comp_up; refine (f_equal (fun s => t[s ↑]) _); exact (eq_sym (wkm_comm Ix S)).
        }
    + eapply eval_beta; constructor.
Qed.

Lemma ufix_ws (γ : Dom) :
  ⟨ γ ⊢ ufix ⟩.
Proof.
  unfold ufix, ufix₁.
  constructor.
  crushUtlcScoping.
Qed.