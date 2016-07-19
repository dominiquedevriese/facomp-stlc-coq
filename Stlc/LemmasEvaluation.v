Require Export Stlc.SpecSyntax.
Require Export Stlc.SpecEvaluation.
Require Export Stlc.LemmasSyntaxBasic.

Lemma evalPlusToStar {t t'} : evalPlus t t' -> evalStar t t'.
Proof.
  induction 1; apply rt1n_trans with y; eauto using clos_refl_trans_1n.
Qed.
      
Lemma cycles_dont_terminate_help {t t'} : evalStar t' t -> evalPlus t t -> ~Terminating t'.
Proof.
  unfold not.
  intros tptot ttot term.
  depind term.
  depind tptot.
  * depind ttot.
    + exact (H1 x H (rt1n_refl Tm eval x)).
    + refine (H1 y H _). 
      apply evalPlusToStar; assumption.
  * apply H1 with y; assumption.
Qed.

Lemma cycles_dont_terminate {t} : evalPlus t t -> ~Terminating t.
Proof.
  apply cycles_dont_terminate_help; constructor.
Qed.


(* Local Variables: *)
(* coq-load-path: (("." "Stlc")) *)
(* End: *)