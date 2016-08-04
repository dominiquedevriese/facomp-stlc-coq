Require Export Stlc.SpecSyntax.
Require Export Stlc.SpecEvaluation.
Require Export Stlc.SpecTyping.
Require Export Stlc.LemmasTyping.
Require Export Stlc.LemmasEvaluation.

Definition stlcOmega (ty : Ty) : Tm :=
  app (fixt tunit ty (abs (tunit ⇒ ty) (var 0))) unit.

Lemma stlcOmegaT {Γ ty} : ⟪ Γ ⊢ stlcOmega ty : ty ⟫.
Proof.
  unfold stlcOmega. crushTyping.
Qed.

Definition stlcOmegaHelp (ty : Ty) : Tm :=
  app (abs tunit (app (fixt tunit ty (abs (tunit ⇒ ty) (var 0))) (var 0))) unit.

Lemma stlcOmega_cycles {ty} : stlcOmega ty -->+ stlcOmega ty.
Proof.
  cut (stlcOmega ty --> stlcOmegaHelp ty ∧ stlcOmegaHelp ty --> stlcOmega ty).
  - destruct 1. eauto with eval.
  - unfold stlcOmega, stlcOmegaHelp; split.
    + apply (eval_ctx (papp₁ phole unit)); constructor.
    + repeat constructor.
Qed.

Lemma stlcOmega_div {ty} : (stlcOmega ty)⇑.
Proof.
  apply cycles_dont_terminate.
  apply stlcOmega_cycles.
Qed.
