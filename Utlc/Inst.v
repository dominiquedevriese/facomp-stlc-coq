Require Import Db.Inst.
Require Export Utlc.SpecSyntax.

Instance vrUTm : Vr UTm := {| vr := var |}.
Proof. inversion 1; auto. Defined.

Module UTmKit <: Kit.

  Definition TM := UTm.
  Definition inst_vr := vrUTm.

  Section Application.

    Context {Y: Type}.
    Context {vrY : Vr Y}.
    Context {wkY: Wk Y}.
    Context {liftY: Lift Y UTm}.

    Hint Rewrite (up_idm Y) : infrastructure.
    Hint Rewrite (lift_vr' Y UTm) : infrastructure.

    Global Instance inst_ap : Ap UTm Y := {| ap := apUTm |}.
    Proof. induction x; cbn; f_equal; crushDb. Defined.

    Global Instance inst_ap_vr : LemApVr UTm Y := {}.
    Proof. reflexivity. Qed.

  End Application.

  Section Weakening.

    Global Instance inst_ap_inj: LemApInj UTm Ix := {}.
    Proof.
      intros m Inj_m x. revert m Inj_m.
      induction x; destruct y; simpl; try discriminate;
      inversion 1; subst; f_equal; eauto using InjSubIxUp.
    Qed.

  End Weakening.

  Hint Rewrite (up_liftSub UTm) : infrastructure.
  Hint Rewrite (up_comp_lift UTm) : infrastructure.

  Section ApCompUTm.

    Variable Y Z: Type.
    Context {vrY: Vr Y}.
    Context {wkY: Wk Y}.
    Context {liftY: Lift Y UTm}.
    Context {vrZ: Vr Z}.
    Context {wkZ: Wk Z}.
    Context {liftZ: Lift Z UTm}.
    Context {apYZ: Ap Y Z}.
    Context {apLiftYUTmZ: LemApLift Y Z UTm}.
    Context {compUpYZ: LemCompUp Y Z}.

    Hint Rewrite (comp_up' Y Z) : infrastructure.

    Global Instance inst_ap_comp : LemApComp UTm Y Z := {}.
    Proof. induction x; crushUtlc. Qed.

  End ApCompUTm.

  Section Instantiation.

    Global Instance inst_ap_liftSub: LemApLiftSub UTm := {}.
    Proof. induction x; crushUtlc. Qed.

    Lemma inst_ap_ixComp (t: UTm) :
      ∀ (ξ: Sub Ix) (ζ: Sub UTm), t[ξ][ζ] = t[⌈ξ⌉ >=> ζ].
    Proof. induction t; crushUtlc. Qed.
  End Instantiation.

End UTmKit.

Module InstUTm := Inst UTmKit.
(* O.o Instances and rewrite rules are visible simply by creating
   the module on the previous line. *)
(* Export InstUTm. *)

Section ApplicationPCtx.

  Context {Y: Type}.
  Context {vrY : Vr Y}.
  Context {wkY: Wk Y}.
  Context {liftYUTm: Lift Y UTm}.

  Hint Rewrite (up_idm Y) : infrastructure.
  Hint Rewrite (ap_id' UTm) : infrastructure.

  Global Instance ApPCtx : Ap PCtx Y := {| ap := apPCtx |}.
  Proof. induction x; crushUtlc. Defined.

End ApplicationPCtx.
