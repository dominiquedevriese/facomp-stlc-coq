Require Export Db.Inst.
Require Export Stlc.SpecSyntax.

Instance vrTm : Vr Tm := {| vr := var |}.
Proof. inversion 1; auto. Defined.

Module TmKit <: Kit.

  Definition TM := Tm.
  Definition inst_vr := vrTm.

  Section Application.

    Context {Y: Type}.
    Context {vrY : Vr Y}.
    Context {wkY: Wk Y}.
    Context {liftY: Lift Y Tm}.

    Hint Rewrite (up_idm Y) : infrastructure.
    Hint Rewrite (lift_vr' Y Tm) : infrastructure.

    Global Instance inst_ap : Ap Tm Y := {| ap := apTm |}.
    Proof. induction x; cbn; f_equal; crushDb. Defined.

    Global Instance inst_ap_vr : LemApVr Tm Y := {}.
    Proof. reflexivity. Qed.

  End Application.

  Section Weakening.

    Global Instance inst_ap_inj: LemApInj Tm Ix := {}.
    Proof.
      intros m Inj_m x. revert m Inj_m.
      induction x; destruct y; simpl; try discriminate;
      inversion 1; subst; f_equal; eauto using InjSubIxUp.
    Qed.

  End Weakening.

  Section ApCompTm.

    Variable Y Z: Type.
    Context {vrY: Vr Y}.
    Context {wkY: Wk Y}.
    Context {liftY: Lift Y Tm}.
    Context {vrZ: Vr Z}.
    Context {wkZ: Wk Z}.
    Context {liftZ: Lift Z Tm}.
    Context {apYZ: Ap Y Z}.
    Context {apLiftYTmZ: LemApLift Y Z Tm}.
    Context {compUpYZ: LemCompUp Y Z}.

    Hint Rewrite (comp_up' Y Z) : infrastructure.

    Global Instance inst_ap_comp : LemApComp Tm Y Z := {}.
    Proof. induction x; crushStlc. Qed.

  End ApCompTm.

  Section Instantiation.

    Variable Y: Type.
    Context {vrY: Vr Y}.
    Context {wkY: Wk Y}.
    Context {liftY: Lift Y Tm}.

    Hint Rewrite (up_liftSub Y) : infrastructure.
    Hint Rewrite (up_comp_lift Tm) : infrastructure.
    Hint Rewrite (lift_vr' Y Tm) : infrastructure.

    Global Instance inst_ap_liftSub: LemApLiftSub Tm Y := {}.
    Proof. induction t; crushStlc. Qed.

    Lemma inst_ap_ixComp (t: Tm) :
      ∀ (ξ: Sub Ix) (ζ: Sub Tm), t[ξ][ζ] = t[⌈ξ⌉ >=> ζ].
    Proof. induction t; crushStlc. Qed.

  End Instantiation.

End TmKit.

Module InstTm := Inst TmKit.
Export InstTm.

(* TODO(SK): For some reason these don't in Inst *)
Hint Rewrite (up_liftSub Tm) : infrastructure.
Hint Rewrite (liftSub_wkm Tm) : infrastructure.
Hint Rewrite (liftSub_wkms Tm) : infrastructure.
