Require Export Db.Inst.
Require Export Db.Lemmas.
Require Export Stlc.SpecSyntax.

Instance vrTm : Vr Tm := {| vr := var |}.
Proof. inversion 1; auto. Defined.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasMatchH;
     rewrite ?comp_up, ?up_liftSub, ?up_comp_lift
    );
  auto.

Module TmKit <: Kit.

  Definition TM := Tm.
  Definition inst_vr := vrTm.

  Section Application.

    Context {Y: Type}.
    Context {vrY : Vr Y}.
    Context {wkY: Wk Y}.
    Context {liftY: Lift Y Tm}.

    Global Instance inst_ap : Ap Tm Y := {| ap := apTm |}.
    Proof. induction x; crush. Defined.

    Global Instance inst_ap_vr : LemApVr Tm Y := {}.
    Proof. reflexivity. Qed.

  End Application.

  Instance inst_ap_inj: LemApInj Tm Ix := {}.
  Proof.
    intros m Inj_m x. revert m Inj_m.
    induction x; destruct y; simpl; try discriminate;
    inversion 1; subst; f_equal; eauto using InjSubIxUp.
  Qed.

  Instance inst_ap_comp (Y Z: Type)
    {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y Tm}
    {vrZ: Vr Z} {wkZ: Wk Z} {liftZ: Lift Z Tm}
    {apYZ: Ap Y Z} {compUpYZ: LemCompUp Y Z}
    {apLiftYTmZ: LemApLift Y Z Tm} :
    LemApComp Tm Y Z := {}.
  Proof. induction x; crush. Qed.

  Instance inst_ap_liftSub (Y: Type)
    {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y Tm} :
    LemApLiftSub Tm Y := {}.
  Proof. induction t; crush. Qed.

  Lemma inst_ap_ixComp (t: Tm) :
    ∀ (ξ: Sub Ix) (ζ: Sub Tm), t[ξ][ζ] = t[⌈ξ⌉ >=> ζ].
  Proof. pose proof up_comp_lift. induction t; crush. Qed.

End TmKit.

Module InstTm := Inst TmKit.
Export InstTm. (* Export for shorter names. *)
