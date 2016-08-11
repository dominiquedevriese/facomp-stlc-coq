Require Export Db.Inst.
Require Export Db.Lemmas.
Require Export Utlc.SpecSyntax.

Instance vrUTm : Vr UTm := {| vr := var |}.
Proof. inversion 1; auto. Defined.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushUtlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasMatchH;
     rewrite ?comp_up, ?up_liftSub, ?up_comp_lift
    );
  auto.

Module UTmKit <: Kit.

  Definition TM := UTm.
  Definition inst_vr := vrUTm.

  Section Application.

    Context {Y: Type}.
    Context {vrY : Vr Y}.
    Context {wkY: Wk Y}.
    Context {liftY: Lift Y UTm}.

    Global Instance inst_ap : Ap UTm Y := {| ap := apUTm |}.
    Proof. induction x; crush. Defined.

    Global Instance inst_ap_vr : LemApVr UTm Y := {}.
    Proof. reflexivity. Qed.

  End Application.

  Instance inst_ap_inj: LemApInj UTm Ix := {}.
  Proof.
    intros m Inj_m x. revert m Inj_m.
    induction x; destruct y; simpl; try discriminate;
    inversion 1; subst; f_equal; eauto using InjSubIxUp.
  Qed.

  Instance inst_ap_comp (Y Z: Type)
    {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y UTm}
    {vrZ: Vr Z} {wkZ: Wk Z} {liftZ: Lift Z UTm}
    {apYZ: Ap Y Z} {compUpYZ: LemCompUp Y Z}
    {apLiftYUTmZ: LemApLift Y Z UTm} :
    LemApComp UTm Y Z := {}.
  Proof. induction x; crush. Qed.

  Instance inst_ap_liftSub (Y: Type)
    {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y UTm} :
    LemApLiftSub UTm Y := {}.
  Proof. induction t; crush. Qed.

  Lemma inst_ap_ixComp (t: UTm) :
    ∀ (ξ: Sub Ix) (ζ: Sub UTm), t[ξ][ζ] = t[⌈ξ⌉ >=> ζ].
  Proof. pose proof up_comp_lift. induction t; crush. Qed.

End UTmKit.

Module InstUTm := Inst UTmKit.
(* Instances are visible simply by creating the module on the previous line, but
   we export the contents anyway so that the implicits have shorter names in
   unambiguous contexts. *)
Export InstUTm.

Section ApplicationPCtx.

  Context {Y: Type}.
  Context {vrY : Vr Y}.
  Context {wkY: Wk Y}.
  Context {liftYUTm: Lift Y UTm}.

  Global Instance ApPCtx : Ap PCtx Y := {| ap := apPCtx |}.
  Proof. induction x; crush. Defined.

End ApplicationPCtx.
