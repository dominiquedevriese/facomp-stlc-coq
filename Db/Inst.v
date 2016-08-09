Require Export Db.Spec.
Require Export Db.Lemmas.
Require Import Coq.Logic.FunctionalExtensionality.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.

Instance wkT {T} {vrT: Vr T}
  {apT: ∀ {Y} {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y T}, Ap T Y}
  {apVrT: ∀ {Y} {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y T}, LemApVr T Y}
  {apTIxInj: LemApInj T Ix} : Wk T :=
  {| wk := ap wk;
     wk_inj := ap_inj wk_inj;
     wk_vr := ap_vr wk
  |}.

Module Type Kit.

  Parameter TM: Type.
  Parameter inst_vr: Vr TM.
  Parameter inst_ap: ∀ Y {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y TM}, Ap TM Y.

  Parameter inst_ap_inj: LemApInj TM Ix.
  Parameter inst_ap_vr: ∀ Y {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y TM}, LemApVr TM Y.
  Parameter inst_ap_comp:
    ∀ Y Z {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y TM} {vrZ: Vr Z} {wkZ: Wk Z}
      {liftZ: Lift Z TM} {apYZ: Ap Y Z} {apLiftYZTM: LemApLift Y Z TM}
      {compUpYZ: LemCompUp Y Z}, LemApComp TM Y Z.
  Parameter inst_ap_liftSub: LemApLiftSub TM.
  Parameter inst_ap_ixComp: ∀ (t: TM) (ξ: Sub Ix) (ζ: Sub TM), t[ξ][ζ] = t[⌈ξ⌉ >=> ζ].

End Kit.

Module Inst (kit: Kit).

  Import kit.

  Instance inst_apTMZTM {Z} {vrZ: Vr Z} {apTMZ: Ap TM Z} :
    LemApLift TM Z TM := λ _ _, eq_refl.
  Instance inst_apLiftIxIx: LemApLift Ix Ix TM := ap_vr.

  Instance compUpTMIx: LemCompUp TM Ix := {}.
  Proof.
    intros; extensionality i; destruct i; simpl;
      rewrite ?ap_vr, ?ap_comp; reflexivity.
  Qed.

  Instance inst_wkApIx: LemApWk TM Ix := λ _, eq_refl.

  Instance compUpTM: LemCompUp TM TM := {}.
  Proof.
    intros; extensionality i; destruct i; simpl.
    - rewrite ap_vr; reflexivity.
    - rewrite inst_ap_ixComp.
      rewrite ap_comp.
      f_equal.
      extensionality j; destruct j; simpl;
        rewrite ap_vr; reflexivity.
  Qed.

  Instance wkApTM: LemApWk TM TM := {}.
  Proof.
    simpl; intros.
    rewrite <- ap_liftSub.
    f_equal.
    extensionality i; simpl.
    rewrite ap_vr.
    reflexivity.
  Qed.

  (* Instance sbTM: Subst TM := {}. *)

  (* Automatically populate the infrastructure database for type TM with lemmas
     for which the rewrite direction is certain. *)
  Hint Rewrite (apply_beta1_comm TM) : infrastructure.
  Hint Rewrite (ap_comp' TM TM TM) : infrastructure.
  Hint Rewrite (wkm_beta_cancel TM) : infrastructure.
  Hint Rewrite (wkm_beta_cancel' TM) : infrastructure.
  Hint Rewrite (wkm_beta_cancel'' TM) : infrastructure.
  Hint Rewrite (wkms_beta_cancel TM) : infrastructure.
  Hint Rewrite (wkms_beta_cancel' TM) : infrastructure.
  Hint Rewrite (wkms_beta_cancel'' TM) : infrastructure.
  Hint Rewrite (beta1_comm TM) : infrastructure.

End Inst.
