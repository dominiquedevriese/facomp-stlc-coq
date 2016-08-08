Require Export Db.Spec.
Require Import Coq.Logic.FunctionalExtensionality.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.

Section Application.

  Variable X Y Z: Type.
  Context {vrY: Vr Y}.
  Context {apXY: Ap X Y}.
  Context {vrZ: Vr Z}.

  Class LemApInj : Prop :=
    ap_inj: ∀ (m: Sub Y), Inj m → Inj (ap m).
  Class LemApComp {apXZ: Ap X Z} {apYZ: Ap Y Z} : Prop :=
    ap_comp: ∀ (x: X) (ξ: Sub Y) (ζ: Sub Z), x[ξ][ζ] = x[ξ >=> ζ].

  Context {vrX: Vr X}.

  Class LemApVr {liftYX: Lift Y X} : Prop :=
    ap_vr: ∀ (ξ: Sub Y) (i: Ix), (vr i)[ξ] = lift (ξ i).
  Class LemApLift {liftXZ: Lift X Z} {apZY: Ap Z Y}: Prop :=
    ap_lift: ∀ (ζ: Sub Y) (x: X), (lift x)[ζ] = lift x[ζ].

  Context {wkX: Wk X}.
  Context {wkY: Wk Y}.

  Class LemApWk : Prop :=
    ap_wk: ∀ (x: X), x[@wkm Y _ _] = @wk X _ _ x.
  Class LemCompUp : Prop :=
    comp_up: ∀ (ξ : Sub X) (ζ : Sub Y), (ξ >=> ζ)↑ = (ξ↑) >=> (ζ↑).

End Application.

Arguments ap_inj {_ _ _ _ _ m} _ [_ _] _.
Arguments ap_comp {_ _ _ _ _ _ _ _ _} x ξ ζ.
Arguments ap_vr {_ _ _ _ _ _ _} ξ i.
Arguments ap_lift {_ _ _ _ _ _ _ _ _ _} ζ x.
Arguments ap_wk {_ _ _ _ _ _ _ _} x.
Arguments comp_up {_ _ _ _ _ _ _ _} ξ ζ.

Lemma ap_wks {X Y} {vrX: Vr X} {wkX: Wk X} {vrY: Vr Y} {wkY: Wk Y}
  {apXY: Ap X Y} {apWkXY: LemApWk X Y} {apYY: Ap Y Y}
  {apCompXY: LemApComp X Y Y} {apWkYY: LemApWk Y Y} :
  ∀ (δ: Dom) (x: X), x[@wkms Y _ _ δ] = @wks X _ _ δ x.
Proof.
  induction δ; intros; simpl.
  - apply ap_id.
  - rewrite <- IHδ, <- ap_wk, ap_comp.
    f_equal.
    extensionality i; simpl.
    rewrite ap_wk.
    reflexivity.
Qed.

Definition ap_id'   := @ap_id.
Definition ap_comp' := @ap_comp.
Definition ap_vr'   := @ap_vr.
Definition ap_lift' := @ap_lift.
Definition ap_wk'   := @ap_wk.
Definition ap_wks'  := @ap_wks.
Definition comp_up' := @comp_up.
Definition lift_vr' := @lift_vr.

Arguments ap_id _ _ {_ _} x.
Arguments ap_comp' _ _ _ {_ _ _ _ _ _} x ξ ζ.
Arguments ap_vr' _ _ {_ _ _ _ _} ξ i.
Arguments ap_lift' _ _ _ {_ _ _ _ _ _ _} ζ x.
Arguments ap_wk' _ _ {_ _ _ _ _ _} x.
Arguments ap_wks' _ _ {_ _ _ _ _ _ _ _ _} δ x.
Arguments comp_up' _ _ {_ _ _ _ _ _} ξ ζ.
Arguments lift_vr' _ _ {_ _ _} i.

Section Indices.

  Class LemApLiftSub X {vrX: Vr X} {apXIx: Ap X Ix} {apXX: Ap X X}: Prop :=
    ap_liftSub:
      ∀ (x: X) (ξ: Sub Ix), x[⌈ξ⌉] = x[ξ].

  Global Instance compUpIx: LemCompUp Ix Ix := {}.
  Proof. intros; extensionality i; destruct i; reflexivity. Qed.
  Global Instance apLiftSubIx: LemApLiftSub Ix := {}.
  Proof. reflexivity. Qed.
  Global Instance apVrIx: LemApVr Ix Ix := {}.
  Proof. reflexivity. Qed.
  Global Instance wkApIxIx: LemApWk Ix Ix := {}.
  Proof. reflexivity. Qed.
  Global Instance apCompIxIxIx: LemApComp Ix Ix Ix := {}.
  Proof. reflexivity. Qed.

End Indices.

Arguments liftXX_id _ {_} _.
Hint Rewrite liftXX_id : infrastructure.
Hint Rewrite (ap_wks' Ix Ix) : infrastructure2.

(** *** Domains *)

Lemma dunion_assoc (δ₁ δ₂ δ₃: Dom) :
  δ₁ ∪ (δ₂ ∪ δ₃) = (δ₁ ∪ δ₂) ∪ δ₃.
Proof. induction δ₃; simpl; congruence. Qed.
Hint Rewrite dunion_assoc: infrastructure.

Section Lemmas.

  (* Injectivity is closed under up. *)
  Lemma InjSubIxUp (ξ: Sub Ix) :
    Inj ξ → Inj (ξ ↑).
  Proof.
    unfold Inj, up in *; simpl; intros.
    destruct x, y; cbn in *; auto; discriminate.
  Qed.

  Variable X : Type.
  Context {vrX: Vr X}.
  Context {wkX: Wk X}.

  (* The following lemmas have more generic versions, but we stick to the
     specialized Ix versions to make proof search easier. *)
  Section Indices.

    Hint Rewrite (wk_vr' X): infrastructure.

    (* Up commutes with lift. *)
    Lemma up_liftSub (ξ: Sub Ix) : ⌈ξ⌉↑ = ⌈ξ↑⌉.
    Proof. extensionality i; destruct i; crushDb. Qed.
    Hint Rewrite up_liftSub : infrastructure.

    Lemma ups_liftSub (δ: Dom) :
      ∀ (ξ: Sub Ix), ⌈ξ⌉ ↑⋆ δ = ⌈ξ ↑⋆ δ⌉.
    Proof. induction δ; crushDb; rewrite ?IHδ; crushDb. Qed.

    (* Lifting the identity yields the identity. *)
    Lemma liftSub_id : ⌈idm Ix⌉ = idm X.
    Proof. reflexivity. Qed.

    (* The weakening substitution is just the lifted
       weakening renaming. *)
    Lemma wkm_lift_wk : @wkm X _ _ = ⌈@wkm Ix _ _⌉.
    Proof. extensionality i; crushDb. Qed.

    Context {apX : Ap X X}.
    Context {apVrX: LemApVr X X}.
    Hint Rewrite (ap_vr' X X): infrastructure.

    (* Up commutes with the composition with a lifting
       on the left-hand side .*)
    Lemma up_comp_lift (ξ: Sub Ix) (ζ: Sub X):
      (⌈ξ⌉ >=> ζ)↑ = ⌈ξ↑⌉ >=> ζ↑.
    Proof. extensionality i; destruct i; crushDb. Qed.

  End Indices.

  Section Weakening.

    Context {apX : Ap X X}.
    Context {apWkX: LemApWk X X}.
    Hint Rewrite (wk_vr' X): infrastructure.
    Hint Rewrite (ap_wk' X): infrastructure.

    Lemma ups_dunion (ξ: Sub X) δ₁ δ₂ :
      (ξ ↑⋆ δ₁) ↑⋆ δ₂ = ξ ↑⋆ (δ₁ ∪ δ₂).
    Proof.
      induction δ₂; crushDb.
      rewrite IHδ₂; crushDb.
    Qed.
    (* TODO: rewrite direction? *)

    Lemma ups_up (ξ : Sub X) δ : (ξ ↑⋆ δ) ↑ = ξ ↑⋆ (S δ).
    Proof. reflexivity. Qed.

    Lemma up_idm : up (idm X) = idm X.
    Proof. extensionality i; destruct i; crushDb. Qed.
    Hint Rewrite up_idm : infrastructure.

    Lemma ups_idm (δ: Dom) : ups (idm X) δ = idm X.
    Proof. induction δ; cbn; rewrite ?IHδ; crushDb. Qed.
    (* Hint Rewrite ups_idm : infrastructure. *)

    Lemma up_def (ζ: Sub X) :
      ζ ↑ = (ζ >=> wkm) · vr 0.
    Proof. extensionality i; destruct i; crushDb. Qed.

    Lemma apply_ups_wks (ξ: Sub X) (δ: Dom) (i: Ix) :
      (ξ ↑⋆ δ) (wks δ i) = wks δ (ξ i).
    Proof. induction δ; crushDb. Qed.
    (* Hint Rewrite apply_ups_wks: infrastructure2. *)

    Lemma wks_comm δ (ξ: Sub X) :
      ∀ i, wks δ (ξ i) = (ξ ↑⋆ δ) (wks δ i).
    Proof. induction δ; crushDb. Qed.
    (* Hint Rewrite wks_comm: infrastructure. *)

    (* Point-wise the weakening substitution is the
       variable injection of the weakening action on
       indices. *)
    Lemma apply_wkms (δ: Dom) (i: Ix) :
      @wkms X _ _ δ i = vr (wks δ i).
    Proof. induction δ; cbn; rewrite ?IHδ; crushDb. Qed.

    Lemma wkms_zero : wkms 0 = idm X.
    Proof. reflexivity. Qed.
    (* Hint Rewrite wkms_zero: infrastructure. *)

    Lemma wkms_succ (δ: Dom) : wkms (S δ) = wkms δ >=> @wkm X _ _.
    Proof. extensionality i; crushDb. Qed.
    (* Hint Rewrite wkms_succ: infrastructure. *)

    Lemma wkm_snoc0 : wkm · vr 0 = idm X.
    Proof. extensionality i; destruct i; crushDb. Qed.

  End Weakening.

  Section Application.

    Context {apX : Ap X X}.

    Section Het.
      Variable S: Type.
      Context {vrS : Vr S}.
      Context {wkS : Wk S}.
      Context {apXS: Ap X S}.

      Hint Rewrite (@ap_id X S): infrastructure.

      Lemma comp_id_right (ζ: Sub X) :
        ζ >=> idm S = ζ.
      Proof. extensionality i; crushDb. Qed.

    End Het.

    Context {apVrX: LemApVr X X}.
    Hint Rewrite (ap_vr' X X): infrastructure.

    Lemma comp_id_left (ζ: Sub X) :
      @idm X _ >=> ζ = ζ.
    Proof. extensionality i; crushDb. Qed.
    Hint Rewrite comp_id_left: infrastructure.

    Lemma comp_snoc (ζ₁ ζ₂: Sub X) t :
      (ζ₁ · t) >=> ζ₂ = (ζ₁ >=> ζ₂) · t[ζ₂].
    Proof. extensionality i; destruct i; crushDb. Qed.

    Context {apWkX: LemApWk X X}.
    Context {apCompX: LemApComp X X X}.
    Hint Rewrite (ap_wks' X X): infrastructure.

    Lemma apply_wk_ap (x: X) (ζ: Sub X) :
      (wk x)[ζ] = x[wkm >=> ζ].
    Proof. rewrite <- ap_wk, ap_comp; auto. Qed.
    Hint Rewrite apply_wk_ap: infrastructure2.

    Lemma apply_wks_ap δ (x: X) (ζ: Sub X) :
      (wks δ x)[ζ] = x[wkms δ >=> ζ].
    Proof. rewrite <- ap_wks, ap_comp; auto. Qed.
    Hint Rewrite apply_wks_ap: infrastructure2.

    (* Always try to associate to the left in rewriting. *)
    Lemma comp_assoc (ζ₁ ζ₂ ζ₃: Sub X) :
      ζ₁ >=> (ζ₂ >=> ζ₃) = (ζ₁ >=> ζ₂) >=> ζ₃.
    Proof. extensionality i; crushDb. Defined.
    Hint Rewrite comp_assoc: infrastructure.

    Hint Rewrite (apply_wkms): infrastructure2.
    Hint Rewrite wks_comm: infrastructure.

    Lemma wkms_comm δ (ξ: Sub X) :
      ξ      >=> wkms δ =
      wkms δ >=> (ξ ↑⋆ δ).
    Proof. extensionality i; crushDb. Qed.
    Hint Rewrite wkms_comm: infrastructure.

    Lemma wkm_comm (ξ: Sub X) :
      ξ   >=> wkm =
      wkm >=> ξ↑.
    Proof. apply (wkms_comm 1). Qed.
    Hint Rewrite wkm_comm: infrastructure.

    Context {Y: Type}.
    Context {vrY: Vr Y}.
    Context {wkY: Wk Y}.
    Context {apXY: Ap X Y}.
    Context {compUpX : LemCompUp X Y}.

    Hint Rewrite (comp_up' X Y) : infrastructure.

    Lemma comp_ups (ξ: Sub X) (ζ: Sub Y) (δ: Dom) :
      (ξ >=> ζ) ↑⋆ δ  = (ξ ↑⋆ δ) >=> (ζ ↑⋆ δ).
    Proof. induction δ; cbn; rewrite ?IHδ; crushDb. Qed.

  End Application.

  Section BetaInteraction.

    Context {apX : Ap X X}.
    Context {apWkX: LemApWk X X}.
    Context {apVrX: LemApVr X X}.
    Context {apCompX: LemApComp X X X}.
    Hint Rewrite (ap_vr' X X): infrastructure.
    Hint Rewrite (wk_vr' X): infrastructure.
    Hint Rewrite apply_wk_ap: infrastructure2.
    Hint Rewrite (comp_id_right X): infrastructure.
    Hint Rewrite (ap_comp): infrastructure.
    Hint Rewrite (apply_wkms): infrastructure2.

    Lemma beta_comm δ (ζ₁ ζ₂: Sub X) :
      beta δ ζ₁  >=> ζ₂  =
      (ζ₂ ↑⋆ δ)  >=> beta δ (ζ₁ >=> ζ₂).
    Proof.
      extensionality i. revert ζ₁ ζ₂ i.
      induction δ; crushDb.
      destruct i; crushDb.
      rewrite IHδ; crushDb.
      f_equal; extensionality j; crushDb.
    Qed.

    Lemma beta1_comm x (ζ: Sub X) :
      beta1 x >=> ζ  =
      (ζ ↑)   >=> beta1 x[ζ].
    Proof. apply (beta_comm 1). Qed.
    Hint Rewrite beta1_comm: infrastructure.

    Lemma apply_beta1_comm x₁ x₂ (ζ: Sub X) :
      x₂[beta1 x₁][ζ] = x₂[ζ↑][beta1 x₁[ζ]].
    Proof. crushDb. Qed.
    Hint Rewrite apply_beta1_comm: infrastructure.

    Lemma subst0_comm x₁ x₂ (ζ: Sub X) :
      (subst0 x₁ x₂)[ζ] =
      subst0 x₁[ζ] x₂[ζ↑].
    Proof. unfold subst0; crushDb. Qed.
    (* Hint Rewrite subst0_comm: infrastructure. *)

    Lemma apply_beta_wks (δ: Dom) :
      ∀ (ξ: Sub X) i, beta δ ξ (wks δ i) = vr i.
    Proof. induction δ; crushDb. Qed.
    Hint Rewrite apply_beta_wks: infrastructure2.

    Lemma wkms_beta_cancel δ (ξ: Sub X) :
      wkms δ >=> beta δ ξ = idm X.
    Proof. extensionality i; crushDb. Qed.
    (* Hint Rewrite wkms_beta_cancel: infrastructure. *)

    Context {compUpX: LemCompUp X X}.

    Lemma wkms_beta_cancel' δ k (ξ: Sub X) :
      (wkms δ ↑⋆ k) >=> (beta δ ξ ↑⋆ k) = idm X.
    Proof.
      rewrite <- comp_ups, wkms_beta_cancel;
      apply ups_idm.
    Qed.
    (* Hint Rewrite wkms_beta_cancel: infrastructure. *)

  End BetaInteraction.

  Section Misc.

    Context {apX: Ap X X}.
    Context {apVrX: LemApVr X X}.
    Hint Rewrite (ap_vr' X X): infrastructure.
    Hint Rewrite (wk_vr' X): infrastructure.

    Lemma wkm_snoc_cancel (ζ: Sub X) t : wkm >=> (ζ · t) = ζ.
    Proof. extensionality i; destruct i; crushDb. Qed.
    (* Hint Rewrite wkm_snoc_cancel: infrastructure. *)

    Lemma snoc_eta_red (ζ: Sub X) : (wkm >=> ζ) · ζ 0 = ζ.
    Proof. extensionality i; destruct i; crushDb. Qed.
    (* Hint Rewrite snoc_eta_red: infrastructure. *)

  End Misc.

End Lemmas.
