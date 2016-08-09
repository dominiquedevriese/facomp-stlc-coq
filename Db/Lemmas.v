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
  Class LemApLiftSub {apXIx: Ap X Ix} : Prop :=
    ap_liftSub: ∀ (t: X) (ξ: Sub Ix), t[⌈ξ⌉] = t[ξ].

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
Arguments ap_liftSub {_ _ _ _ _ _} t ξ.

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

Definition ap_id'      := @ap_id.
Definition ap_comp'    := @ap_comp.
Definition ap_vr'      := @ap_vr.
Definition ap_lift'    := @ap_lift.
Definition ap_wk'      := @ap_wk.
Definition ap_wks'     := @ap_wks.
Definition comp_up'    := @comp_up.
Definition lift_vr'    := @lift_vr.
Definition ap_liftSub' := @ap_liftSub.

Arguments ap_id _ _ {_ _} x.
Arguments ap_comp' _ _ _ {_ _ _ _ _ _} x ξ ζ.
Arguments ap_vr' _ _ {_ _ _ _ _} ξ i.
Arguments ap_lift' _ _ _ {_ _ _ _ _ _ _} ζ x.
Arguments ap_wk' _ _ {_ _ _ _ _ _} x.
Arguments ap_wks' _ _ {_ _ _ _ _ _ _ _ _} δ x.
Arguments comp_up' _ _ {_ _ _ _ _ _} ξ ζ.
Arguments lift_vr' _ _ {_ _ _} i.
Arguments ap_liftSub' _ _ {_ _ _ _} t ξ.

Section Indices.

  Global Instance compUpIx: LemCompUp Ix Ix := {}.
  Proof. intros; extensionality i; destruct i; reflexivity. Qed.
  Global Instance apLiftSubIx: LemApLiftSub Ix Ix := {}.
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

  (* The following lemmas have more generic versions, but we stick to the
     specialized Ix versions to make proof search easier. *)
  Section Indices.

    Variable X : Type.
    Context {vrX: Vr X}.
    Context {wkX: Wk X}.

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
    Lemma liftSub_wkm : @wkm X _ _ = ⌈@wkm Ix _ _⌉.
    Proof. extensionality i; crushDb. Qed.

    Lemma liftSub_wkms (δ: Dom) : @wkms X _ _ δ = ⌈@wkms Ix _ _ δ⌉.
    Proof.
      induction δ; crushDb.
      rewrite IHδ; extensionality i; crushDb.
    Qed.

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

    Variable X : Type.
    Context {vrX: Vr X}.
    Context {wkX: Wk X}.
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

    Lemma apply_up_wk (ξ: Sub X) (i: Ix) :
      (ξ↑) (wk i) = wk (ξ i).
    Proof. reflexivity. Qed.
    Hint Rewrite apply_up_wk : infrastructure.

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

    Variable X : Type.
    Context {vrX: Vr X}.
    Context {wkX: Wk X}.
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

    Variable X : Type.
    Context {vrX: Vr X}.
    Context {wkX: Wk X}.
    Context {apX : Ap X X}.
    Context {apWkX: LemApWk X X}.
    Context {apVrX: LemApVr X X}.
    Context {apCompX: LemApComp X X X}.
    Hint Rewrite (ap_vr' X X): infrastructure.
    Hint Rewrite (wk_vr' X): infrastructure.
    Hint Rewrite apply_wk_ap: infrastructure2.
    Hint Rewrite (comp_id_right X): infrastructure.
    Hint Rewrite (ap_comp' X X X): infrastructure.
    Hint Rewrite (apply_wkms): infrastructure2.
    Hint Rewrite (ap_id' X X) : infrastructure.
    Hint Rewrite (snoc_wk X) : infrastructure.
    Hint Rewrite (up_wk X) : infrastructure.

    Lemma apply_beta_wks (δ: Dom) :
      ∀ (ξ: Sub X) i, beta δ ξ (wks δ i) = vr i.
    Proof. induction δ; crushDb. Qed.
    Hint Rewrite apply_beta_wks : infrastructure.

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

    Lemma wkms_beta_cancel δ (ξ: Sub X) :
      wkms δ >=> beta δ ξ = idm X.
    Proof. extensionality i; crushDb. Qed.

    Lemma beta1_comm (x : X) (ζ: Sub X) :
      beta1 x >=> ζ  =
      (ζ ↑)   >=> beta1 x[ζ].
    Proof. apply (beta_comm 1). Qed.

    Lemma wkm_beta1_cancel (x: X) :
      wkm >=> beta1 x = idm X.
    Proof. apply (wkms_beta_cancel 1). Qed.

  End BetaInteraction.

  Section Misc.

    Variable X : Type.
    Context {vrX: Vr X}.
    Context {wkX: Wk X}.
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

  (* This subsection contains pointful variables of the pointfree lemmas of the
     previous subsection. These are intended to be user-facing. The Db.Inst
     module populates the infrastructure database with these lemmas and some
     others such that it results in a terminating rewrite system (hopefully). *)
  Section Pointful.

    Variable T X: Type.
    Context {vrX: Vr X}.
    Context {wkX: Wk X}.
    Context {apTIx: Ap T Ix}.
    Context {apTX: Ap T X}.
    Context {apXX: Ap X X}.
    Context {apLiftSub: LemApLiftSub T X}.
    Context {apCompTX: LemApComp T X X}.
    Context {apVrX: LemApVr X X}.
    Context {apWkX: LemApWk X X}.
    Context {apCompX: LemApComp X X X}.
    Context {apXIx: Ap X Ix}.
    Context {compUpX: LemCompUp X X}.

    Hint Rewrite (ap_comp' T X X): infrastructure.
    Hint Rewrite (ap_id' T X) : infrastructure.
    Hint Rewrite up_idm : infrastructure.
    Hint Rewrite ups_idm : infrastructure.

    Hint Rewrite (wkm_comm X) : infrastructure.
    Hint Rewrite (wkms_beta_cancel X): infrastructure.
    Hint Rewrite (beta1_comm X): infrastructure.
    Hint Rewrite (wkm_beta1_cancel X): infrastructure.

    (* Extraordinarily rewrite in the opposite direction. *)
    Hint Rewrite <- ap_liftSub : infrastructure.
    Hint Rewrite <- (liftSub_wkm X) : infrastructure.
    Hint Rewrite <- comp_up : infrastructure.
    Hint Rewrite <- comp_ups : infrastructure.
    Hint Rewrite <- (up_liftSub X) : infrastructure.
    Hint Rewrite <- (ups_liftSub X) : infrastructure.

    Lemma apply_wkm_comm (t: T) (ξ: Sub X) :
      t[ξ][@wkm Ix _ _] =
      t[@wkm Ix _ _][ξ↑].
    Proof. crushDb. Qed.

    Lemma apply_wkm_beta1_cancel (t: T) (x: X) :
      t[@wkm Ix _ _][beta1 x] = t.
    Proof. crushDb. Qed.

    Lemma apply_beta1_comm (t: T) (x: X) (ζ: Sub X) :
      t[beta1 x][ζ] = t[ζ↑][beta1 x[ζ]].
    Proof. crushDb. Qed.

    (* 1 up variant *)
    Lemma apply_wkm_up_comm (t: T) (ξ: Sub X) :
      t[ξ↑][(@wkm Ix _ _)↑] =
      t[(@wkm Ix _ _)↑][ξ↑↑].
    Proof. crushDb. Qed.

    Lemma apply_wkm_beta1_up_cancel (t: T) (x: X) :
      t[(@wkm Ix _ _)↑][(beta1 x)↑] = t.
    Proof. crushDb. Qed.

    Lemma apply_beta1_up_comm (t: T) (x: X) (ζ: Sub X) :
      t[(beta1 x)↑][ζ↑] = t[ζ↑↑][(beta1 x[ζ])↑].
    Proof. crushDb. Qed.

    (* 2 ups variant *)
    Lemma apply_wkm_up2_comm (t: T) (ξ: Sub X) :
      t[ξ↑↑][(@wkm Ix _ _)↑↑] =
      t[(@wkm Ix _ _)↑↑][ξ↑↑↑].
    Proof. crushDb. Qed.

    Lemma apply_wkm_beta1_up2_cancel (t: T) (x: X) :
      t[(@wkm Ix _ _)↑↑][(beta1 x)↑↑] = t.
    Proof. crushDb. Qed.

    Lemma apply_beta1_up2_comm (t: T) (x: X) (ζ: Sub X) :
      t[(beta1 x)↑↑][ζ↑↑] = t[ζ↑↑↑][(beta1 x[ζ])↑↑].
    Proof. crushDb. Qed.

    (* δ ups variant *)
    Lemma apply_wkm_ups_comm (δ: Dom) (t: T) (ξ: Sub X) :
      t[ξ ↑⋆ δ][@wkm Ix _ _ ↑⋆ δ] =
      t[@wkm Ix _ _ ↑⋆ δ][ξ↑ ↑⋆ δ].
    Proof. crushDb. Qed.

    Lemma apply_wkm_beta1_ups_cancel (δ: Dom) (t: T) (x: X) :
      t[@wkm Ix _ _ ↑⋆ δ][beta1 x ↑⋆ δ] = t.
    Proof. crushDb. Qed.

    Lemma apply_beta1_ups_comm (δ: Dom) (t: T) (x: X) (ζ: Sub X) :
      t[beta1 x ↑⋆ δ][ζ ↑⋆ δ] = t[ζ↑ ↑⋆ δ][beta1 x[ζ] ↑⋆ δ].
    Proof. crushDb. Qed.

  End Pointful.

End Lemmas.
