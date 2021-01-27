Require Export Db.Spec.
Require Export Db.Lemmas.
Require Export StlcIso.Inst.
Require Export StlcIso.SpecTyping.

Hint Constructors GetEvar : ws.

Lemma getEvarInvHere { Γ T U } :
  ⟪ 0 : T i∈ (Γ i▻ U) ⟫ → T = U.
Proof. inversion 1; auto. Qed.

Lemma getEvarInvThere {Γ i T U} :
  ⟪ (S i) : T i∈ Γ i▻ U ⟫ → ⟪ i : T i∈ Γ ⟫.
Proof. inversion 1; auto. Qed.
Hint Resolve getEvarInvThere : wsi.

Ltac crushTypingMatchH :=
  match goal with
    | [ H: ⟪ _ : _ i∈ empty ⟫         |- _ ] =>
      inversion H
    | [ H: ⟪ 0 : _ i∈ _ ⟫         |- _ ] =>
      apply getEvarInvHere in H; repeat subst
    | [ H: ⟪ (S _) : _ i∈ (_ i▻ _) ⟫ |- _ ] =>
      apply getEvarInvThere in H
    | H: ⟪ _ i⊢ var _        : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ i⊢ abs _ _      : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ i⊢ app _ _      : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ i⊢ unit         : _ ⟫ |- _ => inversion H; clear H
    (* | H: ⟪ _ ⊢ true         : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ false        : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ ite _ _ _    : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ pair _ _     : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ proj₁ _      : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ proj₂ _      : _ ⟫ |- _ => inversion H; clear H *)
    | H: ⟪ _ i⊢ inl _        : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ i⊢ inr _        : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ i⊢ caseof _ _ _ : _ ⟫ |- _ => inversion H; clear H

    | H: ⟪ _ i⊢ fold_ _ : _ ⟫ |- _ => inversion H; clear H
    | H: ⟪ _ i⊢ unfold_ _ : _ ⟫ |- _ => inversion H; clear H
    (* | H: ⟪ _ ⊢ seq _ _      : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ fixt _ _ _   : _ ⟫ |- _ => inversion H; clear H *)
    | [ wi : ⟪ ?i : _ i∈ (_ i▻ _) ⟫
        |- context [match ?i with _ => _ end]
      ] => destruct i
    | [ wi : ⟪ ?i : _ i∈ (_ i▻ _) ⟫
        |- context [(_ · _) ?i]
      ] => destruct i
    | [ |- ⟪ _ i⊢ var _ : _ ⟫                    ] => econstructor
    | [ |- ⟪ _ i⊢ abs _ _ : _ ⟫                  ] => econstructor
    | [ |- ⟪ _ i⊢ app _ _ : _ ⟫                  ] => econstructor
    | [ |- ⟪ _ i⊢ unit : _ ⟫                     ] => econstructor
    (* | [ |- ⟪ _ ⊢ true : _ ⟫                     ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ false : _ ⟫                    ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ ite _ _ _ : _ ⟫                ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ pair _ _ : _ ⟫                 ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ proj₁ _ : _ ⟫                  ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ proj₂ _ : _ ⟫                  ] => econstructor *)
    | [ |- ⟪ _ i⊢ inl _ : _ ⟫                    ] => econstructor
    | [ |- ⟪ _ i⊢ inr _ : _ ⟫                    ] => econstructor
    | [ |- ⟪ _ i⊢ caseof _ _ _ : _ ⟫             ] => econstructor

    | [ |- ⟪ _ i⊢ fold_ _ : _ ⟫                  ] => econstructor
    | [ |- ⟪ _ i⊢ unfold_ _ : _ ⟫                ] => econstructor
    (* | [ |- ⟪ _ ⊢ seq _ _ : _ ⟫                  ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ fixt _ _ _ : _ ⟫               ] => econstructor *)
    | [ |- ⟪ i⊢ phole : _ , _ → _ , _ ⟫          ] => econstructor
    | [ |- ⟪ i⊢ pabs _ _ : _ , _ → _ , _ ⟫       ] => econstructor
    | [ |- ⟪ i⊢ papp₁ _ _ : _ , _ → _ , _ ⟫      ] => econstructor
    | [ |- ⟪ i⊢ papp₂ _ _ : _ , _ → _ , _ ⟫      ] => econstructor
    (* | [ |- ⟪ ⊢ pite₁ _ _ _ : _ , _ → _ , _ ⟫    ] => econstructor *)
    (* | [ |- ⟪ ⊢ pite₂ _ _ _ : _ , _ → _ , _ ⟫    ] => econstructor *)
    (* | [ |- ⟪ ⊢ pite₃ _ _ _ : _ , _ → _ , _ ⟫    ] => econstructor *)
    (* | [ |- ⟪ ⊢ ppair₁ _ _ : _ , _ → _ , _ ⟫     ] => econstructor *)
    (* | [ |- ⟪ ⊢ ppair₂ _ _ : _ , _ → _ , _ ⟫     ] => econstructor *)
    (* | [ |- ⟪ ⊢ pproj₁ _ : _ , _ → _ , _ ⟫       ] => econstructor *)
    (* | [ |- ⟪ ⊢ pproj₂ _ : _ , _ → _ , _ ⟫       ] => econstructor *)
    | [ |- ⟪ i⊢ pinl _ : _ , _ → _ , _ ⟫         ] => econstructor
    | [ |- ⟪ i⊢ pinr _ : _ , _ → _ , _ ⟫         ] => econstructor
    | [ |- ⟪ i⊢ pcaseof₁ _ _ _ : _ , _ → _ , _ ⟫ ] => econstructor
    | [ |- ⟪ i⊢ pcaseof₂ _ _ _ : _ , _ → _ , _ ⟫ ] => econstructor
    | [ |- ⟪ i⊢ pcaseof₃ _ _ _ : _ , _ → _ , _ ⟫ ] => econstructor
    (* | [ |- ⟪ ⊢ pseq₁ _ _ : _ , _ → _ , _ ⟫      ] => econstructor *)
    (* | [ |- ⟪ ⊢ pseq₂ _ _ : _ , _ → _ , _ ⟫      ] => econstructor *)
    (* | [ |- ⟪ ⊢ pfixt _ _ _ : _ , _ → _ , _ ⟫    ] => econstructor *)
    | [ |- ⟪ i⊢ pfold _ : _ , _ → _ , _ ⟫ ] => econstructor
    | [ |- ⟪ i⊢ punfold _ : _ , _ → _ , _ ⟫ ] => econstructor
  end.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushTypingMatchH);
  try discriminate;
  eauto with ws.

Lemma getEvar_wsIx Γ i T :
  ⟪ i : T i∈ Γ ⟫ → dom Γ ∋ i.
Proof. induction 1; crush. Qed.
Hint Resolve getEvar_wsIx : ws.

(* Lemma wsIx_getEvar {Γ i} (wi: dom Γ ∋ i) : *)
(*   ∀ (P: Prop), (∀ T, ⟪ i : T ∈ Γ ⟫ → P) → P. *)
(* Proof. *)
(*   depind wi; destruct Γ; crush. *)
(*   - eapply (IHwi _ x); crush. *)
(* Qed. *)

(* Lemma wtRen_wsRen Γ₁ Γ₂ ξ : *)
(*   WtRen Γ₁ Γ₂ ξ → WsRen (dom Γ₁) (dom Γ₂) ξ. *)
(* Proof. *)
(*   unfold WtRen, WsRen; intros. *)
(*   apply (wsIx_getEvar H0); crush. *)
(* Qed. *)

(* Lemma typing_wt {Γ t T} (wt: ⟪ Γ ⊢ t : T ⟫) : *)
(*   wsTm (dom Γ) t. *)
(* Proof. induction wt; crush. Qed. *)

(* Lemma wtSub_wsSub Γ₁ Γ₂ ζ : *)
(*   WtSub Γ₁ Γ₂ ζ → WsSub (dom Γ₁) (dom Γ₂) ζ. *)
(* Proof. *)
(*   unfold WtSub, WsSub; intros. *)
(*   apply (wsIx_getEvar H0); crush. *)
(*   eauto using typing_wt. *)
(* Qed. *)

(*************************************************************************)

Lemma wtRen_closed ξ Δ : WtRen empty Δ ξ.
Proof. unfold WtRen; intros. inversion H. Qed.
Hint Resolve wtRen_closed : ws.

Lemma wtRen_idm (Γ: Env) : WtRen Γ Γ (idm Ix).
Proof. unfold WtRen, idm; auto. Qed.
Hint Resolve wtRen_idm : ws.

Lemma wtRen_comp {Γ₁ Γ₂ Γ₃ ξ₁ ξ₂} :
  WtRen Γ₁ Γ₂ ξ₁ → WtRen Γ₂ Γ₃ ξ₂ → WtRen Γ₁ Γ₃ (ξ₁ >-> ξ₂).
Proof. unfold WtRen, comp; simpl; auto. Qed.
Hint Resolve wtRen_comp : ws.

(*************************************************************************)

Definition WtRenNatural (Γ₁ Γ₂: Env) (ξ₁ ξ₂: Sub Ix) : Prop :=
  ∀ i T, ⟪ (ξ₁ i) : T i∈ Γ₁ ⟫ → ⟪ (ξ₂ i) : T i∈ Γ₂ ⟫.

Lemma wtRen_natural
  {f₁ f₂: Env → Env} {ξ₁ ξ₂: Sub Ix}
  (hyp: ∀ Γ, WtRenNatural (f₁ Γ) (f₂ Γ) ξ₁ ξ₂) :
  ∀ Γ₁ Γ₂ ξ,
    WtRen Γ₁ (f₁ Γ₂) (ξ >-> ξ₁) →
    WtRen Γ₁ (f₂ Γ₂) (ξ >-> ξ₂).
Proof. unfold WtRenNatural, WtRen in *; eauto. Qed.

(*************************************************************************)

Lemma wtRen_wkms (Δ: Env) :
  ∀ Γ, WtRen Γ (Γ i▻▻ Δ) (wkms (dom Δ)).
Proof. unfold WtRen. induction Δ; crush. Qed.
Hint Resolve wtRen_wkms : ws.

Lemma wtiIx_wkms (Δ: Env) :
  ∀ (Γ: Env) (i: Ix) T,
    ⟪ (wkms (dom Δ) i) : T i∈ (Γ i▻▻ Δ) ⟫ → ⟪ i : T i∈ Γ ⟫.
Proof. induction Δ; eauto with wsi. Qed.
Hint Resolve wtiIx_wkms : wsi.

Lemma wtRen_wkm Γ T :
  WtRen Γ (Γ i▻ T) wkm.
Proof. apply (wtRen_wkms (empty i▻ T)). Qed.
Hint Resolve wtRen_wkm : ws.

Lemma wtiIx_wkm Γ i T :
  ⟪ (wkm i) : T i∈ (Γ i▻ T) ⟫ → ⟪ i : T i∈ Γ ⟫.
Proof. apply (wtiIx_wkms (empty i▻ T)). Qed.
Hint Resolve wtiIx_wkm : wsi.

Lemma wtRenNatural_wkms_id Δ :
  ∀ Γ, WtRenNatural (Γ i▻▻ Δ) Γ (wkms (dom Δ)) (idm Ix).
Proof. unfold WtRenNatural; eauto using wtiIx_wkms. Qed.
Hint Resolve wtRenNatural_wkms_id : wsi.

Lemma wtiRen_comp_wkms Δ :
  ∀ Γ₁ Γ₂ ξ,
    WtRen Γ₁ (Γ₂ i▻▻ Δ) (ξ >-> wkms (dom Δ)) →
    WtRen Γ₁ Γ₂        ξ.
Proof. apply (wtRen_natural (wtRenNatural_wkms_id Δ)). Qed.
Hint Resolve wtiRen_comp_wkms : wsi.

Lemma wtRen_snoc Γ₁ Γ₂ ξ x T :
  WtRen Γ₁ Γ₂ ξ → ⟪ x : T i∈ Γ₂ ⟫ → WtRen (Γ₁ i▻ T) Γ₂ (ξ · x).
Proof. unfold WtRen. crush. Qed.
Hint Resolve wtRen_snoc : ws.

Lemma wtiRen_snoc Γ₁ Γ₂ T ξ x :
  WtRen (Γ₁ i▻ T) Γ₂ (ξ · x) → WtRen Γ₁ Γ₂ ξ.
Proof.
  intros wξ i. specialize (wξ (S i)). eauto using GetEvar.
Qed.
Hint Resolve wtiRen_snoc : wsi.

Lemma wtiIx_snoc Γ₁ Γ₂ ξ T x :
  WtRen (Γ₁ i▻ T) Γ₂ (ξ · x) → ⟪ x : T i∈ Γ₂ ⟫.
Proof.
  intros wξ. specialize (wξ 0). eauto using GetEvar.
Qed.
Hint Resolve wtiIx_snoc : wsi.

Lemma wtRen_up {Γ₁ Γ₂ ξ} (wξ: WtRen Γ₁ Γ₂ ξ) :
  ∀ T, WtRen (Γ₁ i▻ T) (Γ₂ i▻ T) (ξ ↑).
Proof. unfold up; crush. Qed.
Hint Resolve wtRen_up : ws.

Lemma wtiRen_up Γ₁ Γ₂ ξ T :
  WtRen (Γ₁ i▻ T) (Γ₂ i▻ T) (ξ ↑) → WtRen Γ₁ Γ₂ ξ.
Proof.
  unfold up, WtRen. crush.
  specialize (H (S i) T0). eauto with ws wsi.
Qed.
Hint Resolve wtiRen_up : wsi.

Lemma wtRen_ups Γ₁ Γ₂ Δ ξ :
  WtRen Γ₁ Γ₂ ξ → WtRen (Γ₁ i▻▻ Δ) (Γ₂ i▻▻ Δ) (ξ ↑⋆ dom Δ).
Proof. induction Δ; crush. Qed.
Hint Resolve wtRen_ups : ws.

Lemma wtiRen_ups Γ₁ Γ₂ Δ ξ :
  WtRen (Γ₁ i▻▻ Δ) (Γ₂ i▻▻ Δ) (ξ ↑⋆ dom Δ) → WtRen Γ₁ Γ₂ ξ.
Proof. induction Δ; eauto with wsi. Qed.
Hint Resolve wtiRen_ups : wsi.

Lemma wtRen_beta (Γ Δ: Env) :
  ∀ ξ, WtRen Δ Γ ξ → WtRen (Γ i▻▻ Δ) Γ (beta (dom Δ) ξ).
Proof. unfold WtRen; induction Δ; crush. Qed.
Hint Resolve wtRen_beta : ws.

Lemma typing_ren {Γ₁ t T} (wt: ⟪ Γ₁ i⊢ t : T ⟫) :
  ∀ Γ₂ ξ, WtRen Γ₁ Γ₂ ξ → ⟪ Γ₂ i⊢ t[ξ] : T ⟫.
Proof. induction wt; econstructor; crush. Qed.
Hint Resolve typing_ren : ws.

(* Lemma typing_weakening Δ {Γ t T} (wt: ⟪ Γ ⊢ t : T ⟫) : *)
(*   ⟪ Γ ▻▻ Δ ⊢ t[@wkms Ix _ _ (dom Δ)] : T ⟫. *)
(* Proof. apply (typing_ren wt), wtRen_wkms. Qed. *)

(* Lemma typing_weakening1 T' {Γ t T} (wt: ⟪ Γ ⊢ t : T ⟫) : *)
(*   ⟪ Γ ▻ T' ⊢ t[@wkm Ix _ _] : T ⟫. *)
(* Proof. apply (typing_weakening (empty ▻ T') wt). Qed. *)

(*************************************************************************)

Lemma wtSub_closed ζ Δ : WtSub empty Δ ζ.
Proof. inversion 1. Qed.
Hint Resolve wtSub_closed : ws.

Lemma wtSub_idm (Γ: Env) : WtSub Γ Γ (idm Tm).
Proof. unfold WtSub. crush. Qed.
Hint Resolve wtSub_idm : ws.

Lemma wtSub_snoc Γ₁ Γ₂ ζ t T :
  WtSub Γ₁ Γ₂ ζ → ⟪ Γ₂ i⊢ t : T ⟫ → WtSub (Γ₁ i▻ T) Γ₂ (ζ · t).
Proof. unfold WtSub. crush. Qed.
Hint Resolve wtSub_snoc : ws.

Lemma wtiSub_snoc Γ₁ Γ₂ T ζ t :
  WtSub (Γ₁ i▻ T) Γ₂ (ζ · t) → WtSub Γ₁ Γ₂ ζ.
Proof.
  intros wζ i. specialize (wζ (S i)). eauto using GetEvar.
Qed.
Hint Resolve wtiSub_snoc : wsi.

Lemma wtSub_toSub ξ Γ₁ Γ₂ :
  WtRen Γ₁ Γ₂ ξ → WtSub Γ₁ Γ₂ ⌈ξ⌉.
Proof. unfold WtRen, WtSub; eauto using WtVar. Qed.

Lemma wtSub_wkms (Δ: Env) :
  ∀ Γ, WtSub Γ (Γ i▻▻ Δ) ⌈@wkms Ix _ _ (dom Δ)⌉.
Proof. eauto using wtRen_wkms, wtSub_toSub. Qed.
Hint Resolve wtSub_wkms : ws.

Lemma wtSub_wkm Γ T :
  WtSub Γ (Γ i▻ T) ⌈wkm⌉.
Proof. apply (wtSub_wkms (empty i▻ T)). Qed.
Hint Resolve wtSub_wkm : ws.

Lemma wtSub_up {Γ₁ Γ₂ ζ} (wζ: WtSub Γ₁ Γ₂ ζ) :
  ∀ T, WtSub (Γ₁ i▻ T) (Γ₂ i▻ T) (ζ ↑).
Proof. inversion 1; crush. Qed.
Hint Resolve wtSub_up : ws.

Lemma wtSub_ups Γ₁ Γ₂ Δ ζ :
  WtSub Γ₁ Γ₂ ζ → WtSub (Γ₁ i▻▻ Δ) (Γ₂ i▻▻ Δ) (ζ ↑⋆ dom Δ).
Proof. induction Δ; crush. Qed.
Hint Resolve wtSub_ups : ws.

Lemma typing_sub {Γ₁ t T} (wt: ⟪ Γ₁ i⊢ t : T ⟫) :
  ∀ Γ₂ ζ, WtSub Γ₁ Γ₂ ζ → ⟪ Γ₂ i⊢ t[ζ] : T ⟫.
Proof. induction wt; crush. Qed.
Hint Resolve typing_sub : ws.

Lemma wtSub_comp {Γ₁ Γ₂ Γ₃ ζ₁ ζ₂} :
  WtSub Γ₁ Γ₂ ζ₁ → WtSub Γ₂ Γ₃ ζ₂ → WtSub Γ₁ Γ₃ (ζ₁ >=> ζ₂).
Proof. unfold WtSub, comp; eauto with ws. Qed.
Hint Resolve wtSub_comp : ws.

Lemma wtiTm_snoc Γ₁ Γ₂ ζ T t :
  WtSub (Γ₁ i▻ T) Γ₂ (ζ · t) → ⟪ Γ₂ i⊢ t : T ⟫.
Proof.
  intros wζ. specialize (wζ 0). eauto using GetEvar.
Qed.
Hint Resolve wtiTm_snoc : wsi.

(*************************************************************************)

Lemma wtSub_beta (Γ Δ: Env) :
  ∀ ζ, WtSub Δ Γ ζ → WtSub (Γ i▻▻ Δ) Γ (beta (dom Δ) ζ).
Proof.
  unfold WtSub; induction Δ; crush.
Qed.
Hint Resolve wtSub_beta : ws.

Lemma wtSub_beta1 Γ t T (wi: ⟪ Γ i⊢ t : T ⟫) :
  WtSub (Γ i▻ T) Γ (beta1 t).
Proof. apply (wtSub_beta Γ (empty i▻ T)); crush. Qed.
Hint Resolve wtSub_beta1 : ws.

(*************************************************************************)

(* Lemma typing_beta {Γ Δ t T ζ} : *)
(*   WtSub Δ Γ ζ → ⟪ (Γ ▻▻ Δ) ⊢ t : T ⟫ → ⟪ Γ ⊢ t[beta (dom Δ) ζ] : T ⟫. *)
(* Proof. intros; eapply typing_sub; eauto with ws. Qed. *)

(* Lemma typing_beta1 {Γ t T t' T'} : *)
(*   ⟪ Γ ⊢ t' : T' ⟫ → ⟪ Γ ▻ T' ⊢ t : T ⟫ → ⟪ Γ ⊢ t[beta1 t'] : T ⟫. *)
(* Proof. intros; eapply typing_sub; eauto with ws. Qed. *)

(*************************************************************************)

Ltac crushTypingMatchH2 :=
  match goal with
    | [ |- ⟪ _ i⊢ @ap Tm Ix vrIx _ ?ξ ?t : _ ⟫
      ] => eapply typing_ren
    | [ |- ⟪ _ i⊢ @ap Tm Tm vrTm _ ?ζ ?t : _ ⟫
      ] => eapply typing_sub
    | [ |- WtSub (_ i▻ _) _ (beta _ _)
      ] => eapply wtSub_beta
    | [ |- WtSub (_ i▻ _) _ (beta1 _)
      ] => eapply wtSub_beta1
  end.

Ltac crushTyping :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasMatchH;
     repeat crushTypingMatchH;
     repeat crushTypingMatchH2;
     eauto with ws
    ).

Hint Extern 20 (⟪ _ i⊢ _ : _ ⟫) =>
  crushTyping : typing.

Hint Extern 20 (⟪ i⊢ _ : _ , _ → _ , _ ⟫) =>
  crushTyping : typing.

Hint Resolve pctxtyping_cat : typing.
Hint Resolve pctxtyping_app : typing.

Lemma wtvar_implies_wsvar {Γ i τ} :
  ⟪ i : τ i∈ Γ ⟫ → dom Γ ∋ i.
Proof.
  induction 1; eauto with ws.
Qed.

Lemma wt_implies_ws {Γ t τ} :
  ⟪ Γ i⊢ t : τ ⟫ → ⟨ dom Γ ⊢ t ⟩.
Proof.
  induction 1; constructor;
  eauto using wtvar_implies_wsvar with ws.
Qed.

Lemma closed_implies_not_var {i} :
  ClosedTy (tvar i) → False.
Proof.
  intros.
  inversion H.
  inversion H1.
Qed.


Lemma closed_implies_not_var_eq {τ} :
  ClosedTy τ → ∀ i : Ix, τ <> tvar i.
Proof.
  intros.
  intros contra.
  rewrite contra in H.
  exact (closed_implies_not_var H).
Qed.

Lemma closed_arr_implies_closed_argty {τ τ'} :
  ClosedTy (tarr τ τ') → ClosedTy τ.
Proof.
  inversion 1; assumption.
Qed.

Lemma closed_arr_implies_closed_retty {τ τ'} :
  ClosedTy (tarr τ τ') → ClosedTy τ'.
Proof.
  inversion 1; assumption.
Qed.

Lemma closed_arr_implies_closed_argty_eq {τ τ1 τ2} :
  ClosedTy τ →
  τ = tarr τ1 τ2 →
  ClosedTy τ1.
Proof.
  intros.
  rewrite H0 in H.
  exact (closed_arr_implies_closed_argty H).
Qed.

Lemma closed_arr_implies_closed_retty_eq {τ τ1 τ2} :
  ClosedTy τ →
  τ = tarr τ1 τ2 →
  ClosedTy τ2.
Proof.
  intros.
  rewrite H0 in H.
  exact (closed_arr_implies_closed_retty H).
Qed.

Lemma closed_sum_implies_closed_lhs {τ τ'} :
  ClosedTy (tsum τ τ') → ClosedTy τ.
Proof.
  inversion 1; assumption.
Qed.

Lemma closed_sum_implies_closed_rhs {τ τ'} :
  ClosedTy (tsum τ τ') → ClosedTy τ'.
Proof.
  inversion 1; assumption.
Qed.

Lemma closed_sum_implies_closed_lhs_eq {τ τ1 τ2} :
  ClosedTy τ →
  τ = tsum τ1 τ2 →
  ClosedTy τ1.
Proof.
  intros.
  rewrite H0 in H.
  exact (closed_sum_implies_closed_lhs H).
Qed.


Lemma closed_sum_implies_closed_rhs_eq {τ τ1 τ2} :
  ClosedTy τ →
  τ = tsum τ1 τ2 →
  ClosedTy τ2.
Proof.
  intros.
  rewrite H0 in H.
  exact (closed_sum_implies_closed_rhs H).
Qed.

Lemma closed_rec_implies_closed_unfold {τ} :
  ClosedTy (trec τ) → ClosedTy τ[beta1 (trec τ)].
Proof.
  intros.
  inversion H.
  induction τ.
  inversion H1.
  assert (H6 : ClosedTy (trec τ1)).
  constructor.
  assumption.
  assert (H7 : ClosedTy (trec τ2)).
  constructor.
  assumption.
  assert (H8 : ClosedTy τ1[beta1 (trec τ1)]).
  apply IHτ1.
  assumption.
  assert (H9 : ClosedTy τ2[beta1 (trec τ2)]).
  apply IHτ2.
  assumption.
Admitted.

Lemma closed_rec_implies_closed_unfold_eq {τ τ'} :
  ClosedTy τ →
  τ = trec τ' →
  ClosedTy τ'[beta1 (trec τ')].
Proof.
  intros.
  rewrite H0 in H.
  exact (closed_rec_implies_closed_unfold H).
Qed.


(* We want a simple way of proving that types are closed under reasonable circumstances (closed environments, etc.).

 This proof should be nasty and require us to insert various changes into the basic structures (i.e. the abs term constructor will require proof that the argument type is closed), so we admit for now as it is obviously valid (with the appropriate changes to terms and environments) and tangential to the rest of the proof. *)
Lemma typed_terms_are_closed {Γ} (t : Tm) (T : Ty) :
  (* ClosedEnv Γ → *) (* will need this later, but for now it makes our life difficult as we don't have the mechanisms to easily prove this fact about environments *)
  ⟪ Γ i⊢ t : T ⟫ →
  ClosedTy T.
Proof.
  intros.
  induction H.
Admitted.
(*   inversion τ. *)
(*   induction τ. *)
(*   crushTypingMatchH. *)
(*   induction H. *)
(*   induction τ. *)
(*   rewrite H2 in IHτ1. *)
(*   rewrite H2 in IHτ2. *)
(* Admitted. *)

