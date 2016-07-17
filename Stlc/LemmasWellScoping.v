Require Export Stlc.SpecSyntax.
Require Export Stlc.LemmasSyntaxBasic.

Lemma wsiS (γ: Dom) (i: Ix) : S γ ∋ S i → γ ∋ i.
Proof. inversion 1; auto. Qed.
Hint Resolve wsiS : wsi.

Ltac crushScopingMatchH :=
  match goal with
    | [ H: 0 ∋ _                 |- _ ] => inversion H
    | [ H: S _    ∋ O            |- _ ] => clear H
    | [ H: S _ ∋ S _             |- _ ] => apply wsiS in H
    | [ wi : S _ ∋ ?i
        |- context [match ?i with _ => _ end]
      ] => destruct i
    | [ wi : S _ ∋ ?i
        |- context [match wkr _ ?i with _ => _ end]
      ] => destruct i
    | [ wi : S _ ∋ ?i
        |- context [(_ · _) ?i]
      ] => destruct i
    | [ |- S _ ∋ 0               ] => apply ws0
    | [ |- S _ ∋ S _             ] => apply wsS
    | [ |- WsRen _ (_ · _)       ] => constructor
    | [ |- wsTm _ (var _)        ] => constructor
    | [ |- wsTm _ (abs _ _)      ] => constructor
    | [ |- wsTm _ (app _ _)      ] => constructor
    | [ |- wsTm _ unit           ] => constructor
    | [ |- wsTm _ true           ] => constructor
    | [ |- wsTm _ false          ] => constructor
    | [ |- wsTm _ (ite _ _ _)    ] => constructor
    | [ |- wsTm _ (pair _ _)     ] => constructor
    | [ |- wsTm _ (proj₁ _)      ] => constructor
    | [ |- wsTm _ (proj₂ _)      ] => constructor
    | [ |- wsTm _ (inl _)        ] => constructor
    | [ |- wsTm _ (inr _)        ] => constructor
    | [ |- wsTm _ (caseof _ _ _) ] => constructor
    | [ |- wsTm _ (seq _ _)      ] => constructor
    | [ |- wsTm _ (fixt _ _ _)   ] => constructor
  end.

Ltac crush :=
  intros;
  repeat
    (cbn in *;
     repeat crushRewriteH;
     repeat crushScopingMatchH);
  eauto with ws.

Lemma wsIx_plus_dec {γ δ i} (wi: γ ∪ δ ∋ i) :
  ∀ (P: Prop),
    (∀ j, γ ∋ j → wkl δ j = i → P) →
    (∀ j, δ ∋ j → wkr γ j = i → P) → P.
Proof with cbn in *; subst; eauto using wsIx.
  depind wi; destruct δ...
  eapply IHwi; intros...
Qed.

Lemma wsIx_plus_dec' {γ δ i} (wi: γ ∪ δ ∋ i) :
  (∃ j, γ ∋ j ∧ wkl δ j = i) ∨
  (∃ j, δ ∋ j ∧ wkr γ j = i).
Proof. apply (wsIx_plus_dec wi); eauto. Qed.

Hint Constructors wsIx : ws.
Hint Constructors wsTm : ws.

(********************************************************************)

Lemma wsIx_wkl (δ: Dom) :
  ∀ (γ: Dom) (i: Ix), γ ∋ i → (γ ∪ δ) ∋ (wkl δ i).
Proof. induction δ; eauto using wsIx. Qed.
Hint Resolve wsIx_wkl : ws.

Lemma wsRen_wkl (δ: Dom) :
  ∀ γ, WsRen γ (γ ∪ δ) (wkl δ).
Proof. unfold WsRen. auto using wsIx_wkl. Qed.
Hint Resolve wsRen_wkl : ws.

Lemma wsRen_wkl1 :
  ∀ γ, WsRen γ (S γ) (wkl 1).
Proof. apply (wsRen_wkl 1). Qed.
Hint Resolve wsRen_wkl1 : ws.

Lemma wsiIx_wkl (δ: Dom) :
  ∀ (γ: Dom) (i: Ix), (γ ∪ δ) ∋ (wkl δ i) → γ ∋ i.
Proof. induction δ; eauto using wsIx, wsiS. Qed.
Hint Resolve wsiIx_wkl : wsi.

Lemma wsiIx_wkl1 :
  ∀ (γ: Dom) (i: Ix), (S γ) ∋ (wkl 1 i) → γ ∋ i.
Proof. apply (wsiIx_wkl 1). Qed.
Hint Resolve wsiIx_wkl : wsi.

(********************************************************************)

Lemma wsIx_wkr (γ: Dom) :
  ∀ δ i, δ ∋ i → (γ ∪ δ) ∋ (wkr γ i).
Proof. induction 1; cbn; auto using wsIx. Qed.
Hint Resolve wsIx_wkr : ws.

(** Unfortunately the representation is too weak for this. *)
Lemma wsiIx_wkr (γ: Dom) :
  ∀ δ i, (γ ∪ δ) ∋ (wkr γ i) → δ ∋ i.
Abort.

Lemma wsRen_wkr γ :
  ∀ δ, WsRen δ (γ ∪ δ) (wkr γ).
Proof.
  unfold WsRen; induction 1; cbn; auto using wsIx.
Qed.
Hint Resolve wsRen_wkr : ws.

(********************************************************************)

Lemma wsRen_snoc γ₁ γ₂ ξ x :
  WsRen γ₁ γ₂ ξ → γ₂ ∋ x → WsRen (S γ₁) γ₂ (ξ · x).
Proof. unfold WsRen; crush. Qed.
Hint Resolve wsRen_snoc : ws.

Lemma wsiRenSnoc γ₁ γ₂ ξ x :
  WsRen (S γ₁) γ₂ (ξ · x) → WsRen γ₁ γ₂ ξ.
Proof.
  intros wsξ i. specialize (wsξ (S i)). crush.
Qed.
Hint Resolve wsiRenSnoc : wsi.

Lemma wsiIxSnoc γ₁ γ₂ ξ x :
  WsRen (S γ₁) γ₂ (ξ · x) → γ₂ ∋ x.
Proof.
  intros wsξ. specialize (wsξ 0). eauto with ws wsi.
Qed.
Hint Resolve wsiIxSnoc : wsi.

(********************************************************************)

Definition WsRenNatural (γ₁ γ₂: Dom) (ξ₁ ξ₂ : Ren) : Prop :=
  ∀ i, γ₁ ∋ ξ₁ i → γ₂ ∋ ξ₂ i.

Lemma wsRenNat_comp
  {f₁ f₂ f₃: Dom → Dom} {ξ₁ ξ₂ ξ₃: Ren}
  (H₁₂: ∀ γ, WsRenNatural (f₁ γ) (f₂ γ) ξ₁ ξ₂)
  (H₂₃: ∀ γ, WsRenNatural (f₂ γ) (f₃ γ) ξ₂ ξ₃) :
  ∀ γ, WsRenNatural (f₁ γ) (f₃ γ) ξ₁ ξ₃.
Proof. unfold WsRenNatural in *; eauto. Qed.

Lemma wsRen_natural'
  {f₁ f₂: Dom → Dom} {ξ₁ ξ₂: Ren}
  (hyp: ∀ γ, WsRenNatural (f₁ γ) (f₂ γ) ξ₁ ξ₂) :
  ∀ γ₁ γ₂,
    WsRen γ₁ (f₁ γ₂) ξ₁ →
    WsRen γ₁ (f₂ γ₂) ξ₂.
Proof. unfold WsRenNatural, WsRen in *; eauto. Qed.

Lemma wsRen_natural
  {f₁ f₂: Dom → Dom} {ξ₁ ξ₂: Ren}
  (hyp: ∀ γ, WsRenNatural (f₁ γ) (f₂ γ) ξ₁ ξ₂) ξ :
  ∀ γ₁ γ₂,
    WsRen γ₁ (f₁ γ₂) (ξ >-> ξ₁) →
    WsRen γ₁ (f₂ γ₂) (ξ >-> ξ₂).
Proof. eapply wsRen_natural'; unfold WsRenNatural in *; eauto. Qed.

Lemma wsRen_id (γ: Dom) : WsRen γ γ ren_id.
Proof. unfold WsRen, ren_id; auto. Qed.
Hint Resolve wsRen_id : ws.

Lemma wsRen_comp {γ₁ γ₂ γ₃ ξ₁ ξ₂} :
  WsRen γ₁ γ₂ ξ₁ → WsRen γ₂ γ₃ ξ₂ → WsRen γ₁ γ₃ (ξ₁ >-> ξ₂).
Proof. unfold WsRen, ren_comp; auto. Qed.
Hint Resolve wsRen_comp : ws.

Lemma wsRen_closed ξ δ : WsRen 0 δ ξ.
Proof. unfold WsRen; inversion 1. Qed.
Hint Resolve wsRen_closed : ws.

Lemma wsRenNatural_wkl_id δ :
  ∀ γ, WsRenNatural (γ ∪ δ) γ (wkl δ) ren_id.
Proof. unfold WsRenNatural; eauto using wsiIx_wkl. Qed.
Hint Resolve wsRenNatural_wkl_id : wsi.

Lemma wsiRen_comp_wkl δ ξ :
  ∀ γ₁ γ₂,
    WsRen γ₁ (γ₂ ∪ δ) (ξ >-> wkl δ) →
    WsRen γ₁ γ₂        ξ.
Proof. apply (wsRen_natural (wsRenNatural_wkl_id δ)). Qed.
Hint Resolve wsiRen_comp_wkl : wsi.

(******************************************************************************)

Lemma wsRen_up γ₁ γ₂ ξ :
  WsRen γ₁ γ₂ ξ → WsRen (S γ₁) (S γ₂) (ξ ↑).
Proof. unfold up, ren_up; crush. Qed.
Hint Resolve wsRen_up : ws.

Lemma wsiRen_up γ₁ γ₂ ξ :
  WsRen (S γ₁) (S γ₂) (ξ ↑) → WsRen γ₁ γ₂ ξ.
Proof.
  unfold WsRen, up, ren_up; crush.
  specialize (H (S i)); eauto with ws wsi.
Qed.
Hint Resolve wsiRen_up : wsi.

Lemma wsRen_ups γ₁ γ₂ δ ξ :
  WsRen γ₁ γ₂ ξ → WsRen (γ₁ ∪ δ) (γ₂ ∪ δ) (ξ ↑⋆ δ).
Proof. induction δ; crush. Qed.
Hint Resolve wsRen_ups : ws.

Lemma wsiRen_ups γ₁ γ₂ δ ξ :
  WsRen (γ₁ ∪ δ) (γ₂ ∪ δ) (ξ ↑⋆ δ) → WsRen γ₁ γ₂ ξ.
Proof. induction δ; auto with wsi. Qed.
Hint Resolve wsiRen_ups : wsi.

(******************************************************************************)

Lemma wsRen_ren_beta (γ δ: Dom) :
  ∀ ξ, WsRen δ γ ξ → WsRen (γ ∪ δ) γ (ren_beta δ ξ).
Proof. unfold WsRen; induction δ; crush. Qed.
Hint Resolve wsRen_ren_beta : ws.

(******************************************************************************)

Lemma wsRenNatural_up (γ₁ γ₂: Dom) (ξ₁ ξ₂: Ren) :
  WsRenNatural γ₁ γ₂ ξ₁ ξ₂ →
  WsRenNatural (S γ₁) (S γ₂) (ξ₁ ↑) (ξ₂ ↑).
Proof. intros H i; destruct i; crush. Qed.
Hint Resolve wsRenNatural_up : ws.

Lemma wsRenNatural_ups δ :
  ∀ (γ₁ γ₂: Dom) (f g: Ix → Ix) (wfg: WsRenNatural γ₁ γ₂ f g),
    WsRenNatural (γ₁ ∪ δ) (γ₂ ∪ δ) (f ↑⋆ δ) (g ↑⋆ δ).
Proof. induction δ; crush. Qed.
Hint Resolve wsRenNatural_ups : ws.

Lemma wsTm_renTm γ t (wt: wsTm γ t) :
  ∀ ξ δ, WsRen γ δ ξ → wsTm δ (t[ξ]).
Proof. induction wt; crush. Qed.
Hint Resolve wsTm_renTm : ws.

Lemma wsTm_natural t :
  ∀ γ δ ξ₁ ξ₂ (wξ: WsRenNatural γ δ ξ₁ ξ₂),
    wsTm γ t[ξ₁] → wsTm δ t[ξ₂].
Proof.
  induction t; cbn; intros γ δ ξ₁ ξ₂ wξ wt;
    inversion wt; subst; cbn; constructor; crush.
Qed.

Lemma wsiTm_wkl δ γ t :
  wsTm (γ ∪ δ) (t[wkl δ]) → wsTm γ t.
Proof.
  replace (wsTm γ t) with (wsTm γ (t[ren_id])).
  apply wsTm_natural; auto with wsi.
  crush.
Qed.
Hint Resolve wsiTm_wkl : wsi.

Lemma wsiTm_wkl1 γ t :
  wsTm (S γ) (t[wkl 1]) → wsTm γ t.
Proof. apply (wsiTm_wkl 1). Qed.
Hint Resolve wsiTm_wkl1 : wsi.

(*************************************************************************)

Lemma wsSub_natural
  {f₁ f₂: Dom → Dom} {ξ₁ ξ₂: Ren}
  (hyp: ∀ γ, WsRenNatural (f₁ γ) (f₂ γ) ξ₁ ξ₂) :
  ∀ γ₁ γ₂ ζ,
    WsSub γ₁ (f₁ γ₂) (sub_comp_ren ζ ξ₁) →
    WsSub γ₁ (f₂ γ₂) (sub_comp_ren ζ ξ₂).
Proof. unfold WsSub, sub_comp_ren in *; eauto using wsTm_natural. Qed.

Lemma wsSub_closed ζ δ : WsSub 0 δ ζ.
Proof. unfold WsSub; crush. Qed.
Hint Resolve wsSub_closed : ws.

Lemma wsSub_id (γ: Dom) : WsSub γ γ sub_id.
Proof. unfold WsSub, sub_id; crush. Qed.
Hint Resolve wsSub_id : ws.

Lemma wsSub_sub_comp_ren γ₁ γ₂ γ₃ ζ ξ :
  WsSub γ₁ γ₂ ζ → WsRen γ₂ γ₃ ξ → WsSub γ₁ γ₃ (sub_comp_ren ζ ξ).
Proof. unfold WsSub, sub_comp_ren; crush. Qed.
Hint Resolve wsSub_sub_comp_ren : ws.

Lemma wsiSub_comp_wkl' ζ δ γ₁ γ₂ :
  WsSub γ₁ (γ₂ ∪ δ) (sub_comp_ren ζ (wkl δ)) →
  WsSub γ₁ γ₂       (sub_comp_ren ζ ren_id).
Proof. apply (wsSub_natural (wsRenNatural_wkl_id δ)). Qed.

Lemma wsiSub_comp_wkl ζ δ γ₁ γ₂ :
  WsSub γ₁ (γ₂ ∪ δ) (sub_comp_ren ζ (wkl δ)) →
  WsSub γ₁ γ₂       ζ.
Proof.
  pose proof (wsiSub_comp_wkl' ζ).
  specialize (H δ γ₁ γ₂). crush.
Qed.
Hint Resolve wsiSub_comp_wkl : wsi.

Lemma wsiSub_comp_wkl1 ζ γ₁ γ₂ :
  WsSub γ₁ (S γ₂) (sub_comp_ren ζ (wkl 1)) →
  WsSub γ₁ γ₂     ζ.
Proof. apply (wsiSub_comp_wkl ζ 1). Qed.
Hint Resolve wsiSub_comp_wkl1 : wsi.

Lemma wsSub_snoc γ₁ γ₂ ζ t :
  WsSub γ₁ γ₂ ζ → wsTm γ₂ t → WsSub (S γ₁) γ₂ (ζ · t).
Proof. unfold WsSub; crush. Qed.
Hint Resolve wsSub_snoc : ws.

Lemma wsiSubSnoc γ₁ γ₂ ζ x :
  WsSub (S γ₁) γ₂ (ζ · x) → WsSub γ₁ γ₂ ζ.
Proof. intros wζ i. specialize (wζ (S i)). crush. Qed.
Hint Resolve wsiSubSnoc : wsi.

Lemma wsiTmSnoc γ₁ γ₂ ζ t :
  WsSub (S γ₁) γ₂ (ζ · t) → wsTm γ₂ t.
Proof. intros wζ. specialize (wζ 0). crush. Qed.
Hint Resolve wsiTmSnoc : wsi.

Lemma wsSub_up γ₁ γ₂ ζ :
  WsSub γ₁ γ₂ ζ → WsSub (S γ₁) (S γ₂) (ζ ↑).
Proof.
  unfold up, sub_up, WsSub; crush.
Qed.
Hint Resolve wsSub_up : ws.

Lemma wsiSub_up γ₁ γ₂ ζ :
  WsSub (S γ₁) (S γ₂) (ζ ↑) → WsSub γ₁ γ₂ ζ.
Proof. eauto with wsi. Qed.
Hint Resolve wsiSub_up : wsi.

Lemma wsSub_ups γ₁ γ₂ δ ζ :
  WsSub γ₁ γ₂ ζ → WsSub (γ₁ ∪ δ) (γ₂ ∪ δ) (ζ ↑⋆ δ).
Proof. induction δ; crush. Qed.
Hint Resolve wsSub_ups : ws.

Lemma wsiSub_ups γ₁ γ₂ δ ζ :
  WsSub (γ₁ ∪ δ) (γ₂ ∪ δ) (ζ ↑⋆ δ) → WsSub γ₁ γ₂ ζ.
Proof. induction δ; auto with wsi. Qed.
Hint Resolve wsiSub_ups : wsi.

(*************************************************************************)

Lemma wsTm_subTm γ t (wt: wsTm γ t) :
  ∀ ζ δ, WsSub γ δ ζ → wsTm δ (t[ζ]).
Proof. induction wt; crush. Qed.
Hint Resolve wsTm_subTm : ws.

(*************************************************************************)

Lemma wsSub_comp {γ₁ γ₂ γ₃ ζ₁ ζ₂} :
  WsSub γ₁ γ₂ ζ₁ → WsSub γ₂ γ₃ ζ₂ → WsSub γ₁ γ₃ (ζ₁ >=> ζ₂).
Proof. unfold WsSub, sub_comp; crush. Qed.
Hint Resolve wsSub_comp : ws.

Lemma wsSub_sub_beta (γ δ: Dom) :
  ∀ ζ, WsSub δ γ ζ → WsSub (γ ∪ δ) γ (sub_beta δ ζ).
Proof.
  unfold WsSub; induction δ; crush.
  destruct i; crush. eapply IHδ; crush.
Qed.
Hint Resolve wsSub_sub_beta : ws.

Lemma wsSub_sub_beta1 γ t (wt: wsTm γ t) :
  WsSub (S γ) γ (sub_beta1 t).
Proof. apply (wsSub_sub_beta γ 1); crush. Qed.
Hint Resolve wsSub_sub_beta1 : ws.

(* Local Variables: *)
(* coq-load-path: (("." "Stlc")) *)
(* End: *)
