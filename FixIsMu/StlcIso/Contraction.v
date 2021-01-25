Require Export StlcIso.Inst.
Require Export StlcIso.SpecSyntax.
Require Export StlcIso.SpecTyping.
Require Coq.Program.Tactics.
Require Coq.Program.Wf.
Require Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import FunInd.
Require Import Recdef.
Require Import Db.Lemmas.

Require Import Lia.

Fixpoint LMC (τ : Ty) {struct τ} : nat :=
  match τ with
  | trec τ => S (LMC τ)
  | _ => 0
  end.

Inductive Contr : Ty → Prop :=
  | ContrPrim : Contr tunit
  | ContrArr {τ τ'} : Contr (tarr τ τ')
  | ContrSum {τ τ'} : Contr (tsum τ τ')
  | ContrRec {τ} :
      Contr τ →
      Contr (trec τ).

Lemma lmc_invar_subst : ∀ (τ : Ty) (ξ : Sub Ty), Contr τ → LMC τ = LMC (τ[ξ]).
Proof.
  intros.
  revert ξ.
  induction H.
  constructor.
  constructor.
  constructor.
  simpl.
  intros.
  specialize (IHContr ξ↑).
  eauto.
Qed.

Lemma contr_implies_contr_unroll (τ : Ty) (P : Contr (trec τ)) : Contr (τ[beta1 (trec τ)]).
  inversion P.
  subst.
  (* Clear out hypothesis so it dosn't mess up the induction *)
  clear P.
  (* Generalize the substitution *)
  remember (beta1 (trec τ)) as ξ.
  (* Get rid of equality so induction is general (and thus IH is stronger) *)
  clear Heqξ.
  (* Put ξ back in goal so it is inducted upon *)
  revert ξ.
  induction H0;
  constructor.
  apply IHContr.
Qed.

Program Fixpoint fu (τ : Ty) (P : Contr τ) {measure (LMC τ)} : Ty :=
  match τ with
  | trec τ' => fu τ'[beta1 (trec τ')] _
  | _ => τ
  end.
Next Obligation.
  exact (contr_implies_contr_unroll τ' P).
Qed.
Next Obligation.
  inversion P.
  rewrite <- ?(lmc_invar_subst τ' (beta1 (trec τ')) H0).
  constructor.
Qed.


Fixpoint fu_accum (τ : Ty) (current_sub : Sub Ty) {struct τ} : Ty :=
  match τ with
    | trec τ => fu_accum τ (comp (up current_sub) (beta1 (trec τ)[current_sub]))
    | _ => τ[current_sub]
  end.

Definition fu' (τ : Ty) := fu_accum τ (idm Ty).


Eval compute in (fu' (trec (tsum (tvar 0) tunit))).
Eval compute in (fu' (trec (trec (tsum (tvar 0) tunit)))).
Compute (fu' (trec (trec (tsum (tvar 1) (tvar 0))))).

Functional Scheme fu_accum_ind := Induction for fu_accum Sort Prop.
Functional Scheme lmc_ind := Induction for LMC Sort Prop.
(* Functional Scheme fu_func_ind := Induction for fu_func Sort Prop. *)

(* Check fu_ind. *)


Lemma contr_implies_contr_fu (τ : Ty) (P : Contr τ) : Contr (fu' τ).
Proof.
  unfold fu'.
  generalize (idm Ty).
  induction P; cbn;
  constructor || intuition.
Qed.

(* simple recursive type: *)
(*   α | τ_contr *)


(* τ_contr: *)
(* tunit *)
(* simple => simple *)
(* μ α . τ_contr *)



Inductive SimpleContr : Ty → Prop :=
| SimpContrPrim : SimpleContr tunit
| SimpContrArrow {τ τ'} : SimpleRec τ → SimpleRec τ' → SimpleContr (tarr τ τ')
| SimpContrSum {τ τ'} : SimpleRec τ → SimpleRec τ' → SimpleContr (tsum τ τ')
| SimpContrRec {τ} : SimpleContr τ → SimpleContr (trec τ)
with SimpleRec : Ty → Prop :=
| SimpleAlpha {i} : SimpleRec (tvar i)
| SimpleRecContr {τ} : SimpleContr τ → SimpleRec τ.

Scheme simp_contr_mut_ind := Induction for SimpleContr Sort Prop
  with simp_rec_mut_ind := Induction for SimpleRec Sort Prop.

Combined Scheme simp_contr_comb_ind from simp_contr_mut_ind, simp_rec_mut_ind.

Definition SimpleContrSub (ξ : Sub Ty) : Prop := forall i : Ix, SimpleContr (ξ i).
Definition SimpleRecSub (ξ : Sub Ty) : Prop := forall i : Ix, SimpleRec (ξ i).

Lemma SimpleContrSub_implies_SimpleRecSub {ξ} : SimpleContrSub ξ → SimpleRecSub ξ.
Proof.
  unfold SimpleContrSub, SimpleRecSub.
  intros.
  specialize (H i).
  exact (SimpleRecContr H).
Qed.

Lemma SimpleContrSub_comp {ξ δ} : SimpleContrSub ξ → SimpleContrSub (δ >-> ξ).
Proof.
  unfold SimpleContrSub.
  intros.
  unfold fcomp.
  exact (H (δ i)).
Qed.

Lemma SimpleRecSub_comp {ξ δ} : SimpleRecSub ξ → SimpleRecSub (δ >-> ξ).
Proof.
  unfold SimpleRecSub.
  intros.
  unfold fcomp.
  exact (H (δ i)).
Qed.

Lemma SimpleContr_implies_SimpleRec {τ} : SimpleContr τ → SimpleRec τ.
Proof.
  apply SimpleRecContr.
Qed.

Lemma SimpleRecSub_wkm : SimpleRecSub wkm.
Proof.
  unfold SimpleRecSub; cbn; constructor.
Qed.

Lemma SimpleRec_implies_SimpleRecSub_snoc {ξ τ} : SimpleRecSub ξ → SimpleRec τ → SimpleRecSub (ξ · τ).
Proof.
  unfold SimpleRecSub, snoc.
  intros.
  destruct i;
  intuition.
Qed.

Lemma SimpleContr_implies_SimpleContrSub_snoc {ξ τ} : SimpleContrSub ξ → SimpleContr τ → SimpleContrSub (ξ · τ).
Proof.
  unfold SimpleContrSub, snoc.
  intros.
  destruct i;
  intuition.
Qed.

(* Lemma SimpleRecSub_Left_comp {ξ δ} : SimpleRecSub ξ → SimpleRecSub (ξ >-> δ). *)
(* Proof. *)
(*   unfold SimpleRecSub. *)
(*   intros. *)
(*   cbn. *)
(*   specialize (H i). *)
(*   inversion H. *)

Compute (wk (trec (tsum tunit (tvar 0)))).
Compute (wk tunit).
Compute (wk (tarr tunit (tvar 0))).
Compute ((tvar 0)[wk↑]).
Compute ((tvar 1)[wk↑]).

(* Due to definition of wk and up this seems to be cyclic with SimpleRecSubUp *)
Lemma SimpleRec_wk {τ} : SimpleRec τ → SimpleRec τ[wk]
with SimpleContr_wk {τ} : SimpleContr τ → SimpleContr τ[wk].
Proof.
  (* change τ[wk] with (wk τ). *)
  (* rewrite ap_wk. *)
  (* intros. *)

  induction τ; cbn; intros;
  repeat change (apTy ?ξ ?τ) with τ[ξ].

  inversion H.
  inversion H0.
  specialize (IHτ1 H4).
  specialize (IHτ2 H5).
  constructor.
  constructor; assumption.

  constructor.
  constructor.

  inversion H.
  inversion H0.
  specialize (IHτ1 H4).
  specialize (IHτ2 H5).
  constructor.
  constructor; assumption.

  (* constructor. *)
  (* constructor. *)


  (* apply SimpleRec_implies_SimpleRecSub_snoc. *)


  (* inversion H. *)
  (* inversion H0. *)
  (* pose proof (SimpleRecContr H3). *)
  (* specialize (IHτ H4). *)
  (* constructor. *)
  (* constructor. *)

  (* (* remember wk↑ as ξ. *) *)
  (* rewrite <- ap_wk. *)
  (* unfold up. *)

Admitted.
  (* apply SimpleRec_implies_SimpleRecSub_snoc. *)
  (* assumption. *)
  (* unfold up, fcomp, snoc. *)
  (* change ?τ[?ξ] with (apTy ξ τ). *)
  (* unfold apTy. *)
  (* destruct Heqξ. *)
  (* unfold fcomp. *)
  (* unfold snoc. *)

(* Admitted. *)
  (* extensionality i. *)




  (* apply (simp_rec_mut_ind *)
  (*          (fun {τ} (_ : SimpleContr τ) => (SimpleContr τ → SimpleContr τ[wk])) *)
  (*          (fun {τ} (_ : SimpleRec τ) => (SimpleRec τ → SimpleRec τ[wk]))); *)
  (*   cbn; intros. *)
  (* constructor. *)
  (* inversion H1. *)
  (* constructor; intuition. *)
  (* inversion H1. *)
  (* constructor; intuition. *)
  (* crushDbSyntaxMatchH. *)
  (* constructor. *)
  (* unfold up. *)
  (* Admitted. *)

(*   unfold apTy. *)
(*   apply SimpleRec_implies_SimpleRecSub_snoc. *)
(*   induction τ0; cbn. *)


(*   crushRewriter. *)
(*   destruct τ; cbn. *)
(*   4: { *)
(*     crushRewriter. *)
(*     crushDbLemmasRewriteH. *)
(*     crushDbLemmasMatchH. *)
(*   } *)



(*   induction 1; cbn. *)
(*   constructor. *)
(*   inversion H. *)
(*   4: { *)
(*     crushDbLemmasRewriteH. *)
(*     cbn. *)
(*     constructor. *)
(*     constructor. *)
(*   } *)


(*   induction τ. *)
(*   constructor; constructor; assumption. *)
(*   constructor; constructor. *)
(*   constructor; constructor; assumption. *)
(*   constructor; constructor. *)

(* Lemma SimpleContr_wk {τ} : SimpleContr τ → SimpleContr τ[wk]. *)
(* Proof. *)
(*   apply (simp_contr_mut_ind *)
(*            (fun {τ} (_ : SimpleContr τ) => (SimpleContr τ → SimpleContr τ[wk])) *)
(*            (fun {τ} (_ : SimpleRec τ) => (SimpleRec τ → SimpleRec τ[wk]))); *)
(*     cbn; intros. *)
(*   constructor. *)
(*   inversion H1. *)
(*   constructor; intuition. *)
(*   inversion H1. *)
(*   constructor; intuition. *)
(*   crushDbSyntaxMatchH. *)
(*   constructor. *)
(*   specialize (H s). *)
(*   repeat change (apTy ?ξ ?τ) with τ[ξ]. *)
(* Admitted. *)


Lemma SimpleRecSub_implies_SimpleRecSubUp {ξ} : SimpleRecSub ξ → SimpleRecSub (up ξ).
Proof.
  unfold SimpleRecSub.
  intros.

  destruct i; cbn.
  constructor.

  apply SimpleRec_wk.
  exact (H i).
Qed.

(* Lemma SimpleContrSub_implies_SimpleRecSubUp {ξ} : SimpleContrSub ξ → SimpleContrSub (up ξ). *)
(* Proof. *)
(*   unfold up. *)
(*   intros. *)
(*   apply SimpleContr_implies_SimpleContrSub_snoc. *)
(*   unfold fcomp, SimpleContrSub in *. *)
(*   intros. *)
(*   apply SimpleContr_wk. *)
(*   intuition. *)
(*   cbn. *)
(*   constructor. *)
(* Qed. *)

Lemma SimpleRecSub_implies_SimpleRec {τ ξ} : SimpleRec τ → SimpleRecSub ξ → SimpleRec τ[ξ].
Proof.
  intro H.
  apply (simp_rec_mut_ind
           (fun {τ} (_ : SimpleContr τ) => (forall ξ : Sub Ty, SimpleRecSub ξ → SimpleContr τ[ξ]))
           (fun {τ} (_ : SimpleRec τ) => (forall ξ : Sub Ty, SimpleRecSub ξ → SimpleRec τ[ξ]))).
  cbn.
  constructor.
  cbn.
  intros.
  constructor; intuition.
  apply H0.
  assumption.
  apply H1.
  assumption.
  cbn.
  intros.
  constructor; intuition.
  apply H0.
  assumption.
  apply H1.
  assumption.
  cbn.
  intros.
  constructor.
  eauto using H0, SimpleRecSub_implies_SimpleRecSubUp.

  intros.
  apply H0.

  intros.
  eauto using SimpleRecContr.

  assumption.
Qed.

Check simp_contr_mut_ind.

Lemma SimpleContrSub_implies_SimpleContr {τ ξ} : SimpleContr τ → SimpleRecSub ξ → SimpleContr τ[ξ].
  intro H.
  apply (simp_contr_mut_ind
           (fun {τ} (_ : SimpleContr τ) => (forall ξ : Sub Ty, SimpleRecSub ξ → SimpleContr τ[ξ]))
           (fun {τ} (_ : SimpleRec τ) => (forall ξ : Sub Ty, SimpleRecSub ξ → SimpleRec τ[ξ]))).
  cbn.
  constructor.

  intros.
  cbn.
  constructor.
  apply H0.
  assumption.
  apply H1.
  assumption.

  intros.
  cbn.
  constructor.
  apply H0.
  assumption.
  apply H1.
  assumption.

  intros.
  cbn.
  constructor.
  apply H0.
  apply SimpleRecSub_implies_SimpleRecSubUp.
  assumption.

  intros.
  cbn.
  exact (H0 i).

  intros.
  specialize (H0 ξ0).
  apply SimpleRecSub_implies_SimpleRec.
  apply SimpleRecContr.
  assumption.

  assumption.
  assumption.
Qed.

Lemma idm_contr_sub : SimpleRecSub (idm Ty).
Proof.
  unfold SimpleRecSub; cbn.
  constructor.
Qed.

Lemma SimpleRecSub_compose {ξ ζ} : SimpleRecSub ξ → SimpleRecSub ζ → SimpleRecSub (ξ >=> ζ).
Proof.
  unfold SimpleRecSub.
  intros.
  unfold comp.
  unfold ap.
  cbn.
  apply SimpleRecSub_implies_SimpleRec.
  exact (H i).
  assumption.
Qed.

Lemma simpl_contr_implies_contr_fu {τ} : SimpleContr τ → SimpleContr (fu' τ)
with simpl_rec_implies_rec_fu {τ} : SimpleRec τ → SimpleRec (fu' τ).
Proof.
  - unfold fu'.
    intro P.
    pose proof idm_contr_sub.
    revert H.
    generalize (idm Ty).
    (* functional induction (fu_accum τ ξ) using fu_accum_ind. *)
    intros ξ Q.

    functional induction (fu_accum τ ξ) using fu_accum_ind; cbn.
    inversion P.
    constructor;
    apply SimpleRecSub_implies_SimpleRec; assumption.
    constructor.
    inversion P.
    constructor;
    apply SimpleRecSub_implies_SimpleRec; assumption.

    inversion P.
    specialize (IHt H0).
    apply IHt.

    cbn.
    constructor.
    unfold comp.
    admit.


Admitted.

    (* constructor; apply SimpleRecContr; assumption. *)
    (* constructor. *)
    (* constructor; apply SimpleRecContr; assumption. *)
    (* constructor; assumption. *)
    (* induction P. *)
    (* cbn. *)
    (* constructor. *)
    (* cbn. *)
    (* constructor. *)
    (* apply simpl_rec_implies_rec_fu. *)

    (* cbn; try constructor. *)
    (* induction 1; cbn; constructor || intuition. *)

Reserved Notation "⟪ τ ≗ τ' ⟫"
  (at level 0, τ at level 98, τ' at level 98).
CoInductive Tyeq : Ty → Ty → Prop :=
| EqPrim : ⟪ tunit ≗ tunit ⟫
| EqArr {τ τ' σ σ'} :
    ⟪ τ ≗ σ ⟫ →
    ⟪ τ' ≗ σ' ⟫ →
    ⟪ tarr τ τ' ≗ tarr σ σ' ⟫
| EqSum {τ τ' σ σ'} :
    ⟪ τ ≗ σ ⟫ →
    ⟪ τ' ≗ σ' ⟫ →
    ⟪ τ ⊎ τ' ≗ σ ⊎ σ' ⟫
| EqVar {i} :
    ⟪ tvar i ≗ tvar i ⟫
| EqMuL {τ σ} :
    (* ⟪ fu' τ ≗ σ ⟫ → *)
    ⟪ τ[beta1 (trec τ)] ≗ σ ⟫ →
    SimpleContr τ →
    ⟪ trec τ ≗ σ ⟫
| EqMuR {τ σ} :
    LMC τ = 0 →
    SimpleContr σ →
    ⟪ τ ≗ σ[beta1 (trec σ)] ⟫ →
    ⟪ τ ≗ trec σ ⟫
where "⟪ τ ≗ τ' ⟫" := (Tyeq τ τ').

CoInductive Tyeq' : Ty → Ty → Prop :=
| EqPrim' : Tyeq' tunit tunit
| EqArr' {τ τ' σ σ'} :
    Tyeq' τ σ →
    Tyeq' τ' σ' →
    Tyeq' (tarr τ τ') (tarr σ σ')
| EqSum' {τ τ' σ σ'} :
    Tyeq' τ σ →
    Tyeq' τ' σ' →
    Tyeq' (τ ⊎ τ') (σ ⊎ σ')
| EqVar' {i} :
    Tyeq' (tvar i) (tvar i)
| EqMuL' {τ σ} :
    Tyeq' (fu' (trec τ)) σ →
    SimpleContr τ →
    Tyeq' (trec τ) σ
| EqMuR' {τ σ} :
    LMC τ = 0 →
    SimpleContr σ →
    Tyeq' τ (fu' (trec σ)) →
    Tyeq' τ (trec σ).


Lemma fu_accum_subst_eq {τ ξ ζ} : SimpleContr τ → fu_accum τ (ξ >=> ζ) = fu_accum τ[ξ] ζ.
Proof.
  intro H.
  revert ξ ζ.
  induction H;
    cbn;
    repeat change (apTy ?ξ ?τ) with τ[ξ];
    intros;
    rewrite ?ap_comp;
    try auto.

  rewrite <- (IHSimpleContr ξ↑ (ζ↑ >=> beta1 (trec τ[ξ↑ >=> ζ↑]))).
  rewrite comp_assoc.
  rewrite comp_up.
  reflexivity.
Qed.

Lemma fu_eq_unfold_fu {τ} : SimpleContr τ → fu' (trec τ) = fu' (τ[beta1 (trec τ)]).
  intros.
  unfold fu'.
  cbn.
  repeat change (apTy ?ξ ?τ) with τ[ξ].
  rewrite ?ap_comp,
  ?up_idm,
  ?comp_id_right,
  ?comp_id_left,
  ?ap_id.

  assert (beta1 (trec τ) = beta1 (trec τ) >=> idm Ty) by (symmetry; apply comp_id_right).
  rewrite H0 at 1.
  exact (@fu_accum_subst_eq τ (beta1 (trec τ)) (idm Ty) H).
Qed.

Lemma lmc_fu_zero {τ} : SimpleContr τ → LMC (fu' τ) = 0.
Proof.
  unfold fu'.
  functional induction (fu_accum τ (idm Ty)) using fu_accum_ind;
  repeat cbn; trivial.

  inversion 1.
  specialize (IHt H1).
  assumption.

  inversion 1.
Qed.

Lemma lmc_fu_zero' {τ ξ} : SimpleContr τ → LMC (fu_accum τ ξ) = 0.
Proof.
  revert ξ.
  functional induction (fu_accum τ (idm Ty)) using fu_accum_ind;
  repeat cbn; trivial.

  inversion 1.
  apply IHt.
  assumption.

  inversion 1.
Qed.

Lemma fu_id_lmc_zero {τ} : LMC τ = 0 → fu' τ = τ.
Proof.
  intros.
  destruct τ; cbn; trivial; repeat change (apTy ?ξ ?τ) with τ[ξ];
  repeat rewrite ap_id; try reflexivity.
  enough (LMC (trec τ) <> 0) by contradiction.
  cbn.
  auto.
Qed.

Lemma fu_idem {τ} : SimpleContr τ → fu' (fu' (τ)) = fu' τ.
Proof.
  auto using fu_id_lmc_zero, lmc_fu_zero.
Qed.

Lemma fu_eq_lhs {τ} : SimpleContr τ → ⟪ fu' τ ≗ τ ⟫.
Proof.
  unfold fu'.
  intro H.
  remember (fu_accum τ (idm Ty)) as P.
  assert (τ = τ[idm Ty]) by (symmetry; apply ap_id).
  rewrite H0.
  rewrite HeqP.
  clear HeqP H0.
  generalize (idm Ty) as ξ.
  intro ξ.
  functional induction (fu_accum τ ξ) using fu_accum_ind;
    intros.
  admit.
  admit.
  admit.
  inversion H.
  specialize (IHt H1).
  cbn.
  constructor.
  apply lmc_fu_zero'.
  assumption.


  admit.
Admitted.


Lemma fu_eq_pres {τ σ} : SimpleContr τ → SimpleContr σ → ⟪ fu' τ ≗ σ ⟫ → ⟪ τ ≗ σ ⟫.
Proof.
  unfold fu'.
  intros.
  revert H1.

  induction H; intros.
  cbn in H1.
  assumption.

  cbn in H2.
  repeat change (apTy ?ξ ?τ) with τ[ξ] in H2.
  repeat rewrite ap_id in H2.
  assumption.

  cbn in H2.
  repeat change (apTy ?ξ ?τ) with τ[ξ] in *.
  repeat rewrite ap_id in H2.
  assumption.

  functional induction (fu_accum (trec τ) (idm Ty)) using fu_accum_ind.

  cbn in H1.
Admitted.
  (* rewrite up_idm in H1. *)
  (* rewrite comp_id_left in H1. *)
  (* repeat change (apTy ?ξ ?τ) with τ[ξ] in *. *)
  (* pose proof (@fu_eq_unfold_fu τ H). *)
  (* unfold fu' in H2. *)
  (* constructor. *)
  (* rewrite H2 in IHSImpl *)
  (* . *)






  (* assert (σ = σ[idm Ty]) by (symmetry; apply ap_id). *)
  (* rewrite H. *)
  (* clear H. *)
  (* generalize (idm Ty) as ξ. *)
  (* intros. *)
  (* functional induction (fu_accum τ ξ) using fu_accum_ind. *)
  (* cbn in *. *)
  (* repeat change
 (apTy ?ξ ?τ) with τ[ξ] in *. *)
  (* inversion H1. *)
  (* constructor. *)

Lemma fu_pres_tyeq'_lhs {τ σ} : Tyeq' τ σ → Tyeq' (fu' τ) σ.
  intros.
  induction τ;
    try (
      cbn;
      repeat change (apTy ?ξ ?τ) with τ[ξ] in *;
      rewrite ?ap_id;
      assumption
  ).
  inversion H.
  assumption.
  cbn in H0.
  lia.
Qed.

Lemma fu_pres_tyeq'_rhs {τ σ} : Tyeq' τ σ → Tyeq' τ (fu' σ).
Proof.
  intros.
  induction σ;
    try (
      cbn;
      repeat change (apTy ?ξ ?τ) with τ[ξ] in *;
      rewrite ?ap_id;
      assumption
  ).
  inversion H.
  constructor.
  inversion H0;
    try (
      assert (LMC (trec τ1) = LMC (fu' (trec τ0))) by (
                                                     f_equal; assumption
                                                   );
      contradict H8;
      rewrite lmc_fu_zero;
      cbn;
      [lia | (constructor; assumption)]
      ).
  all: assumption.
Qed.

Lemma fu_pres_tyeq' {τ σ} : Tyeq' τ σ → Tyeq' (fu' τ) (fu' σ).
Proof.
  auto using fu_pres_tyeq'_lhs, fu_pres_tyeq'_rhs.
Qed.

Lemma fuz {τ σ} : SimpleContr τ → SimpleContr σ → Tyeq' τ σ → Tyeq' (trec τ) (trec σ).
Proof.
  intros.
  constructor.
  constructor.
  apply lmc_fu_zero.
  constructor.
  assumption.
  assumption.
  destruct τ, σ.
  cbn.
  repeat change (apTy ?ξ ?τ) with τ[ξ] in *.
  rewrite ?ap_id.
  rewrite ?
  cbn.
Admitted.



Lemma tyeq'_refl_contr_base {τ} : SimpleContr τ → Tyeq' τ τ
with tyeq'_refl_rec_base {τ} : SimpleRec τ → Tyeq' τ τ.
Proof.
  intro H.
  induction τ;
    try (
      inversion H;
      constructor;
      auto;
      fail
    ).
  constructor.
  constructor.
  apply lmc_fu_zero.
  assumption.
  inversion H.
  assumption.
Admitted.




(* I have to rework this proof on paper. *)
Lemma tyeq_refl (τ : Ty) : SimpleContr τ → ⟪ τ ≗ τ ⟫.
Proof.
  apply (simp_contr_mut_ind
           (fun {τ} (_ : SimpleContr τ) => (SimpleContr τ → ⟪ τ ≗ τ ⟫))
           (fun {τ} (_ : SimpleRec τ) => (SimpleRec τ → ⟪ τ ≗ τ ⟫)));
    try (constructor; auto; fail).
  intros.
  inversion H0.
Admitted.

Lemma lhs_fu_eq (τ : Ty) (P : Contr τ) : ⟪ τ ≗ fu' τ ⟫.
Proof.
  unfold fu'.
  replace τ with τ[idm Ty] at 1.
  generalize (idm Ty).
  induction τ;
  cbn.
  constructor.
Admitted.

