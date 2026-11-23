import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthGoodSubProj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnCoord

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Cx
open GlobalTheory.FormTies GlobalTheory.OnTies
open GlobalTheory.OntoChain (coordMap thetaMat thetaOp liftLvl liftSub supLat Mir mirIncl uni mirToGL)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cx_eq_zero {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    (hZ : X.RatZ) (j : Bs.J) (t : Bs.Tup) (f : A.FL j t)
    (hf : ∀ z ∈ X.Zl j t, inner ℂ (X.jL j t z) (X.jL j t f) = 0) : X.θ' j t (X.jL j t f) = 0 := by
  have h1 : ∀ y ∈ LinearMap.range (LinearMap.adjoint (X.θ' j t)), inner ℂ y (X.jL j t f) = 0 := by
    rw [← hZ.2 j t]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨z, hz, rfl⟩ := hy; exact hf z hz
    | zero => exact inner_zero_left _
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  have h2 := h1 _ ⟨X.θ' j t (X.jL j t f), rfl⟩
  rwa [LinearMap.adjoint_inner_left, inner_self_eq_zero] at h2

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem inner_jV (hM : R.IsModels) (i : Fin D.R.m) (t : T0) (x y : (A.MtCSD i t).Forms) :
    inner ℂ (jVx R i t x) (jVx R i t y) = D.what₂.embLL ((A.MtCSD i t).csum x.1 y.1) :=
  ((hM.HV i t).2.2 (jVx R i t x) (jVx R i t y)).trans
    ((congrArg₂ (Bridge.adInner _ _ _) (hM.jV i t x) (hM.jV i t y)).trans (GlobalTheory.PresBasic.isom (R.B.L i t).pres x y))

theorem thG_eq_zero (hM : R.IsModels) (hZ : R.LRatZ F) (i : Fin D.R.m) (t : T0) (f : (A.MtCSD i t).Forms)
    (hf : ∀ z : (A.MtCSD i t).Forms, z ∈ liftSub R F i t → (A.MtCSD i t).csum z.1 f.1 = 0) :
    R.thG i t (jVx R i t f) = 0 :=
  cx_eq_zero (R.toCx F) hZ i t f fun z hz =>
    (congrArg (cj (twAt D.what₂.embLL A.v0)) ((inner_jV hM i t z f).trans
      ((congrArg D.what₂.embLL (hf z hz)).trans (map_zero _)))).trans (map_zero _)

theorem jVx_sub (i : Fin D.R.m) (t : T0) (x y : (A.MtCSD i t).Forms) :
    jVx R i t (x - y : (A.MtCSD i t).Forms) = jVx R i t x - jVx R i t y := map_sub (R.jV i t) x y

theorem thG_good {s : ℕ} (hOk : A.fam.Ok s) (hM : R.IsModels) (hS : R.LStable F) (hZ : R.LRatZ F) (i : Fin D.R.m) (t : T0)
    (x : Fin (srcDim A i t F.P0 F.ψ0⁻¹) → D.what₂.LL) :
    R.thG i t (jVx R i t (srcForm A i t F.P0 F.ψ0⁻¹
      (((A.MtCSD i t).lvlOp (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹ (idemOf A.X)).mulVec x))) =
    R.thG i t (jVx R i t ((A.fam.L i t).toF (liftLvl F) (liftSub R F i t)
      (((A.fam.L i t).lPr (liftLvl F) (liftSub R F i t)).mulVec x))) := by
  refine sub_eq_zero.1 ((map_sub (R.thG i t) _ _).symm.trans ((congrArg (R.thG i t) (jVx_sub i t _ _).symm).trans ?_))
  refine thG_eq_zero hM hZ i t _ fun z hz => ?_
  have h := orth_good_sub_proj (OntoChain.blockHyp (F := F) hOk i t) (Z := liftSub R F i t)
    (fun g => hS.2 i t (Sum.inr g)) x ⟨z, hz, rfl⟩
  rw [CyclotomicLifting.hform_eq_csum, CSD.I_apply, CSD.I_apply, map_sub] at h
  unfold BlockDat.fE at h
  rw [← Matrix.mulVec_mulVec] at h
  refine Eq.trans (congrArg₂ (fun a b => (A.MtCSD i t).csum a b) ?_ rfl) h
  exact congrArg Subtype.val ((A.MtCSD i t).basis.equivFun.symm_apply_apply z).symm

theorem sign_at_base_place_eq_embedding (R : RealDat D A Ks) : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0

theorem adForm_injective (hM : R.IsModels) (hU : R.LUnif) (i : Fin D.R.m) : Function.Injective (adForm R i) := by
  refine (hM.HW i _).1.comp ((injective_iff_map_eq_zero ((R.FW i).j (sg0 D A))).2 fun x hx => ?_)
  by_contra hne
  exact ((hU i (sg0 D A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 hne)).ne_zero 0 hx

theorem adForm_eOp (hU : R.LUnif) (i : Fin D.R.m) (x : Fin (R.nW i) → D.what₂.LL) :
    adForm R i ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) x) =
      Mult.postOn _ (R.eWf i (sg0 D A)) (adForm R i x) := by
  unfold adForm
  rw [Arith.FormsL.eOp_apply, map_sum, map_sum]
  simp only [map_smulₛₗ, RingHom.id_apply, (hU i (sg0 D A)).2.2, smul_smul]
  have e : ∀ g, (sg0 D A) ((idemOf A.X).coeff g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) *
      (sg0 D A) (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) = RealDat.eC (A := A) (sg0 D A) g := fun g => by
    rw [← map_mul, mul_assoc, Units.inv_mul, mul_one]; rfl
  simp only [e]
  refine MultilinearMap.ext fun v => ?_
  rw [sum_apply]
  show _ = (R.eWf i (sg0 D A)) ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) x) v)
  unfold RealDat.eWf gaL
  rw [LinearMap.sum_apply]
  rfl

theorem eOp_classSum {s : ℕ} (hOk : A.fam.Ok s) (hM : R.IsModels) (hP : R.IsThP) (hU : R.LUnif) (hS : R.LStable F)
    (hZ : R.LRatZ F) (h5 : R.LTheta F) (hr : R.LRatTh F) (i : Fin D.R.m) (t : T0) (a : D.what₂.LL)
    {θ : (Fin (srcDim A i t F.P0 F.ψ0⁻¹) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)}
    (hθ : IsClassSum R i t F.P0 F.ψ0⁻¹ (D.what₂.embLL a) θ) (x : Fin (srcDim A i t F.P0 F.ψ0⁻¹) → D.what₂.LL) :
    (R.FW i).eOp (fun g => (idemOf A.X).coeff g)
      (θ (((A.MtCSD i t).lvlOp (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹ (idemOf A.X)).mulVec x)) = a • thetaOp R F i t x := by
  apply adForm_injective hM hU i
  have h1 : adForm R i (a • thetaOp R F i t x) = D.what₂.embLL a • adForm R i (thetaOp R F i t x) := by
    unfold adForm
    rw [map_smulₛₗ, map_smul, sign_at_base_place_eq_embedding R]
  rw [adForm_eOp hU, hθ, map_smul, h1]
  refine congrArg _ ((hP.thG i t _).symm.trans (congrArg (R.HW i (sg0 D A)).e ?_))
  exact (thG_good hOk hM hS hZ i t x).trans (OntoChain.j_thetaOp h5 hr i t x).symm

theorem chi_eq_one (hG : R.IsGrp F) (i : Fin D.R.m) {g : G} (hg : g ∈ F.P0) : (R.FW i).chi g = 1 := by
  obtain ⟨u, hu, rfl⟩ := (OntoChain.mem_base_iff hG.levels g).1 hg
  have h1 := (OntoChain.mem_pi_unip_iff R _).2 ⟨u, hu, rfl⟩
  refine Units.ext (D.what₂.embLL.injective ?_)
  rw [hG.chiW, Units.val_one, map_one, OntoChain.eG_mirIncl]
  refine Finset.prod_eq_one fun v _ => ?_
  have h2 := h1 v (Set.mem_univ v)
  have h3 : Matrix.GeneralLinearGroup.det (mirToGL R u v) = 1 := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular h2.1]
    exact Finset.prod_eq_one fun k _ => h2.2 k
  rw [h3, map_one, Units.val_one]

end Real

end GlobalTheory.OnCoord
