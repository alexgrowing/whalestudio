import Mathlib
import GroundTheory.AutomorphicForms.L2LocalComponents.Summand
import GroundTheory.AutomorphicForms.L2LocalComponents.CenterCommute
import GroundTheory.AutomorphicForms.L2LocalComponents.ArchBump

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace IsExpLieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)

theorem isSmoothVector_of_commute (S : E →L[ℂ] E) (hS : ∀ g, S ∘L π g = π g ∘L S) {v : E}
    (hv : h.IsSmoothVector π v) : h.IsSmoothVector π (S v) := by
  rw [isSmoothVector_iff] at hv ⊢
  have e : h.expOrbit π (S v) = (S.restrictScalars ℝ) ∘ h.expOrbit π v := by
    funext Y
    simp only [expOrbit, Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    exact (congrArg (fun T : E →L[ℂ] E => T v) (hS _)).symm
  rw [e]
  exact (S.restrictScalars ℝ).contDiff.comp hv

theorem derivOp_of_commute (S : E →L[ℂ] E) (hS : ∀ g, S ∘L π g = π g ∘L S) {v : E}
    (hv : h.IsSmoothVector π v) (X : 𝔤) : h.derivOp π X (S v) = S (h.derivOp π X v) := by
  have e : h.expOrbit π (S v) = (S.restrictScalars ℝ) ∘ h.expOrbit π v := by
    funext Y
    simp only [expOrbit, Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    exact (congrArg (fun T : E →L[ℂ] E => T v) (hS _)).symm
  unfold derivOp
  rw [e, ((S.restrictScalars ℝ).hasFDerivAt.comp 0 (h.differentiable_expOrbit π hv 0).hasFDerivAt).fderiv]
  rfl

theorem uAction_of_commute (S : E →L[ℂ] E) (hS : ∀ g, S ∘L π g = π g ∘L S)
    (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) (v : h.smoothVectors π) :
    (h.uAction π u ⟨S v, h.isSmoothVector_of_commute π S hS v.2⟩ : E) = S (h.uAction π u v) := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ h.lieSubalgebra) u
  induction t using TensorAlgebra.induction generalizing v with
  | algebraMap r =>
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, Submodule.coe_smul_of_tower]
    rw [← Complex.coe_smul, ← Complex.coe_smul, map_smul]
  | ι x =>
    show (h.uAction π (UniversalEnvelopingAlgebra.ι ℝ x) ⟨S v, _⟩ : E) =
      S (h.uAction π (UniversalEnvelopingAlgebra.ι ℝ x) v)
    rw [uAction_ι, coe_derivEnd, coe_derivEnd]
    exact h.derivOp_of_commute π S hS v.2 _
  | mul a b iha ihb =>
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    have e : (h.uAction π (UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra b)
        ⟨S v, h.isSmoothVector_of_commute π S hS v.2⟩) =
        ⟨S (h.uAction π (UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra b) v),
          h.isSmoothVector_of_commute π S hS (h.uAction π _ v).2⟩ := Subtype.ext (ihb v)
    rw [e, iha]
  | add a b iha ihb =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, Submodule.coe_add,
      iha, ihb, map_add]

end IsExpLieAlgebra

namespace CuspidalSpectrum

open AutomorphicForm Reduction

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

theorem norm_archRepT_le (a : archGroup K n) : ‖archRepT μ a‖ ≤ 1 :=
  (archURepT μ).norm_map_le a

variable (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]

def archOp {κ : archGroup K n → ℂ} (hκ : (isExpLieAlgebra K n).IsTestFunction κ) :
    CuspL2 μ →L[ℂ] CuspL2 μ :=
  LinearMap.mkContinuous
    { toFun := (archRepT μ).integrated ν κ
      map_add' := (isExpLieAlgebra K n).integrated_add (archRepT μ) hκ
      map_smul' := fun c x => IsExpLieAlgebra.integrated_smul (archRepT μ) κ c x }
    (∫ a, ‖κ a‖ ∂ν) fun x =>
      (isExpLieAlgebra K n).norm_integrated_le (archRepT μ) ν (norm_archRepT_le μ) hκ x

@[simp] theorem archOp_apply {κ : archGroup K n → ℂ} (hκ : (isExpLieAlgebra K n).IsTestFunction κ)
    (x : CuspL2 μ) : archOp μ ν hκ x = (archRepT μ).integrated ν κ x := rfl

theorem archOp_eq_integral {κ : archGroup K n → ℂ} (hκ : (isExpLieAlgebra K n).IsTestFunction κ)
    (x : CuspL2 μ) : archOp μ ν hκ x = ∫ a, κ a • archRepT μ a x ∂ν := rfl

theorem archOp_comm {κ : archGroup K n → ℂ} (hκ : (isExpLieAlgebra K n).IsTestFunction κ)
    (S : CuspL2 μ →L[ℂ] CuspL2 μ) (hS : ∀ a, S ∘L archRepT μ a = archRepT μ a ∘L S) (x : CuspL2 μ) :
    S (archOp μ ν hκ x) = archOp μ ν hκ (S x) := by
  rw [archOp_eq_integral, archOp_eq_integral,
    ← S.integral_comp_comm (integrable_smul_archRepT μ ν (hκ.continuous _) hκ.2 x)]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  simp only [map_smul]
  exact congrArg (κ a • ·) (congrArg (fun T : CuspL2 μ →L[ℂ] CuspL2 μ => T x) (hS a))

theorem inner_archOp {κ : archGroup K n → ℂ} (hκ : (isExpLieAlgebra K n).IsTestFunction κ)
    (hreal : ∀ a, starRingEnd ℂ (κ a) = κ a) (hsymm : ∀ a, κ a⁻¹ = κ a) (x y : CuspL2 μ) :
    ⟪archOp μ ν hκ x, y⟫_ℂ = ⟪x, archOp μ ν hκ y⟫_ℂ := by
  have hix := integrable_smul_archRepT μ ν (hκ.continuous _) hκ.2 x
  have hiy := integrable_smul_archRepT μ ν (hκ.continuous _) hκ.2 y
  rw [archOp_eq_integral, archOp_eq_integral, ← inner_conj_symm, ← integral_inner hix,
    ← integral_inner hiy]
  rw [← integral_conj]
  have e : ∀ a, starRingEnd ℂ ⟪y, κ a • archRepT μ a x⟫_ℂ = κ a * ⟪x, archRepT μ a⁻¹ y⟫_ℂ := by
    intro a
    rw [inner_smul_right, map_mul, hreal, inner_conj_symm, archRepT_apply, archRepT_apply,
      UnitaryRep.inner_map_left, map_inv]
  simp_rw [e]
  rw [← integral_inv_archGroup ν (fun a => κ a * ⟪x, archRepT μ a⁻¹ y⟫_ℂ)]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  simp only [inv_inv, hsymm, inner_smul_right]

theorem archOp_comm_archCompact {κ : archGroup K n → ℂ} (hκ : (isExpLieAlgebra K n).IsTestFunction κ)
    (hconj : ∀ k ∈ archCompact K n, ∀ a, κ (k * a * k⁻¹) = κ a) {k : archGroup K n}
    (hk : k ∈ archCompact K n) (x : CuspL2 μ) :
    archRepT μ k (archOp μ ν hκ x) = archOp μ ν hκ (archRepT μ k x) := by
  rw [archOp_eq_integral, archOp_eq_integral,
    ← (archRepT μ k).integral_comp_comm (integrable_smul_archRepT μ ν (hκ.continuous _) hκ.2 x)]
  have e : ∀ a, archRepT μ k (κ a • archRepT μ a x) =
      (fun b => κ b • archRepT μ b (archRepT μ k x)) (k * a * k⁻¹) := by
    intro a
    show _ = κ (k * a * k⁻¹) • archRepT μ (k * a * k⁻¹) (archRepT μ k x)
    rw [hconj k hk a, map_smul, ← BanachRep.map_mul_apply, ← BanachRep.map_mul_apply]
    congr 3
    group
  simp_rw [e]
  exact integral_conj_archGroup ν (fun b => κ b • archRepT μ b (archRepT μ k x)) k

def fixU (U : Subgroup (AdelicGLn.integralFiniteGL K n)) : Submodule ℂ (CuspL2 μ) where
  carrier := {y | ∀ u ∈ U, cuspRepT μ (finOne K n u) y = y}
  add_mem' hx hy u hu := by rw [map_add, hx u hu, hy u hu]
  zero_mem' u _ := map_zero _
  smul_mem' c x hx u hu := by rw [map_smul, hx u hu]

theorem isClosed_fixU (U : Subgroup (AdelicGLn.integralFiniteGL K n)) :
    IsClosed (fixU μ U : Set (CuspL2 μ)) := by
  have : (fixU μ U : Set (CuspL2 μ)) = ⋂ u ∈ U, {y | cuspRepT μ (finOne K n u) y = y} := by
    ext y; simp [fixU]
  rw [this]
  exact isClosed_biInter fun u _ => isClosed_eq (cuspRepT μ (finOne K n u)).continuous continuous_id

instance (U : Subgroup (AdelicGLn.integralFiniteGL K n)) : CompleteSpace (fixU μ U) :=
  (isClosed_fixU μ U).completeSpace_coe

theorem finOne_archP_comm (u : AdelicGLn.integralFiniteGL K n) (a : archGroup K n) :
    finOne K n u * archP K n a = archP K n a * finOne K n u := by
  ext1
  simp only [Subgroup.coe_mul, coe_finOne, archimedeanProjection_apply]
  exact (archProj_mul_finEmb_comm (a : ArchUnits K n) (u : AdelicGLn.FiniteAdelicGL K n)).symm

theorem archRepT_mem_fixU {U : Subgroup (AdelicGLn.integralFiniteGL K n)} (a : archGroup K n)
    {y : CuspL2 μ} (hy : y ∈ fixU μ U) : archRepT μ a y ∈ fixU μ U := by
  intro u hu
  rw [archRepT_apply, ← UnitaryRep.map_mul_apply, finOne_archP_comm, UnitaryRep.map_mul_apply, hy u hu]

theorem starProjection_fixU_comm (U : Subgroup (AdelicGLn.integralFiniteGL K n)) (a : archGroup K n) :
    (fixU μ U).starProjection ∘L archRepT μ a = archRepT μ a ∘L (fixU μ U).starProjection := by
  have h := ((UnitaryRep.isInvariant_iff_commute_starProjection (π := archURepT μ) (fixU μ U)).1
    (fun b y hy => archRepT_mem_fixU μ b hy)) a
  exact h.eq.symm

theorem integrated_eq_smul_archOp {U : Subgroup (AdelicGLn.integralFiniteGL K n)}
    {κ : archGroup K n → ℂ} (hκ : (isExpLieAlgebra K n).IsTestFunction κ)
    {F₀ : CompactlySupportedContinuousMap (normOneGL K n) ℂ} {c : ℝ}
    (hint : ∀ Θ : normOneGL K n → ℂ, Continuous Θ → (∀ u ∈ U, ∀ x, Θ (x * finOne K n u) = Θ x) →
      ∫ x, F₀ x * Θ x ∂μ = c * ∫ a, κ a * Θ (archP K n a) ∂ν)
    {y : CuspL2 μ} (hy : y ∈ fixU μ U) :
    (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ F₀) y = (c : ℂ) • archOp μ ν hκ y := by
  refine ext_inner_left ℂ fun w => ?_
  rw [inner_integrated_ccToL1_eq (cuspRepT μ) μ F₀ w y,
    hint (fun x => ⟪w, cuspRepT μ x y⟫_ℂ) (continuous_const.inner ((cuspRepT μ).continuous_orbit y))
      (fun u hu x => by rw [UnitaryRep.map_mul_apply, hy u hu]),
    inner_smul_right, archOp_eq_integral,
    ← integral_inner (integrable_smul_archRepT μ ν (hκ.continuous _) hκ.2 y)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  show κ a * _ = ⟪w, κ a • archRepT μ a y⟫_ℂ
  rw [inner_smul_right, archRepT_apply]

end CuspidalSpectrum

end

end GroundTheory.Automorphic
