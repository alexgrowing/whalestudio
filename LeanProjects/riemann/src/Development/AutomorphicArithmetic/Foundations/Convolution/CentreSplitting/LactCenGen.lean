import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CentralIntegrated
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LactSpec

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.Dp

theorem oinf_toLp {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : TI K n) (w : CuspL2 μ) :
    Oinf μ ν β (toLp μ w) = toLp μ ((archRepT μ).integrated ν β w) := by
  refine Eq.trans ?_ (toLp_integrated_archRepT μ ν (γ := β) β.continuous β.hasCompactSupport w).symm
  rw [Oinf, UnitaryRep.integrated_ccToL1_apply]
  rfl

theorem rUC_tmul {K : Type} [Field K] [NumberField K] {n : ℕ} (c : ℂ) (p : UEnv K n) (f : (isExpLieAlgebra K n).smoothFuns (F := ℂ))
    (g : archGroup K n) : (rUC (c ⊗ₜ p) f).1 g = c * ((isExpLieAlgebra K n).rightUAction p f).1 g := by
  have h : rUC (c ⊗ₜ p) = algebraMap ℂ _ c * (isExpLieAlgebra K n).rightUAction (F := ℂ) p :=
    Algebra.TensorProduct.lift_tmul _ _ _ c p
  rw [h]
  rfl

set_option maxHeartbeats 800000 in
theorem lactCen_of_gen (K : Type) [Field K] [NumberField K] (n : ℕ)
    (hG : Subgroup.closure (Set.range (isExpLieAlgebra K n).expG) = ⊤) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : TI K n) (hβ : SmoothT β) :
    ∀ p ∈ (isExpLieAlgebra K n).centerU, ∀ q ∈ (isExpLieAlgebra K n).centerU, ∀ φ ∈ centralCuspForms K n,
      Oinf μ ν (lact ((1 : ℂ) ⊗ₜ p + Complex.I ⊗ₜ q) β) (clsL μ φ) =
        Oinf μ ν β (clsL μ (uActionCusp K n p φ + Complex.I • uActionCusp K n q φ)) := by
  intro p hp q hq φ hφ
  obtain ⟨h, hl⟩ := lactSpec K n ((1 : ℂ) ⊗ₜ p + Complex.I ⊗ₜ q) β hβ
  have hT : (isExpLieAlgebra K n).IsTestFunction β := ⟨hβ, β.hasCompactSupport⟩
  let f : (isExpLieAlgebra K n).smoothFuns (F := ℂ) := ⟨fun g => β g⁻¹, h⟩
  have e : (fun g => f.1 g⁻¹) = β := funext fun g => by simp only [f, inv_inv]
  have hf : (isExpLieAlgebra K n).IsTestFunction fun g => f.1 g⁻¹ := e ▸ hT
  have hπ : ∀ g, ‖archRepT μ g‖ ≤ 1 := fun g => ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [one_mul]
    exact ((archURepT μ).norm_map g v).le
  have key : ∀ z ∈ (isExpLieAlgebra K n).centerU,
      (archRepT μ).integrated ν (fun g => ((isExpLieAlgebra K n).rightUAction z f).1 g⁻¹) (cuspVecL μ φ) =
        (archRepT μ).integrated ν β (cuspVecL μ (uActionCusp K n z φ)) := fun z hz => by
    rw [← (kernel_uAction _ ν (archRepT μ) z f hf).2, central_integrated _ ν (archRepT μ) hπ hG hz hf (isSmoothVector_cuspToL2 μ hφ),
      uAction_cuspToL2 μ hφ, e]
  have e2 : (lact ((1 : ℂ) ⊗ₜ p + Complex.I ⊗ₜ q) β : archGroup K n → ℂ) = fun g =>
      ((isExpLieAlgebra K n).rightUAction p f).1 g⁻¹ + Complex.I * ((isExpLieAlgebra K n).rightUAction q f).1 g⁻¹ := by
    funext g
    have h3 := rUC_tmul 1 p f g⁻¹
    rw [one_mul] at h3
    rw [hl g, map_add, ← h3, ← rUC_tmul Complex.I q f g⁻¹]
    rfl
  have h1 := (kernel_uAction _ ν (archRepT μ) p f hf).1
  have h2 := (kernel_uAction _ ν (archRepT μ) q f hf).1
  have h4 : ∀ (γ : TI K n) ψ, Oinf μ ν γ (clsL μ ψ) = toLp μ ((archRepT μ).integrated ν γ (cuspVecL μ ψ)) :=
    fun γ ψ => oinf_toLp μ ν γ _
  have h5 : Oinf μ ν β (clsL μ (uActionCusp K n p φ + Complex.I • uActionCusp K n q φ)) =
      Oinf μ ν β (clsL μ (uActionCusp K n p φ)) + Complex.I • Oinf μ ν β (clsL μ (uActionCusp K n q φ)) := by
    rw [(clsL μ).map_add, (clsL μ).map_smul, (Oinf μ ν β).map_add, (Oinf μ ν β).map_smul]
  rw [h5, h4, h4, h4, e2, (isExpLieAlgebra K n).integrated_add_kernel ν _ h1 (h2.const_mul _),
    IsExpLieAlgebra.integrated_const_mul_kernel, key p hp, key q hq, (toLp μ).map_add, (toLp μ).map_smul]

end UpperTheory.ConvolutionTheory.Dp
