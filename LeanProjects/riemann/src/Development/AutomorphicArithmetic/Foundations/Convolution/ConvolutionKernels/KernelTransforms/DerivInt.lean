import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
import GroundTheory.AutomorphicForms.TraceFormulaConvolution
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
import GroundTheory.AutomorphicForms.MultiplicityOne.OpenSubgroupRep
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteAdelicHaar
import GroundTheory.AutomorphicForms.L2LocalComponents.CenterCommute
import GroundTheory.AutomorphicForms.GKModules.KernelCalculus

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

section
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

private theorem UpperTheory.ConvolutionTheory.Tf.rightAction_integral_derivative {Θ : G → ℂ} (hΘ : Continuous Θ)
    (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) (κ : h.smoothFuns (F := ℂ))
    (hκ : h.IsTestFunction (fun y => (κ : G → ℂ) y⁻¹)) :
    h.IsTestFunction (fun y => (h.rightUAction u κ : G → ℂ) y⁻¹) ∧
      (h.rightUAction (F := ℂ) u
          ⟨fun g => ∫ y, Θ (g * y) * (κ : G → ℂ) y⁻¹ ∂μ, h.isSmoothFun_integral_mul μ hΘ hκ⟩ : G → ℂ) =
        fun g => ∫ y, Θ (g * y) * (h.rightUAction u κ : G → ℂ) y⁻¹ ∂μ := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ h.lieSubalgebra) u
  induction t using TensorAlgebra.induction generalizing κ with
  | algebraMap r =>
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    refine ⟨hκ.const_mul (r : ℂ), ?_⟩
    funext g
    exact (IsExpLieAlgebra.integral_mul_const_mul μ Θ (fun y => (κ : G → ℂ) y⁻¹) (r : ℂ) g).symm
  | ι x =>
    have e : UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra (TensorAlgebra.ι ℝ x) =
        UniversalEnvelopingAlgebra.ι ℝ x := rfl
    have e2 : (fun y => h.rightDeriv (h.ofLie x) (κ : G → ℂ) y⁻¹) =
        h.convDeriv (h.ofLie x) (fun y => (κ : G → ℂ) y⁻¹) := by
      funext y
      simp [IsExpLieAlgebra.convDeriv]
    simp only [e, IsExpLieAlgebra.rightUAction_ι, IsExpLieAlgebra.coe_rightDerivEnd]
    refine ⟨e2 ▸ hκ.convDeriv _, ?_⟩
    funext g
    rw [h.rightDeriv_integral_mul μ hΘ hκ, ← e2]
  | mul a b ha hb =>
    obtain ⟨hb1, hb2⟩ := hb κ hκ
    obtain ⟨ha1, ha2⟩ := ha _ hb1
    simp only [map_mul, Module.End.mul_apply]
    refine ⟨ha1, ?_⟩
    rw [← ha2]
    congr 2
    exact Subtype.ext hb2
  | add a b ha hb =>
    obtain ⟨ha1, ha2⟩ := ha κ hκ
    obtain ⟨hb1, hb2⟩ := hb κ hκ
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add]
    refine ⟨ha1.add hb1, ?_⟩
    rw [ha2, hb2]
    funext g
    exact (h.integral_mul_add μ hΘ ha1 hb1 g).symm

private theorem UpperTheory.ConvolutionTheory.Tf.derivInt_shift (κ Θ : G → ℂ) (x : G) :
    ∫ a, κ (a⁻¹ * x) * Θ a ∂μ = ∫ y, Θ (x * y) * κ y⁻¹ ∂μ := by
  rw [← integral_mul_left_eq_self (μ := μ) (fun a => κ (a⁻¹ * x) * Θ a) x]
  congr 1
  funext y
  simp [mul_comm]

end

theorem UpperTheory.ConvolutionTheory.Tf.derivInt :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (κ : archGroup K n → ℂ) (hκ : κ ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ)), HasCompactSupport κ →
      ∀ Θ : archGroup K n → ℂ, Continuous Θ →
      ∃ hF : (fun x => ∫ a, κ (a⁻¹ * x) * Θ a ∂ν) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ), ∀ (u : UEnv K n) (x : archGroup K n),
        ((isExpLieAlgebra K n).rightUAction u ⟨_, hF⟩ : archGroup K n → ℂ) x =
          ∫ a, ((isExpLieAlgebra K n).rightUAction u ⟨κ, hκ⟩ : archGroup K n → ℂ) (a⁻¹ * x) * Θ a ∂ν := by
  intro K _ _ n ν _ κ hκ hc Θ hΘ
  have ht : (isExpLieAlgebra K n).IsTestFunction (fun y => κ y⁻¹) :=
    ⟨IsExpLieAlgebra.isSmoothFun_comp_inv hκ, hc.comp_homeomorph (Homeomorph.inv _)⟩
  have e : (fun x => ∫ a, κ (a⁻¹ * x) * Θ a ∂ν) = fun x => ∫ y, Θ (x * y) * κ y⁻¹ ∂ν :=
    funext fun x => UpperTheory.ConvolutionTheory.Tf.derivInt_shift ν κ Θ x
  have hs := (isExpLieAlgebra K n).isSmoothFun_integral_mul ν hΘ ht
  refine ⟨e ▸ hs, fun u x => ?_⟩
  have key := (UpperTheory.ConvolutionTheory.Tf.rightAction_integral_derivative (isExpLieAlgebra K n) ν hΘ u ⟨κ, hκ⟩ ht).2
  rw [UpperTheory.ConvolutionTheory.Tf.derivInt_shift ν _ Θ x, ← congrFun key x]
  exact congrArg (fun f => (((isExpLieAlgebra K n).rightUAction u f : (isExpLieAlgebra K n).smoothFuns (F := ℂ)) :
    archGroup K n → ℂ) x) (Subtype.ext e)
