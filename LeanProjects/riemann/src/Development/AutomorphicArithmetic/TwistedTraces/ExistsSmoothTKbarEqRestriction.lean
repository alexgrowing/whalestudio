import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClassAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.DixmierMalliavin
import Development.AutomorphicArithmetic.TwistedTraces.ExistsSmoothArchCutoffKbarEqOne

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

theorem UpperTheory.exists_smoothT_kbar_eq_restriction :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (a : CC K n) (x₀ : G1 K n),
        (isExpLieAlgebra K n).IsSmoothFun (fun A : archGroup K n => a (archP K n A * x₀)) →
        ∃ F : TI K n, SmoothT F ∧ ∀ A, kbar F A = a (archP K n A * x₀) := by
  intro K _ _ n hn a x₀ ha
  obtain ⟨χ, hχs, hχ1, hχc⟩ := UpperTheory.exists_smooth_archCutoff_kbar_eq_one K n hn
  have hχcont : Continuous fun A : archGroup K n => (χ A : ℂ) := by
    letI := (isExpLieAlgebra K n).chartedSpace
    exact ContMDiff.continuous hχs
  have hcont : Continuous fun A : archGroup K n => (χ A : ℂ) * a (archP K n A * x₀) :=
    hχcont.mul (a.continuous.comp (continuous_archP.mul continuous_const))
  have hC : IsCompact ((fun g : G1 K n => g * x₀⁻¹) '' tsupport a) :=
    a.hasCompactSupport.isCompact.image (continuous_id.mul continuous_const)
  obtain ⟨D, hD, hDm⟩ := hχc _ hC
  have hcs : HasCompactSupport fun A : archGroup K n => (χ A : ℂ) * a (archP K n A * x₀) := by
    refine HasCompactSupport.intro hD fun A hA => ?_
    by_contra hne
    have h1 : χ A ≠ 0 := fun h0 => hne (by rw [h0, Complex.ofReal_zero, zero_mul])
    have h2 : a (archP K n A * x₀) ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
    exact hA (hDm A h1 ⟨archP K n A * x₀, subset_tsupport _ h2, by simp⟩)
  refine ⟨⟨⟨_, hcont⟩, hcs⟩, ?_, fun A => ?_⟩
  · refine ((isExpLieAlgebra K n).isSmoothFun_iff).2 fun g => ?_
    exact ContDiff.mul (((isExpLieAlgebra K n).isSmoothFun_iff).1 hχs g)
      (((isExpLieAlgebra K n).isSmoothFun_iff).1 ha g)
  · have h1 := hχ1 A
    unfold kbar at h1 ⊢
    have h2 : ∀ s, (χ (A * zInf K n s) : ℂ) * a (archP K n (A * zInf K n s) * x₀) =
        (χ (A * zInf K n s) : ℂ) * a (archP K n A * x₀) := fun s => by
      rw [archimedeanProjection_mul_positiveScalar hn]
    show ∫ s, (χ (A * zInf K n s) : ℂ) * a (archP K n (A * zInf K n s) * x₀) ∂_ = _
    simp_rw [h2]
    rw [integral_mul_const, h1, one_mul]
