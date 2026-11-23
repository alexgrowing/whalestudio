import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.fourAe :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (u : L V), Integrable (u : ℝ → V) → ∀ᵐ ξ : ℝ, Lp.fourierTransformₗᵢ ℝ V u ξ = 𝓕 (u : ℝ → V) ξ := by
  intro V _ _ _ _ u hu
  have hc : Continuous (𝓕 (u : ℝ → V)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hu
  refine ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp _).locallyIntegrable (by norm_num)) hc.locallyIntegrable ?_
  intro g hg hgc
  have hs : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) := hgc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let φ : SchwartzMap ℝ ℂ := hs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hg)
  have hφ : ∀ x, φ x = (g x : ℂ) := fun x => rfl
  have h1 := congrArg (fun T : TemperedDistribution ℝ V => T φ) (Lp.fourier_toTemperedDistribution_eq u)
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at h1
  have h2 := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar) (L := innerₗ ℝ) (μ := volume) (ν := volume) (f := (φ : ℝ → ℂ)) (g := (u : ℝ → V))
    Real.continuous_fourierChar (by fun_prop) φ.integrable hu
  have h3 : (innerₗ ℝ).flip = innerₗ ℝ := by ext; simp
  rw [h3] at h2
  have e : ∀ (x : ℝ) (v : V), g x • v = φ x • v := fun x v => by rw [hφ, Complex.coe_smul]
  simp only [e]
  exact h1.symm.trans h2
