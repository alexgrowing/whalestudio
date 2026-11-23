import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.QuadraticFormRationalPoints
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.ContInfPart
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.Fub3
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.SwapInt
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerContAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical
open UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.coefPer :
    DecE → Maj → OrbS → MomKill → OrbFn → CoefPer := by
  intro _ _ _ momKill orbFn E _ _ _ D W M N P φ hφ h0 h
  haveI := N.haar
  obtain ⟨j, -, hj, -⟩ := reps E D
  obtain ⟨hp, hw, hi⟩ := yInt E D W M N P φ hφ
  have hδ : D.δ < 0 := by simpa using D.neg (Rat.castHom ℝ)
  haveI : SFinite (mY D.δ N) := by unfold mY; infer_instance
  have hU := perCont E D W M N P φ hφ
  set U : G1 E → ℂ := fun h : G1 E => UPer D M fun x => φ.1 (x * gl h) with hUd
  have key : ∀ c : G1 E → ℂ, Continuous c → HasCompactSupport c → ∫ y, c y * U y ∂N.μ = 0 := fun c hc hs => by
    obtain ⟨Ψ, hΨ, hΨ'⟩ := orbFn E D M j hj c hc hs
    obtain ⟨h1, h2⟩ := zAll E D W M N P φ hφ j hj c hc hs Ψ hΨ hΨ'
    rw [← h2]
    exact momKill D.δ hδ _ (mY D.δ N) (pY D) _ hp hw hi (fun ph hph => (yEq E D W M N P φ hφ ph hph).symm.trans (h0 ph hph)) Ψ hΨ h1
  by_contra hne
  obtain ⟨χ, h1, -, hs, h01⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := h)) isClosed_empty
    (Set.disjoint_empty _)
  have h2 := key (fun y => (χ y : ℂ) * starRingEnd ℂ (U y))
    ((Complex.continuous_ofReal.comp χ.continuous).mul (Complex.continuous_conj.comp hU))
    ((hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero).mul_right)
  have e : ∀ y, (χ y : ℂ) * starRingEnd ℂ (U y) * U y = ((χ y * ‖U y‖ ^ 2 : ℝ) : ℂ) := fun y => by
    rw [mul_assoc, Complex.conj_mul']
    push_cast
    rfl
  simp only [e, integral_complex_ofReal, Complex.ofReal_eq_zero] at h2
  refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := N.μ) (x := h) (χ.continuous.mul (hU.norm.pow 2))
    hs.mul_right (fun y => mul_nonneg (h01 y).1 (sq_nonneg ‖U y‖)) ?_).ne' h2
  have : χ h = 1 := h1 rfl
  change χ h * ‖U h‖ ^ 2 ≠ 0
  rw [this, one_mul]
  exact pow_ne_zero _ (norm_ne_zero_iff.2 hne)
