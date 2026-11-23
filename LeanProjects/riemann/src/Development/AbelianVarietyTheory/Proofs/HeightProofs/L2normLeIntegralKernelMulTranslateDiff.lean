import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivative
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCoordFunMulEqSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormIntegralStarMulSqLeMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

variable {n : ℕ}

theorem continuous_integral_paramK {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : KG ε → KG ε → E} (hF : Continuous (Function.uncurry F)) :
    Continuous (fun x => ∫ k, F x k ∂(muK ε)) := by
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  haveI : SecondCountableTopology (KG ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (KG ε : Set (UJ ε))
  have h := continuous_parametric_integral_of_continuous (μ := muK ε) hF (isCompact_univ (X := KG ε))
  simpa only [Measure.restrict_univ] using h

theorem integrable_prod_of_continuousK {ε : Fin n → Bool} {F : KG ε × KG ε → ℂ} (hF : Continuous F) :
    Integrable F ((muK ε).prod (muK ε)) := by
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  haveI : SecondCountableTopology (KG ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (KG ε : Set (UJ ε))
  exact hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem norm_integral_star_mul_le_sqrtK {ε : Fin n → Bool} {f g : KG ε → ℂ} (hf : Continuous f)
    (hg : Continuous g) :
    ‖∫ x, star (f x) * g x ∂(muK ε)‖ ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂(muK ε)) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂(muK ε)) := by
  have hsq : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  have re1 : ∀ h : KG ε → ℂ, (∫ x, star (h x) * h x ∂(muK ε)).re = ∫ x, ‖h x‖ ^ 2 ∂(muK ε) := by
    intro h; simp_rw [hsq]; rw [integral_complex_ofReal, Complex.ofReal_re]
  have H := GlobalTheory.norm_integral_star_mul_sq_le (muK ε) f g hf.aestronglyMeasurable hg.aestronglyMeasurable
    (integrable_of_continuousK (by fun_prop)) (integrable_of_continuousK (by fun_prop))
  rw [re1 f, re1 g] at H
  rw [← Real.sqrt_mul (integral_nonneg fun x => by positivity)]
  have := Real.abs_le_sqrt H
  rwa [abs_of_nonneg (norm_nonneg _)] at this

set_option maxHeartbeats 1600000 in

theorem sqrt_integral_normSq_le_integral_kernel_mul_translate :
    ∀ {n : ℕ} (ε : Fin n → Bool) (p : KG ε → ℂ) (κ : KG ε → ℝ), Continuous p → Continuous κ →
      (∀ k, 0 ≤ κ k) → ∫ k, κ k ∂(muK ε) = 1 →
      (∀ k, ∫ x, star (p x) * (κ (x⁻¹ * k) : ℂ) ∂(muK ε) = 0) →
      Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) ≤
        ∫ k, κ k * Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) ∂(muK ε) := by
  intro n ε p κ hp hκ hκ0 hκ1 horth
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  have hsq : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  have hA0 : 0 ≤ ∫ x, ‖p x‖ ^ 2 ∂(muK ε) := integral_nonneg fun x => by positivity
  have hAc : ∫ x, star (p x) * p x ∂(muK ε) = ((∫ x, ‖p x‖ ^ 2 ∂(muK ε) : ℝ) : ℂ) := by
    simp_rw [hsq]; exact integral_complex_ofReal
  have htr : ∀ x, ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε) = ∫ k, (κ (x⁻¹ * k) : ℂ) * p k ∂(muK ε) := by
    intro x
    have := integral_mul_left_eq_self (μ := muK ε) (fun k => (κ (x⁻¹ * k) : ℂ) * p k) x
    simpa only [inv_mul_cancel_left] using this
  have hzero : ∫ x, star (p x) * ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε) ∂(muK ε) = 0 := by
    simp_rw [htr]
    have e1 : ∀ x, star (p x) * ∫ k, (κ (x⁻¹ * k) : ℂ) * p k ∂(muK ε) =
        ∫ k, star (p x) * ((κ (x⁻¹ * k) : ℂ) * p k) ∂(muK ε) := fun x => (integral_const_mul _ _).symm
    simp_rw [e1]
    have hint : Integrable (Function.uncurry fun x k => star (p x) * ((κ (x⁻¹ * k) : ℂ) * p k))
        ((muK ε).prod (muK ε)) :=
      integrable_prod_of_continuousK (F := fun z : KG ε × KG ε => star (p z.1) * ((κ (z.1⁻¹ * z.2) : ℂ) * p z.2))
        (by fun_prop)
    rw [integral_integral_swap hint]
    have e2 : ∀ k, ∫ x, star (p x) * ((κ (x⁻¹ * k) : ℂ) * p k) ∂(muK ε) =
        (∫ x, star (p x) * (κ (x⁻¹ * k) : ℂ) ∂(muK ε)) * p k := by
      intro k; rw [← integral_mul_const]; congr 1; funext x; ring
    simp_rw [e2, horth, zero_mul, integral_zero]
  have hκ1c : ∫ k, (κ k : ℂ) ∂(muK ε) = 1 := by rw [integral_complex_ofReal, hκ1, Complex.ofReal_one]
  have hinner : ∀ x, ∫ k, (κ k : ℂ) * (p x - p (x * k)) ∂(muK ε) =
      p x - ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε) := by
    intro x
    have i1 : Integrable (fun k => (κ k : ℂ) * p x) (muK ε) := integrable_of_continuousK (by fun_prop)
    have i2 : Integrable (fun k => (κ k : ℂ) * p (x * k)) (muK ε) := integrable_of_continuousK (by fun_prop)
    simp_rw [mul_sub]
    rw [integral_sub i1 i2, integral_mul_const, hκ1c, one_mul]
  have hcontT : Continuous (fun x => ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε)) :=
    continuous_integral_paramK (F := fun x k => (κ k : ℂ) * p (x * k)) (by fun_prop)
  have hkey : ((∫ x, ‖p x‖ ^ 2 ∂(muK ε) : ℝ) : ℂ) =
      ∫ k, (κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε) ∂(muK ε) := by
    have e1 : ∀ k, (κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε) =
        ∫ x, star (p x) * ((κ k : ℂ) * (p x - p (x * k))) ∂(muK ε) := by
      intro k; rw [← integral_const_mul]; congr 1; funext x; ring
    simp_rw [e1]
    have hint : Integrable (Function.uncurry fun x k => star (p x) * ((κ k : ℂ) * (p x - p (x * k))))
        ((muK ε).prod (muK ε)) :=
      integrable_prod_of_continuousK
        (F := fun z : KG ε × KG ε => star (p z.1) * ((κ z.2 : ℂ) * (p z.1 - p (z.1 * z.2)))) (by fun_prop)
    rw [← integral_integral_swap hint]
    have e2 : ∀ x, ∫ k, star (p x) * ((κ k : ℂ) * (p x - p (x * k))) ∂(muK ε) =
        star (p x) * p x - star (p x) * ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε) := by
      intro x; rw [integral_const_mul, hinner, mul_sub]
    simp_rw [e2]
    have iA : Integrable (fun x => star (p x) * p x) (muK ε) := integrable_of_continuousK (by fun_prop)
    have iB : Integrable (fun x => star (p x) * ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε)) (muK ε) :=
      integrable_of_continuousK ((continuous_star.comp hp).mul hcontT)
    rw [integral_sub iA iB, hzero, sub_zero, hAc]
  have hCS : ∀ k, ‖∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε)‖ ≤
      Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) * Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) :=
    fun k => norm_integral_star_mul_le_sqrtK (g := fun x => p x - p (x * k)) hp (by fun_prop)
  have hIc : Continuous (fun k => ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε)) :=
    continuous_integral_paramK (F := fun k x => star (p x) * (p x - p (x * k))) (by fun_prop)
  have hDc : Continuous (fun k => ∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) :=
    continuous_integral_paramK (F := fun k x => ‖p x - p (x * k)‖ ^ 2) (by fun_prop)
  have hmain : ∫ x, ‖p x‖ ^ 2 ∂(muK ε) ≤ Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) *
      ∫ k, κ k * Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) ∂(muK ε) := by
    have e : ∫ x, ‖p x‖ ^ 2 ∂(muK ε) =
        (∫ k, (κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε) ∂(muK ε)).re := by
      rw [← hkey, Complex.ofReal_re]
    have hl : Continuous (fun k => ‖(κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε)‖) := by
      fun_prop
    have hr : Continuous (fun k => κ k * (Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) *
        Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)))) := by fun_prop
    calc ∫ x, ‖p x‖ ^ 2 ∂(muK ε)
        ≤ ‖∫ k, (κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε) ∂(muK ε)‖ := by
          rw [e]; exact Complex.re_le_norm _
      _ ≤ ∫ k, ‖(κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε)‖ ∂(muK ε) :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ k, κ k * (Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) *
            Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε))) ∂(muK ε) := by
          refine integral_mono (hl.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
            (hr.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) fun k => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hκ0 k)]
          exact mul_le_mul_of_nonneg_left (hCS k) (hκ0 k)
      _ = _ := by rw [← integral_const_mul]; congr 1; funext k; ring
  rcases hA0.lt_or_eq with hpos | hz
  · have hs : 0 < Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) := Real.sqrt_pos.2 hpos
    refine le_of_mul_le_mul_left ?_ hs
    rw [Real.mul_self_sqrt hA0]
    exact hmain
  · rw [← hz, Real.sqrt_zero]
    exact integral_nonneg fun k => mul_nonneg (hκ0 k) (Real.sqrt_nonneg _)

end GlobalTheory.KFourier

end
