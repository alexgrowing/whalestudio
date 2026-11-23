import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry CategoryTheory MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.L2DbarEstimates GlobalTheory GlobalTheory.ShFam GlobalTheory.ChernReg GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AvgMV

theorem avg_sub_le : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [SmoothOfRelativeDimension d p]
    (a : ChartForm p σ d) (E : ChartMap p σ d) (c : AlgChart p σ d) (f : CxPts p σ → ℝ) (y : CxPts p σ) (t Cc M : ℝ),
    IsKaehlerForm (AnRead.all p σ d) a → IsExph a E → y ∈ c.e.source → 0 < t → 0 < Cc → 0 ≤ M →
    Metric.ball (c.e y) (Cc * t) ⊆ c.e.target →
    (∀ g : CxPts p σ → ℝ, IntegrableOn (g ∘ c.e.symm) (Metric.ball (c.e y) (Cc * t)) →
      Integrable (fun ξ => g (E c y (t • ξ)) * ChernReg.cutoff (a c y ξ)) ∧
      |rho a E g y t| ≤ Cc / t ^ (2 * d) * ∫ v in Metric.ball (c.e y) (Cc * t), |g (c.e.symm v)|) →
    (∀ w ∈ Metric.ball (c.e y) (Cc * t), DifferentiableAt ℝ (f ∘ c.e.symm) w ∧ ‖fderiv ℝ (f ∘ c.e.symm) w‖ ≤ M) →
    rho a E f y t - f y ≤ Cc * (volume (Metric.ball (0 : V d) 1)).toReal * Cc ^ (2 * d) * Cc * M * t := by
  intro k _ Y p σ d _ a E c f y t Cc M ha hE hy ht hCc hM hsub hker hdf
  have hq := continuous_and_smul ha hy
  have hpos := ha.2 c y hy
  have hMs := mass_pos hq.1 hq.2 hpos
  have hI := integrable_cutoff hq.1 hq.2 hpos
  set B := Metric.ball (c.e y) (Cc * t) with hB
  have hR : 0 < Cc * t := mul_pos hCc ht
  have hyB : c.e y ∈ B := Metric.mem_ball_self hR
  have hsy : c.e.symm (c.e y) = y := c.e.left_inv hy

  have hMV : ∀ v ∈ B, |f (c.e.symm v) - f y| ≤ M * (Cc * t) := by
    intro v hv
    have h := (convex_ball (c.e y) (Cc * t)).norm_image_sub_le_of_norm_fderiv_le
      (fun w hw => (hdf w hw).1) (fun w hw => (hdf w hw).2) hyB hv
    simp only [Function.comp_apply, hsy, Real.norm_eq_abs] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hM)
    rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hv).le
  have hcont : ContinuousOn (f ∘ c.e.symm) B := fun w hw => (hdf w hw).1.continuousAt.continuousWithinAt
  have hfin : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hIO : IntegrableOn (f ∘ c.e.symm) B := by
    haveI : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hfin
    refine Integrable.of_bound (C := |f y| + M * (Cc * t))
      (hcont.aestronglyMeasurable Metric.isOpen_ball.measurableSet)
      ((ae_restrict_iff' Metric.isOpen_ball.measurableSet).2 (ae_of_all _ fun v hv => ?_))
    have := hMV v hv
    rw [Function.comp_apply, Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (f (c.e.symm v)) (f y)
    linarith
  have hIOg : IntegrableOn ((fun z => f z - f y) ∘ c.e.symm) B :=
    hIO.sub (integrableOn_const hfin)
  have hg := (hker f hIO).1
  have hk2 := (hker (fun z => f z - f y) hIOg).2
  have hdiff : rho a E f y t - f y = rho a E (fun z => f z - f y) y t := by
    rw [rho_eq ha hE f hy t, rho_eq ha hE _ hy t, rhoIn, rhoIn, mean, mean]
    simp_rw [sub_mul]
    rw [integral_sub hg (hI.const_mul (f y)), integral_const_mul, sub_div,
      mul_div_cancel_right₀ _ hMs.ne']
  have hint : ∫ v in B, |(fun z => f z - f y) (c.e.symm v)| ≤ M * (Cc * t) * (volume B).toReal := by
    have := setIntegral_mono_on hIOg.abs (integrableOn_const hfin) Metric.isOpen_ball.measurableSet
      (fun v hv => hMV v hv)
    refine this.trans (le_of_eq ?_)
    rw [setIntegral_const]
    simp [Measure.real, smul_eq_mul, mul_comm]
  have hvol : (volume B).toReal = (Cc * t) ^ (2 * d) * (volume (Metric.ball (0 : V d) 1)).toReal := by
    rw [hB, Measure.addHaar_ball_of_pos _ _ hR, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    congr 2
    rw [← Module.finrank_mul_finrank ℝ ℂ (V d), Complex.finrank_real_complex]
    simp
  have hV1 : 0 ≤ (volume (Metric.ball (0 : V d) 1)).toReal := ENNReal.toReal_nonneg
  have htd : 0 < t ^ (2 * d) := by positivity
  calc rho a E f y t - f y ≤ |rho a E (fun z => f z - f y) y t| := hdiff ▸ le_abs_self _
    _ ≤ Cc / t ^ (2 * d) * ∫ v in B, |(fun z => f z - f y) (c.e.symm v)| := hk2
    _ ≤ Cc / t ^ (2 * d) * (M * (Cc * t) * (volume B).toReal) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = Cc * (volume (Metric.ball (0 : V d) 1)).toReal * Cc ^ (2 * d) * Cc * M * t := by
        rw [hvol, mul_pow]; field_simp
end GlobalTheory.AvgMV
