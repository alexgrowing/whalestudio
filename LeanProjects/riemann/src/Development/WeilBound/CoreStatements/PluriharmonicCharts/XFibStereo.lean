import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.WeilBound.CoreStatements.PluriharmonicCharts.LintegralStereo
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace PositivityTheory.Xgp.fib_stereo

open MeasureTheory Set
open scoped ENNReal NNReal

theorem measure_part (f : (Fin 3 → ℝ) → ℝ) (hf : Measurable f) :
    (Integrable (fun a : ℂ => f (nF a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) ↔
      Integrable (fun m : ReciprocityTheory.ChartRestriction.G.AI.S2 => f fun i => (m : ReciprocityTheory.ChartRestriction.G.AI.E3) i)
        ReciprocityTheory.ChartRestriction.G.AI.sphereMeasure) ∧
    ∫ a : ℂ, f (nF a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2) =
      ∫ m : ReciprocityTheory.ChartRestriction.G.AI.S2, f (fun i => (m : ReciprocityTheory.ChartRestriction.G.AI.E3) i)
        ∂ ReciprocityTheory.ChartRestriction.G.AI.sphereMeasure := by
  set gE : GroundTheory.Heights₂.Heights.FlagBundles.E3 → ℝ := fun x => f (fun i => x i) with hgE
  have hgm : Measurable gE :=
    hf.comp (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable
  set w : ℂ → ℝ≥0 := fun a => Real.toNNReal (wt a) with hw
  have hwm : Measurable w := Measurable.real_toNNReal (by unfold wt; fun_prop)
  have hmap : (volume.withDensity fun a : ℂ => (w a : ℝ≥0∞)).map nE =
      GroundTheory.Heights₂.Heights.FlagBundles.sphereMeasure.map
        (fun m : GroundTheory.Heights₂.Heights.FlagBundles.Sphere2 => (m : GroundTheory.Heights₂.Heights.FlagBundles.E3)) :=
    map_stereo
  have hpt : (fun a : ℂ => f (nF a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) =
      fun a => w a • gE (nE a) := by
    funext a
    have hnn : 0 ≤ wt a := by unfold wt; positivity
    rw [NNReal.smul_def, smul_eq_mul, hw, Real.coe_toNNReal _ hnn]
    show f (nF a) * _ = wt a * f (nF a)
    unfold wt
    ring
  have hnE := measurable_nE.aemeasurable (μ := volume.withDensity fun a : ℂ => (w a : ℝ≥0∞))
  have hco : AEMeasurable (fun m : GroundTheory.Heights₂.Heights.FlagBundles.Sphere2 =>
      (m : GroundTheory.Heights₂.Heights.FlagBundles.E3)) GroundTheory.Heights₂.Heights.FlagBundles.sphereMeasure :=
    measurable_subtype_coe.aemeasurable
  constructor
  · rw [hpt, ← integrable_withDensity_iff_integrable_smul₀ hwm.aemeasurable]
    refine (integrable_map_measure (g := gE) hgm.aestronglyMeasurable hnE).symm.trans ?_
    rw [hmap]
    exact integrable_map_measure hgm.aestronglyMeasurable hco
  · rw [hpt, ← integral_withDensity_eq_integral_smul hwm]
    refine (integral_map hnE hgm.aestronglyMeasurable).symm.trans ?_
    rw [hmap]
    exact integral_map hco hgm.aestronglyMeasurable

theorem logSin_part (a₀ a₁ : ℂ) :
    logSin 1 a₀ a₁ = (1 / 2) * Real.log ((1 - ∑ i, nF a₀ i * nF a₁ i) / 2) := by
  have hN : ∀ u : ℂ, ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := fun u => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have e1 : ∀ u v : ℂ, herm2 1 ![1, u] ![1, v] = 1 + (starRingEnd ℂ) u * v := by
    intro u v
    simp [herm2, dotProduct, Fin.sum_univ_two]
  have e2 : ∀ u : ℂ, (herm2 1 ![1, u] ![1, u]).re = 1 + (u.re ^ 2 + u.im ^ 2) := by
    intro u
    rw [e1]
    simp [Complex.mul_re]
    ring
  have e3 : ‖herm2 1 ![1, a₀] ![1, a₁]‖ ^ 2 =
      (1 + (a₀.re * a₁.re + a₀.im * a₁.im)) ^ 2 + (a₀.re * a₁.im - a₀.im * a₁.re) ^ 2 := by
    rw [e1, hN]
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hs : ∑ i, nF a₀ i * nF a₁ i =
      (2 * a₀.re / (1 + ‖a₀‖ ^ 2)) * (2 * a₁.re / (1 + ‖a₁‖ ^ 2)) +
      (2 * a₀.im / (1 + ‖a₀‖ ^ 2)) * (2 * a₁.im / (1 + ‖a₁‖ ^ 2)) +
      ((1 - ‖a₀‖ ^ 2) / (1 + ‖a₀‖ ^ 2)) * ((1 - ‖a₁‖ ^ 2) / (1 + ‖a₁‖ ^ 2)) := by
    rw [Fin.sum_univ_three]
    rfl
  unfold logSin
  rw [e2, e2, e3, hs, hN, hN]
  congr 2
  have p0 : (0 : ℝ) < 1 + (a₀.re ^ 2 + a₀.im ^ 2) := by positivity
  have p1 : (0 : ℝ) < 1 + (a₁.re ^ 2 + a₁.im ^ 2) := by positivity
  field_simp
  ring

end PositivityTheory.Xgp.fib_stereo
