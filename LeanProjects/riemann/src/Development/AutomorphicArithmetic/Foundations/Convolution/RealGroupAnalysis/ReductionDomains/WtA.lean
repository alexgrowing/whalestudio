import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.wtA :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (β u : G1 F → ℝ≥0∞) (c : ℝ≥0∞), Measurable β → (∀ g, ∫⁻ b, β (nU b * g) ∂(adeleMeasure F) = c) → Measurable u → (∀ b g, u (nU b * g) = u g) → ∫⁻ g, u g * β g ∂M₀.μ = c * M.J0 M₀ u := by
  intro F _ _ M₀ β u c hβ hc hu hinv
  haveI := M₀.prob
  have hm : Measurable fun p : IdeleGroup F × G1 F => mD p.1 * p.2 :=
    ((M.continuous_mD.comp continuous_fst).mul continuous_snd).measurable
  have hJ : Measurable fun p : IdeleGroup F × G1 F => M.wt p.1 * u (mD p.1 * p.2) :=
    (M.measurable_wt.comp measurable_fst).mul (hu.comp hm)
  have hin : ∀ (a : IdeleGroup F) (k : G1 F),
      ∫⁻ b, u (nU b * mD a * k) * β (nU b * mD a * k) * ENNReal.ofReal ((ab a)⁻¹ ^ 2) ∂(adeleMeasure F)
        = c * (M.wt a * u (mD a * k)) := by
    intro a k
    have h1 : ∀ b, u (nU b * mD a * k) * β (nU b * mD a * k) * ENNReal.ofReal ((ab a)⁻¹ ^ 2)
        = (M.wt a * u (mD a * k)) * β (nU b * (mD a * k)) := fun b => by
      rw [mul_assoc (nU b), hinv, M.wt]; ring
    simp_rw [h1]
    have hb : Measurable fun b : A F => β (nU b * (mD a * k)) :=
      hβ.comp ((M.continuous_nU.mul continuous_const).measurable)
    rw [lintegral_const_mul _ hb, hc, mul_comm]
  have hk : Measurable fun k : G1 F => ∫⁻ a, M.wt a * u (mD a * k) ∂(ideleMeasure F) :=
    hJ.lintegral_prod_left'
  have hsec : ∀ k : G1 F, Measurable fun a : IdeleGroup F => M.wt a * u (mD a * k) :=
    fun k => M.measurable_wt.mul (hu.comp ((M.continuous_mD.mul continuous_const).measurable))
  rw [M₀.iwasawa (fun g => u g * β g) (hu.mul hβ), M.J0, Meas.ν, lintegral_prod_symm _ hJ.aemeasurable,
    ← lintegral_const_mul _ hk]
  refine lintegral_congr fun k => ?_
  rw [← lintegral_const_mul _ (hsec k)]
  exact lintegral_congr fun a => hin a k
