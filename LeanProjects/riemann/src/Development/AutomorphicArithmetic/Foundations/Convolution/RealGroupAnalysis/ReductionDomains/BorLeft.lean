import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem lintegral_mul_left_adele {F : Type} [Field F] [NumberField F] (c : (A F)ˣ) (g : A F → ℝ≥0∞) :
    ∫⁻ s, g ((c : A F) * s) ∂(adeleMeasure F) = ENNReal.ofReal (ab c)⁻¹ * ∫⁻ s, g s ∂(adeleMeasure F) := by
  have he : MeasurableEmbedding (fun x : A F => c • x) := (Homeomorph.smul c).measurableEmbedding
  have h1 : ∫⁻ s, g ((c : A F) * s) ∂(adeleMeasure F) =
      ∫⁻ s, g s ∂((adeleMeasure F).map (fun x : A F => c • x)) :=
    (he.lintegral_map g).symm
  rw [h1, map_smul_adeleMeasure, lintegral_smul_measure]
  rfl

private theorem wt_mul {F : Type} [Field F] [NumberField F] (s t : (A F)ˣ) : M.wt (s * t) = M.wt s * M.wt t := by
  have hs : 0 ≤ ((ab s)⁻¹ ^ 2 : ℝ) := by positivity
  simp only [M.wt]
  rw [← ENNReal.ofReal_mul hs, M.ab_mul, mul_inv, mul_pow]

theorem UpperTheory.ConvolutionTheory.R2.M.borLeft :
    ∀ (F : Type) [Field F] [NumberField F], ∀ (f : G1 F → ℝ≥0∞), Measurable f → ∀ (b₀ : A F) (a₀ : (A F)ˣ), ∫⁻ a : IdeleGroup F, ∫⁻ b, f (nU b₀ * mD a₀ * (nU b * mD a)) * M.wt a ∂(adeleMeasure F) ∂(ideleMeasure F) = ∫⁻ a : IdeleGroup F, ∫⁻ b, f (nU b * mD a) * M.wt a ∂(adeleMeasure F) ∂(ideleMeasure F) := by
  intro F _ _ f _ b₀ a₀
  have key : ∀ (a : (A F)ˣ) (b : A F), nU b₀ * mD a₀ * (nU b * mD a) =
      nU (b₀ + ((a₀ * a₀ : (A F)ˣ) : A F) * b) * mD (a₀ * a) := by
    intro a b
    rw [M.nU_add, M.mD_mul, mul_assoc (nU b₀), ← mul_assoc (mD a₀), M.mD_mul_nU]
    simp [pow_two, mul_assoc]
  have hc : ENNReal.ofReal (ab (a₀ * a₀))⁻¹ = M.wt a₀ := by
    simp only [M.wt]
    rw [M.ab_mul, mul_inv, pow_two]
  have inner : ∀ a : IdeleGroup F,
      ∫⁻ b, f (nU b₀ * mD a₀ * (nU b * mD a)) * M.wt a ∂(adeleMeasure F) =
        ∫⁻ b, f (nU b * mD (a₀ * a)) * M.wt (a₀ * a) ∂(adeleMeasure F) := by
    intro a
    have hwa : M.wt a ≠ ∞ := ENNReal.ofReal_ne_top
    have hwb : M.wt (a₀ * a) ≠ ∞ := ENNReal.ofReal_ne_top
    simp only [key]
    rw [lintegral_mul_const' _ _ hwa, lintegral_mul_const' _ _ hwb,
      lintegral_mul_left_adele (a₀ * a₀) (fun s => f (nU (b₀ + s) * mD (a₀ * a))),
      lintegral_add_left_eq_self (fun s => f (nU s * mD (a₀ * a))) b₀, hc, wt_mul]
    ring
  simp only [inner]
  exact lintegral_mul_left_eq_self
    (fun x : IdeleGroup F => ∫⁻ b, f (nU b * mD x) * M.wt x ∂(adeleMeasure F)) a₀
