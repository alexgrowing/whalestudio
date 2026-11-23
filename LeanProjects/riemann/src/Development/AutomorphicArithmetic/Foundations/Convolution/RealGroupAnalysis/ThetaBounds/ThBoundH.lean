import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThBound
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.RedH
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.NormMatrixMulLeTwo
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem one_mul_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] {y y' : GL (Fin 2) (Cinf E)} (hy : Ff.One F y) (hy' : Ff.One F y') :
    Ff.One F (y * y') := by
  unfold Ff.One nu at *
  rw [map_mul, map_mul, map_mul, hy, hy', _root_.one_mul]

theorem UpperTheory.ConvolutionTheory.R2.Ff.thBoundH :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (π : TR.CuspSub F 2), ThBoundH W π := by
  intro F E _ _ _ _ _ _ _ D W π f hf φ hφ h C hC C' hC' hOne
  obtain ⟨y₀, hy₀, φ₁, hφ₁, m, hred⟩ := redH F E D W h φ hφ
  obtain ⟨B, N, hB⟩ := thBound F E D W π f hf φ₁ hφ₁ ((fun x => (gl m)⁻¹ * x) '' C)
    (hC.image (continuous_const.mul continuous_id))
  obtain ⟨M, hM⟩ := (hC'.image (htLe E).1).bddAbove
  refine ⟨|B| * (2 * Ht y₀ * |M|) ^ N, fun g x hx y hy => ?_⟩
  have e : gl g * x = gl (g * m) * ((gl m)⁻¹ * x) := by
    rw [gl_mul, _root_.mul_assoc, mul_inv_cancel_left]
  rw [hred g y, e]
  refine (hB _ (one_mul_one hy₀ (hOne y hy)) (g * m) _ ⟨x, hx, rfl⟩).trans ?_
  have h1 : 1 ≤ Ht (y₀ * y) := ((htLe E).2 _).1
  have h2 : Ht (y₀ * y) ≤ 2 * Ht y₀ * Ht y := ((htLe E).2 y₀).2.2 y
  have h3 : Ht y ≤ |M| := (hM ⟨y, hy, rfl⟩).trans (le_abs_self M)
  have h4 : 1 ≤ Ht y₀ := ((htLe E).2 y₀).1
  have h5 : Ht (y₀ * y) ≤ 2 * Ht y₀ * |M| :=
    h2.trans (mul_le_mul_of_nonneg_left h3 (by linarith))
  have h6 : Ht (y₀ * y) ^ N ≤ (2 * Ht y₀ * |M|) ^ N :=
    pow_le_pow_left₀ (by linarith) h5 N
  calc B * Ht (y₀ * y) ^ N ≤ |B| * Ht (y₀ * y) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
    _ ≤ |B| * (2 * Ht y₀ * |M|) ^ N := mul_le_mul_of_nonneg_left h6 (abs_nonneg B)
