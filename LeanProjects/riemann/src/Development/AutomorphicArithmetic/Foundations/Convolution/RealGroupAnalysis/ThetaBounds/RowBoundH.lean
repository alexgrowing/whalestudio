import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.RowMaj
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.RedH
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThMeas
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Iwa
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsRest
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.UnitsCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.rowBoundH :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (π : TR.CuspSub F 2), RowBoundH W π := by
  intro F E _ _ _ _ _ _ _ D W π f hf φ hφ h x
  obtain ⟨y, hy, φ₁, hφ₁, m, e⟩ := redH F E D W h φ hφ
  obtain ⟨c, hc, hred⟩ := UpperTheory.ConvolutionTheory.R2.red F
  obtain ⟨B₁, hB₁⟩ := rowMaj F E D W φ₁ hφ₁ y hy c hc
  have hC : IsCompact ((fun k : G1 F => gl k * ((gl m)⁻¹ * x)) '' KK F) :=
    (iwa F).1.image (M.continuous_gl.mul continuous_const)
  obtain ⟨B₂, hB₂⟩ := (UpperTheory.ConvolutionTheory.R2.decay F π f hf).2 _ hC c hc 1
  have hinv := (thMeas F E D W (W.L (infGL E 2 y) φ₁)).2.2.2.1
  refine ⟨B₂ * B₁, fun g => ?_⟩
  have e1 : W.Om g (W.L h φ) = W.Om (g * m) (W.L (infGL E 2 y) φ₁) := by
    simpa using e g 1
  obtain ⟨γ, b, a, k, hk, ek, ha⟩ := hred (g * m)
  have e2 : ThRow 0 0 (W.Om g (W.L h φ)).1 =
      ThRow 0 0 (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ₁)).1 := by
    rw [e1, ← ek]
    exact (hinv γ (g * m)).symm
  have e3 : f.1 (gl g * x) = f.1 (gl (nU b * mD a) * (gl k * ((gl m)⁻¹ * x))) := by
    have e4 : gl (nU b * mD a) * (gl k * ((gl m)⁻¹ * x)) =
        ratGL F 2 (Matrix.SpecialLinearGroup.toGL γ) * (gl g * x) := by
      have e5 : ratGL F 2 (Matrix.SpecialLinearGroup.toGL γ) = gl (ratS F γ) := Units.ext rfl
      rw [← mul_assoc, ← gl_mul, ← mul_assoc, ← ek, gl_mul, gl_mul, e5]
      group
    rw [e4]
    exact ((π.cusp _ hf).1.left _ _).symm
  rw [norm_mul, e2, e3]
  have hp := M.ab_pos a
  have h1 := hB₁ b a k hk ha
  have h2 := hB₂ b a _ ⟨k, hk, rfl⟩ ha
  calc _ ≤ (B₂ * (ab a)⁻¹ ^ 1) * (B₁ * ab a) :=
        mul_le_mul h2 h1 (norm_nonneg _) ((norm_nonneg _).trans h2)
    _ = B₂ * B₁ := by field_simp
