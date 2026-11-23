import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.UnitsCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsMore
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Vol
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThMeas
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WeilLiftOneCuspidal
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThBoundH
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.RowBoundH
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.RedH

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.conv :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Conv W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h
  have hc : Continuous fun g : G1 F => f.1 (gl g * dM (nu F h)) :=
    (decay F π f hf).1.comp (Matrix.SpecialLinearGroup.continuous_toGL.mul continuous_const)
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using vol F M⟩
  obtain ⟨m1, -, m2, -, -⟩ := thMeas F E D W (W.L h φ)
  obtain ⟨a1, a2, -⟩ := weilLift_one_cuspidal F E D W M π f hf (W.L h φ) (dM (nu F h))
  refine ⟨?_, ?_, a1, a2, ?_⟩
  · obtain ⟨B, hB⟩ := thBoundH F E D W π f hf φ hφ h {dM (nu F h)} isCompact_singleton {1} isCompact_singleton
      (by rintro _ rfl; simp [Ff.One, nu])
    refine Integrable.of_bound (hc.measurable.mul m1).aestronglyMeasurable B (ae_of_all _ fun g => ?_)
    simpa using hB g _ rfl 1 rfl
  · obtain ⟨B, hB⟩ := rowBoundH F E D W π f hf φ hφ h (dM (nu F h))
    exact Integrable.of_bound (hc.measurable.mul (m2 0 0)).aestronglyMeasurable B (ae_of_all _ hB)
  · obtain ⟨y, hy, φ₁, h₁, m, hm⟩ := redH F E D W h φ hφ
    obtain ⟨b1, b2, -⟩ := weilLift_one_cuspidal F E D W M π f hf (W.L (infGL E 2 y) φ₁) ((gl m)⁻¹ * dM (nu F h))
    have b3 := (weilLift_one_cuspidal F E D W M π f hf φ₁ ((gl m)⁻¹ * dM (nu F h))).2.2 h₁ y hy
    have := ((inv F M _ b1 b2 b3).1 m).1
    have e : w1 W f.1 φ h = fun g => Wf f.1 (gl (g * m) * ((gl m)⁻¹ * dM (nu F h))) *
        hat (W.Om (g * m) (W.L (infGL E 2 y) φ₁)).1 ![0, 1, 1, 0] := by
      funext g
      have h2 := hm g 1
      simp only [map_one, mul_one] at h2
      rw [w1, h2, show gl (g * m) = gl g * gl m from map_mul _ _ _, mul_assoc, mul_inv_cancel_left]
    rw [e]
    exact this
