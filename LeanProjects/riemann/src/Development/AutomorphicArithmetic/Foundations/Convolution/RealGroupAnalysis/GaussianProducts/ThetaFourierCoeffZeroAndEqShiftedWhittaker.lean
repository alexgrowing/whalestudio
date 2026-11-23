import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.PtMove
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsMore
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.One
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.CuspZero

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem normOneIntegral_diagonal_invariant {F : Type} [Field F] [NumberField F] (M₀ : Meas F) (t : IdeleGroup F) (ht : ab t = 1)
    (v : G1 F → ℂ) : M₀.I0 (fun g => v (mD t * g)) = M₀.I0 v := by
  haveI := M₀.prob
  let e : (IdeleGroup F × G1 F) ≃ᵐ (IdeleGroup F × G1 F) :=
    (MeasurableEquiv.mulLeft t).prodCongr (MeasurableEquiv.refl _)
  have hp : MeasurePreserving e M₀.ν M₀.ν :=
    (measurePreserving_mul_left (ideleMeasure F) t).prod (MeasurePreserving.id M₀.κ)
  have hi := hp.integral_comp' (g := iw v)
  rw [Meas.I0, Meas.I0, ← hi]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  change iw (fun g => v (mD t * g)) p = iw v (t * p.1, p.2)
  simp only [iw]
  rw [M.ab_mul, ht, one_mul, M.mD_mul, mul_assoc]

theorem UpperTheory.ConvolutionTheory.R2.G.thetaFourierCoeff_zero_and_eq_shifted_whittaker :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h, Wx W M f.1 φ h 0 = 0 ∧ Wx W M f.1 φ h ![1, 0] = W1 W M f.1 φ h ∧
    ∀ ξ, ξ ≠ 0 → Wx W M f.1 φ h ξ = W1 W M f.1 φ (aE (al D ξ) * h) := by
  intro F E _ _ _ _ _ _ _ D W M₀ π f hf φ hφ h
  obtain ⟨hL, hz⟩ := Pp.cuspZero F π f hf
  refine ⟨?_, ?_, fun ξ hξ => ?_⟩
  · have e : wx W f.1 φ h 0 = fun _ => 0 := by
      funext g
      have h1 : ∀ b : A F, ψ (rt ((0 : Fin 2 → F) 0 ^ 2 - D.δ * (0 : Fin 2 → F) 1 ^ 2) * b) = 1 := by
        intro b
        simp [ψ]
      simp only [wx, h1, mul_one, hz, zero_mul]
    simp [Wx, e, Meas.I0, iw]
  · have e : wx W f.1 φ h ![1, 0] = w1 W f.1 φ h := by
      funext g
      simp [wx, w1, Wf, pt]
    rw [Wx, e, W1]
  · obtain ⟨t, ht⟩ := wxPt F E D W ξ hξ
    obtain ⟨-, -, a1, a2, a3⟩ := UpperTheory.ConvolutionTheory.R2.conv F E D W M₀ π f hf φ hφ (aE (al D ξ) * h)
    have hc := ((UpperTheory.ConvolutionTheory.R2.inv F M₀ _ a1 a2 a3).2 (IdeleGroup.diagonal F t)).2
    have e : wx W f.1 φ h ξ = fun g => (fun g => w1 W f.1 φ (aE (al D ξ) * h) (cD (IdeleGroup.diagonal F t) g)) (mD (IdeleGroup.diagonal F t) * g) :=
      funext fun g => (ht f.1 hL φ h g).symm
    have hm := normOneIntegral_diagonal_invariant M₀ (IdeleGroup.diagonal F t) (ab_diagonal t)
      (fun g => w1 W f.1 φ (aE (al D ξ) * h) (cD (IdeleGroup.diagonal F t) g))
    rw [Wx, e, hm, hc, W1, ab_diagonal t]
    simp
