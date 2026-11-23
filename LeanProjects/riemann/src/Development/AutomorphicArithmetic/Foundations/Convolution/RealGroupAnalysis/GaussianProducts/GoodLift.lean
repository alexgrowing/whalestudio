import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Expand1
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.TransN
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ThetaFourierCoeffZeroAndEqShiftedWhittaker
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.EAddRight
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.LiftCentre

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem delta_ne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : Dat F E) : D.δ ≠ 0 := by
  intro h0
  have hθ : D.θ = 0 := by
    have h := D.sq
    rw [h0, map_zero] at h
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h
  exact D.b.ne_zero 1 (by rw [D.b1, hθ])

theorem UpperTheory.ConvolutionTheory.R2.G.goodLift :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ThetaLiftTrivialOrbitTermsVanish W M π → ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, Good D (lift W M f.1 φ) := by
  intro F E _ _ _ _ _ _ _ D W M π hN f hf φ hφ
  have hδ : D.δ ≠ 0 := delta_ne D
  have hex := fun h => UpperTheory.ConvolutionTheory.R2.G.expand1 F E D W M π f hf φ hφ h
  have hw := fun h => UpperTheory.ConvolutionTheory.R2.G.thetaFourierCoeff_zero_and_eq_shifted_whittaker F E D W M π f hf φ hφ h
  have ho : ∀ h, _ := fun h => UpperTheory.ConvolutionTheory.R2.G.orth F D.δ hδ 0 (Wx W M f.1 φ h)
    (fun u => lift W M f.1 φ (nE D u * h)) (hex h).1 (fun u => by
      have e := (hex (nE D u * h)).2
      rw [hN f hf φ hφ (nE D u * h)] at e
      rw [e]
      congr 1
      refine tsum_congr fun ξ => ?_
      exact (UpperTheory.ConvolutionTheory.R2.G.transN F E D W M f.1 φ h u).2 ξ)
  have hWE : ∀ h, WE D (lift W M f.1 φ) h = W1 W M f.1 φ h := fun h => by
    have e : WE D (lift W M f.1 φ) h = Wx W M f.1 φ h ![1, 0] := (ho h).2.2.2
    rw [e, (hw h).2.1]
  refine
    { left := (UpperTheory.ConvolutionTheory.R2.equiv F E D W M π f hf φ).1
      int0 := fun h => (ho h).1
      int1 := fun h => (ho h).2.1
      zero := fun h => ?_
      sum := fun h => ?_ }
  · have e := (ho h).2.2.1
    rw [e, (hw h).1, add_zero]
  · have hs : HasSum (fun ξ => Wx W M f.1 φ h ξ) (lift W M f.1 φ h) := by
      have e := (hex h).2
      rw [hN f hf φ hφ h, zero_add] at e
      rw [e]
      exact (Summable.of_norm (hex h).1).hasSum
    have hsup : Function.support (fun ξ => Wx W M f.1 φ h ξ) ⊆ {ξ : Fin 2 → F | ξ ≠ 0} := by
      intro ξ hξ h0
      apply hξ
      have h0' : ξ = 0 := h0
      simpa [h0'] using (hw h).1
    have hs' := (hasSum_subtype_iff_of_support_subset hsup).2 hs
    have hs'' : HasSum (fun ξ : Rw F => Wx W M f.1 φ h ξ.1) (lift W M f.1 φ h) := hs'
    have e : (fun ξ : Rw F => WE D (lift W M f.1 φ) (aE (al D ξ.1) * h)) = fun ξ : Rw F => Wx W M f.1 φ h ξ.1 :=
      funext fun ξ => by
        rw [hWE]
        exact ((hw h).2.2 ξ.1 ξ.2).symm
    rw [e]
    exact hs''
