import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic

noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.Published

def WeylIntegrationSum : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (𝒯 : Finset (Subgroup (UJ ε))),
    IsCartanSystem 𝒯 → ∀ dt : ∀ T : Subgroup (UJ ε), Measure T, (∀ T ∈ 𝒯, (dt T).IsHaarMeasure) →
      ∀ F : UJ ε → ℝ≥0∞, Measurable F →
        ∫⁻ g, F g ∂μ = ∑ T ∈ 𝒯, (weylOrder T : ℝ≥0∞)⁻¹ *
          ∫⁻ t : T, ‖weylDisc (ujMat ε t)‖ₑ * ∫⁻ q, F (q.out⁻¹ * t * q.out) ∂quotMeas T (dt T) μ ∂dt T

end GlobalTheory.Published

end
