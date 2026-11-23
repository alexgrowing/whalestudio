import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientExistence

noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.Published

def CuspidalOrbitalIntegrals : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (σ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (h : IsSqIntIrr ε σ) (μ : Measure (UJ ε)) [μ.IsHaarMeasure],
    ∀ f ∈ CcMat (ujMat ε), IsBiFinite (KG ε) f → HasPseudoTraces ε μ (ujRep h.2.2.1) f →
    ∀ Θ : UJ ε → ℂ, IsCharFn (ujMat ε) μ (ujRep h.2.2.1) Θ → ∀ s, IsRegSS (ujMat ε s) →
      ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant],
        (IsCompact (cent s : Set (UJ ε)) → HasOrbInt μ s dt f (conj (Θ s) / dt.real Set.univ)) ∧
        (¬ IsCompact (cent s : Set (UJ ε)) → HasOrbInt μ s dt f 0)

end GlobalTheory.Published

end
