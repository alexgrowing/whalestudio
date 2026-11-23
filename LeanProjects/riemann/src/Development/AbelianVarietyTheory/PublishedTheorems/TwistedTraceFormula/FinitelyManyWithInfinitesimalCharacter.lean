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

def FinitelyManyWithInfinitesimalCharacter : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (χ : Fin n → ℂ), ∃ N : ℕ,
    ∀ (H : Fin (N + 1) → Type) [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
      [∀ i, CompleteSpace (H i)] (π : ∀ i, Matrix (Fin n) (Fin n) ℂ → (H i →L[ℂ] H i)),
      (∀ i, IsIrrAdm ε (π i) ∧ HasInfChar ε χ (π i)) →
      ∃ i l, i ≠ l ∧ IsFactor ε (π i) ⊥ (kFinVec ε (π i)) (π l)

end GlobalTheory.Published

end
