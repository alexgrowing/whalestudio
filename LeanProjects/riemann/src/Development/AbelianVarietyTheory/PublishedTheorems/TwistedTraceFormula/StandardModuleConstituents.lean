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

def paramSum {n : ℕ} {ε : Fin n → Bool} (D : Datum ε) (d : ℕ) : ℝ :=
  ∑ i, (D.s i).re * (((min d (∑ l ∈ Finset.Iic i, D.j l) : ℕ) : ℝ) - ((min d (∑ l ∈ Finset.Iio i, D.j l) : ℕ) : ℝ))

def StandardModuleConstituents : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (b : ℕ) (W₀ : Flag n b), IsMinimalFlag ε W₀ →
    ∀ I I' : IndModule ε, I.IsStandard W₀ → I'.IsStandard W₀ →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsIrrAdm ε π →
      ∀ Z', IsFactor ε I'.ρ Z' (kFinVec ε I'.ρ) π → ∀ Z Y, Y ≠ kFinVec ε I.ρ → IsFactor ε I.ρ Z Y π →
        (∀ d, paramSum I'.toDatum d ≤ paramSum I.toDatum d) ∧ ∃ d, paramSum I'.toDatum d < paramSum I.toDatum d

example (s : ℂ) : paramSum (sphericalDatum s) 1 = s.re := by
  have h : ∑ i : Fin 1, ((![s] : Fin 1 → ℂ) i).re * (((min 1 (∑ l ∈ Finset.Iic i, (![1] : Fin 1 → ℕ) l) : ℕ) : ℝ) -
      ((min 1 (∑ l ∈ Finset.Iio i, (![1] : Fin 1 → ℕ) l) : ℕ) : ℝ)) = s.re := by
    simp
  exact h

end GlobalTheory.Published

end
