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

def TemperedSubrepresentation : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (D : Datum ε), ∃ (b : ℕ) (W' : Flag n b), IsIsoFlag ε (fun _ => 1) W' ∧
    (∀ i, D.W i ∈ Set.range W') ∧
    ∃ (U : Type) (_ : NormedAddCommGroup U) (_ : InnerProductSpace ℂ U) (_ : CompleteSpace U)
      (τ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U)) (y : Fin b → ℝ), IsIrrTempered (leviOne ε W') τ ∧
      ∀ μ : Measure ↥(KG ε ⊓ D.M), μ.IsHaarMeasure → IsProbabilityMeasure μ →
        ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
          (ρ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (ι : indFun D.M (fun _ => 1) W' τ (fun l => Complex.I * y l) →ₗ[ℂ] X),
          IsIndModel D.M (KG ε ⊓ D.M) μ _ ρ ι →
          ∃ T : D.V →ₗᵢ[ℂ] X, ∀ m ∈ D.M, ∀ v, T (D.σ (uMat m) v) = ρ (uMat m) (T v)

end GlobalTheory.Published

end
