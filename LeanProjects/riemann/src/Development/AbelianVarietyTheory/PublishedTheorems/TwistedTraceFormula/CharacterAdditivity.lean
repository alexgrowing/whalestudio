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

def CharacterAdditivity : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (hρ : IsAdmRep ε ρ) (r : ℕ) (Y : Fin (r + 1) → Submodule ℂ X)
    (H : Fin r → Type) [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]
    (π : ∀ i, Matrix (Fin n) (Fin n) ℂ → (H i →L[ℂ] H i)) (hπ : ∀ i, IsIrrAdm ε (π i)),
    Y 0 = ⊥ → Y (Fin.last r) = kFinVec ε ρ → (∀ i, IsFactor ε ρ (Y i.castSucc) (Y i.succ) (π i)) →
    ∀ (μ : Measure (UJ ε)) [μ.IsHaarMeasure], ∀ f ∈ CcMat (ujMat ε),
      (∀ i, IsTraceClass (repOp (groupRep ε (hπ i).2.1.1) μ f)) ∧
      HasTrace (repOp (groupRep ε hρ.1) μ f) (∑ i, trace (repOp (groupRep ε (hπ i).2.1.1) μ f))

end GlobalTheory.Published

end
