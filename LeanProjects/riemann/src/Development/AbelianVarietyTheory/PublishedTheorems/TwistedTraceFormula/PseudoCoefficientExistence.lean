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

def IsTemperedKFin {n : ℕ} (ε : Fin n → Bool) (μ : Measure (UJ ε)) {U : Type} [NormedAddCommGroup U]
    [InnerProductSpace ℂ U] (π : UJ ε →* (U →L[ℂ] U)) : Prop :=
  ∀ S : Submodule ℂ U, FiniteDimensional ℂ S → (∀ k ∈ KG ε, ∀ u ∈ S, π k u ∈ S) →
    ∀ v ∈ S, ∀ w ∈ S, ∀ e : ℝ, 0 < e → Integrable (fun g => ‖⟪w, π g v⟫_ℂ‖ ^ (2 + e)) μ

def HasPseudoTraces {n : ℕ} (ε : Fin n → Bool) (μ : Measure (UJ ε)) {X : Type} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X] (D : UJ ε →* (X →L[ℂ] X)) (f : UJ ε → ℂ) : Prop :=
  HasTrace (repOp D μ f) 1 ∧
    ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)),
      IsUnitaryRep π → IsTopIrreducible π → IsTemperedKFin ε μ π → ¬ IsUnitEquiv π D → HasTrace (repOp π μ f) 0

def PseudoCoefficientExistence : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (σ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (h : IsSqIntIrr ε σ) (μ : Measure (UJ ε)) [μ.IsHaarMeasure],
    ∃ f ∈ CcMat (ujMat ε), IsBiFinite (KG ε) f ∧ HasPseudoTraces ε μ (ujRep h.2.2.1) f

end GlobalTheory.Published

end
