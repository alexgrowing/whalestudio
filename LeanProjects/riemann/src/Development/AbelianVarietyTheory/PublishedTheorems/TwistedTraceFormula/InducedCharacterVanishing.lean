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

def InducedCharacterVanishing : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (a : ℕ) (j : Fin a → ℕ) (W : Flag n a),
    IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] [Nontrivial V]
      (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (mats (leviOne ε W)) σ → IsIrredOn (mats (leviOne ε W)) σ →
      ∀ (s : Fin a → ℂ) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
        (ρ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (ι : indFun (ε := ε) ⊤ j W σ s →ₗ[ℂ] X),
        IsIndModel ⊤ (KG ε) (muK ε) _ ρ ι →
        ∀ h : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ, ∃ Θ, IsCharFn (ujMat ε) μ (groupRep ε h) Θ ∧
          ∀ g, IsRegSS (ujMat ε g) → (∀ x, x * g * x⁻¹ ∉ flagM ε W) → Θ g = 0

end GlobalTheory.Published

end
