import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.StandardModuleConstituents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalInvariantSubspace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothIntertwinerExtension

noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.StdMult

variable {n : ℕ} {ε : Fin n → Bool}

section Transport

variable {H H' K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
  [InnerProductSpace ℂ H'] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ρ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

def toReal (U : H ≃ₗᵢ[ℂ] H') : H ≃L[ℝ] H' :=
  { U.toLinearEquiv.restrictScalars ℝ with
    continuous_toFun := U.continuous
    continuous_invFun := U.symm.continuous }

@[simp] theorem toReal_apply (U : H ≃ₗᵢ[ℂ] H') (x : H) : toReal U x = U x := rfl

variable (U : H ≃ₗᵢ[ℂ] H') (hU : ∀ g ∈ UJset ε, ∀ v, U (ρ g v) = ρ' g (U v))
include hU

end Transport

end GlobalTheory.StdMult

namespace GlobalTheory.StdMult

variable {n : ℕ} {ε : Fin n → Bool}

section Equivalent

variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
  [InnerProductSpace ℂ V']

end Equivalent

section Chains

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup K]
  [InnerProductSpace ℂ K] {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
  {π : Matrix (Fin n) (Fin n) ℂ → (K →L[ℂ] K)}

end Chains

end GlobalTheory.StdMult

end
