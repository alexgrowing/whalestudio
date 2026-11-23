import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KFiniteCoefficientsAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KFiniteVectorsSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClosureGKSubmoduleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactUnitaryFiniteInvariantSubspace
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.SubquotRep

variable {n : ℕ} {ε : Fin n → Bool} {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

def sqSpace (Z Y : Submodule ℂ X) : Submodule ℂ X := Y.topologicalClosure ⊓ (Z.topologicalClosure)ᗮ

theorem isClosed_sqSpace (Z Y : Submodule ℂ X) : IsClosed (sqSpace Z Y : Set X) :=
  Y.isClosed_topologicalClosure.inter (Submodule.isClosed_orthogonal _)

instance (Z Y : Submodule ℂ X) : CompleteSpace (sqSpace Z Y) := (isClosed_sqSpace Z Y).completeSpace_coe

def sqRep (ρ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (Z Y : Submodule ℂ X) :
    Matrix (Fin n) (Fin n) ℂ → (sqSpace Z Y →L[ℂ] sqSpace Z Y) :=
  fun g => (sqSpace Z Y).orthogonalProjectionOnto ∘L ρ g ∘L (sqSpace Z Y).subtypeL

variable {Z Y : Submodule ℂ X}

variable {ρ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)}

end GlobalTheory.SubquotRep

namespace GlobalTheory.SubquotRep

variable {n : ℕ} {ε : Fin n → Bool} {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
variable {Z Y : Submodule ℂ X} {ρ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)}

end GlobalTheory.SubquotRep

namespace GlobalTheory.SubquotRep

section Transfer

variable {n : ℕ} {ε : Fin n → Bool} {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {ρ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)} {H : Submodule ℂ X}
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

end Transfer

section Exists

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

end Exists

end GlobalTheory.SubquotRep

namespace GlobalTheory.SubquotRep

end GlobalTheory.SubquotRep
