import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClosureGKSubmodule
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KFiniteCoefficientsAnalytic
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_gK_submodule : GlobalTheory.Published.KFiniteCoefficientsAnalytic → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε π → ∀ Y : Submodule ℂ H, IsGKSub ε π Y → (∀ g ∈ UJset ε, ∀ v ∈ Y.topologicalClosure, π g v ∈ Y.topologicalClosure) ∧ Y.topologicalClosure ⊓ kFinVec ε π = Y := by
  first | exact @GlobalTheory.GKClosure.topologicalClosure_stable_inf_kFinVec | exact GlobalTheory.GKClosure.topologicalClosure_stable_inf_kFinVec | (intros; apply GlobalTheory.GKClosure.topologicalClosure_stable_inf_kFinVec <;> assumption)
