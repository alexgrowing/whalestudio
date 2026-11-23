import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKProjectorFiniteDim
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleUnitaryAdmissible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientExistence
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_K_projector_finite_dim : GlobalTheory.Published.IrreducibleUnitaryAdmissible → ∀ (n : ℕ) (ε : Fin n → Bool) (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π → ∀ S : Submodule ℂ U, FiniteDimensional ℂ S → (∀ k ∈ KG ε, ∀ u ∈ S, π k u ∈ S) → ∃ φ : KG ε → ℂ, Continuous φ ∧ (∀ s ∈ S, ∫ k, φ k • π k s ∂(muK ε) = s) ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun u : U => ∫ k, φ k • π k u ∂(muK ε))) := by
  first | exact @GlobalTheory.KAvgFinite.fix_and_finite_range | exact GlobalTheory.KAvgFinite.fix_and_finite_range | (intros; apply GlobalTheory.KAvgFinite.fix_and_finite_range <;> assumption)
