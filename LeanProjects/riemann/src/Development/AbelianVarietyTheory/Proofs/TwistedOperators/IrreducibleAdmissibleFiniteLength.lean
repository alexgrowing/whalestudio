import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClosureGKSubmoduleStatement
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

namespace GlobalTheory.HCChar

theorem simple_of_isIrrAdm : GlobalTheory.Published.KFiniteCoefficientsAnalytic → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsIrrAdm ε π →
    (∀ Y : Submodule ℂ H, IsGKSub ε π Y → Y = ⊥ ∨ Y = kFinVec ε π) ∧ HasFiniteLength ε π := by
  intro hA n ε H _ _ _ π hπ
  have key : ∀ Y : Submodule ℂ H, IsGKSub ε π Y → Y = ⊥ ∨ Y = kFinVec ε π := fun Y hY => by
    obtain ⟨h1, h2⟩ := GlobalTheory.T.closure_gK_submodule hA n ε H π hπ.2.1 Y hY
    rcases hπ.2.2 Y.topologicalClosure Y.isClosed_topologicalClosure h1 with e | e
    · left; rw [← h2, e, bot_inf_eq]
    · right; rw [← h2, e, top_inf_eq]
  refine ⟨key, 1, fun r Y hY hm => ?_⟩
  by_contra hr
  have hr : 1 < r := not_le.1 hr
  have a : Y ⟨0, by omega⟩ < Y ⟨1, by omega⟩ := hm (Fin.mk_lt_mk.2 (by omega))
  have b : Y ⟨1, by omega⟩ < Y ⟨2, by omega⟩ := hm (Fin.mk_lt_mk.2 (by omega))
  rcases key _ (hY ⟨1, by omega⟩) with e | e
  · exact not_lt_bot (e ▸ a)
  · rcases key _ (hY ⟨2, by omega⟩) with e' | e'
    · exact not_lt_bot (e' ▸ b)
    · exact b.ne (e.trans e'.symm)

end GlobalTheory.HCChar
