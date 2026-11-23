import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightFunctionalCharacter
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_functional_character : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ), GlRel E → (∀ (Y : ℂ) (v : V), qdet E (Y + ((n : ℂ) - 1) / 2) v = (∏ s, (Y + χ s)) • v) → ∀ (p q : Fin n), p ≠ q → ∀ (ℓ : V →ₗ[ℂ] ℂ) (α β : ℂ), ℓ ≠ 0 → (∀ b, b ≠ p → ∀ v, ℓ (E p b v) = 0) → (∀ a, a ≠ q → ∀ v, ℓ (E a q v) = 0) → (∀ v, ℓ (E p p v) = α * ℓ v) → (∀ v, ℓ (E q q v) = β * ℓ v) → ∃ i j, i ≠ j ∧ χ i = α - ((n : ℂ) - 1) / 2 ∧ χ j = β + ((n : ℂ) - 1) / 2 := by
  first | exact @GlobalTheory.CapelliRoots.two_roots_of_parabolic_functional | exact GlobalTheory.CapelliRoots.two_roots_of_parabolic_functional | (intros; apply GlobalTheory.CapelliRoots.two_roots_of_parabolic_functional <;> assumption)
