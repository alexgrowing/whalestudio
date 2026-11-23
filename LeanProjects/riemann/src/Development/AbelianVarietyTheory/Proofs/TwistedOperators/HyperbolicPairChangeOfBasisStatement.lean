import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HyperbolicPairChangeOfBasis
import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_pair_change_of_basis : ∀ (n : ℕ) (ε : Fin n → Bool) (e : Fin n → ℂ), e ≠ 0 → star e ⬝ᵥ (Jm ε *ᵥ e) = 0 → ∃ (P : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (c : ℂ), IsUnit P ∧ p ≠ q ∧ P *ᵥ Pi.single p 1 = e ∧ P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ e) ∧ ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) → (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0 := by
  first | exact @GlobalTheory.IsotropicPartner.exists_adapted_basis | exact GlobalTheory.IsotropicPartner.exists_adapted_basis | (intros; apply GlobalTheory.IsotropicPartner.exists_adapted_basis <;> assumption)
