import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsActionOnRowWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight : ∀ (R : Type) [CommRing R] (r n : ℕ) (μ : Fin r → ℕ) (f : MvPolynomial (Fin r × Fin n) R), IsWeightedHomogeneous (rowW r n) f μ → (∀ a, rowE R r n a a f = (μ a : R) • f) ∧ ∀ a b, a ≠ b → (μ b = 0 → rowE R r n a b f = 0) ∧ ∀ μ' : Fin r → ℕ, μ' + Pi.single b 1 = μ + Pi.single a 1 → IsWeightedHomogeneous (rowW r n) (rowE R r n a b f) μ' := by
  first | exact @GlobalTheory.Alc.rowE_rowWeight | exact GlobalTheory.Alc.rowE_rowWeight | (intros; apply GlobalTheory.Alc.rowE_rowWeight <;> assumption)
