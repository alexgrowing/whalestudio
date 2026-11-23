import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiperiodicDifferenceSymmetricFamily
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCoefficientHolomorphicInBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicHolomorphicFourierExpansionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCoefficientExponentialDecayLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCharacterUniformlyAwayFromOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiperiodicDifferenceHolomorphicStatement
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.FamilyFourier
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiperiodic_difference_symmetric_family : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap U τ → ∀ h : Fin g → Pt E g → ℂ, (∀ k, DifferentiableOn ℂ (h k) (cov U g)) → (∀ k, ∀ P ∈ cov U g, ∀ i : Fin g, h k (P.1, P.2 + Pi.single i 1) = h k P) → (∀ k m, ∀ P ∈ cov U g, h k (transl τ (Pi.single (Sum.inl m) (1 : ℝ)) P) - h k P = h m (transl τ (Pi.single (Sum.inl k) (1 : ℝ)) P) - h m P) → ∀ b ∈ U, ∃ V : Set E, IsOpen V ∧ b ∈ V ∧ V ⊆ U ∧ ∃ K : Pt E g → ℂ, DifferentiableOn ℂ K (cov V g) ∧ (∀ P ∈ cov V g, ∀ i : Fin g, K (P.1, P.2 + Pi.single i 1) = K P) ∧ ∃ c : Fin g → E → ℂ, (∀ k, DifferentiableOn ℂ (c k) V) ∧ ∀ k, ∀ P ∈ cov V g, h k P = K (transl τ (Pi.single (Sum.inl k) (1 : ℝ)) P) - K P + c k P.1 := by
  first | exact @GlobalTheory.cocycle_core_local_solution | exact GlobalTheory.cocycle_core_local_solution | (intros; apply GlobalTheory.cocycle_core_local_solution <;> assumption)
