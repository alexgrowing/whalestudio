import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalMatrixCoefficientSpan
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_matrixCoefficientSpan : ∀ (K W : Type) [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W), FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  first | exact @GlobalTheory.Proof.CoeffSpan.finiteDimensional_coeffSpan | exact GlobalTheory.Proof.CoeffSpan.finiteDimensional_coeffSpan | (intros; apply GlobalTheory.Proof.CoeffSpan.finiteDimensional_coeffSpan <;> assumption)
