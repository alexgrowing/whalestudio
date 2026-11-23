import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlHomNnrealTrivialOfScalarTrivial
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gl_hom_nnreal_trivial_of_scalar_trivial : ∀ (k : Type) [Field k], (∃ x : k, x ≠ 0 ∧ x ≠ 1) → ∀ (N : ℕ) (φ : GL (Fin N) k →* NNReal), (∀ z : kˣ, φ (Matrix.GeneralLinearGroup.scalar (Fin N) z) = 1) → ∀ g, φ g = 1 := by
  first | exact @GlobalTheory.gl_hom_nnreal_trivial_of_scalar | exact GlobalTheory.gl_hom_nnreal_trivial_of_scalar | (intros; apply GlobalTheory.gl_hom_nnreal_trivial_of_scalar <;> assumption)
