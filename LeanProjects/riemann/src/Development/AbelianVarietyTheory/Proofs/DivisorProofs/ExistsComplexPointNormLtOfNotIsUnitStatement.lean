import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexPointNormLtOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SpecialisationNumberFieldAndCountableValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_point_norm_lt_of_not_isUnit' : ∀ (K B : Type) [Field K] [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B] (σ : K →+* ℂ) (n : ℕ) (w : Fin n → B) (u q : B), ¬ IsUnit u → q ≠ 0 → ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ∃ φ : B →+* ℂ, φ.comp (algebraMap K B) = σ ∧ φ q ≠ 0 ∧ ‖φ u‖ < ε ∧ ∀ i, ‖φ (w i)‖ ≤ M := by
  first | exact @GlobalTheory.exists_complex_point_norm_lt_of_not_isUnit | exact GlobalTheory.exists_complex_point_norm_lt_of_not_isUnit | (intros; apply GlobalTheory.exists_complex_point_norm_lt_of_not_isUnit <;> assumption)
