import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCharacterEqExpRiemannForm
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_character_eq_exp_riemann_form : ∀ {g : ℕ} {M : Submodule ℤ (Fl g)}, IsLat M → ∀ χ : Fl g → ℂ, (∀ l ∈ M, ‖χ l‖ = 1) → (∀ l ∈ M, ∀ l' ∈ M, χ (l + l') = χ l * χ l') → ∃ x : Fl g, ∀ l ∈ M, χ l = Complex.exp (2 * π * Complex.I * riem x l) := by
  first | exact @GlobalTheory.unitary_char_eq_exp_riem | exact GlobalTheory.unitary_char_eq_exp_riem | (intros; apply GlobalTheory.unitary_char_eq_exp_riem <;> assumption)
