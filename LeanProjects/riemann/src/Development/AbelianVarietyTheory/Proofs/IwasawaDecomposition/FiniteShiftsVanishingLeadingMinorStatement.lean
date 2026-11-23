import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteShiftsVanishingLeadingMinor
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_shifts_vanishing_leading_minor : ∀ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ), Set.Finite {s : ℂ | ¬ ∀ (k : ℕ) (hk : k ≤ n), ((B + s • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0} := by
  first | exact @GlobalTheory.shift_minors_vanish_finite | exact GlobalTheory.shift_minors_vanish_finite | (intros; apply GlobalTheory.shift_minors_vanish_finite <;> assumption)
