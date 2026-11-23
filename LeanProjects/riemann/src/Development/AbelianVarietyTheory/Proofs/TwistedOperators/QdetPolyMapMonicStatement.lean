import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonic
import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monic_poly_eq_qdet : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), ∃ c : ℕ → A, c n = 1 ∧ ∀ u : ℂ, qdet E u = ∑ i ∈ range (n + 1), u ^ i • c i := by
  first | exact @GlobalTheory.qdet_polyMap_monic | exact GlobalTheory.qdet_polyMap_monic | (intros; apply GlobalTheory.qdet_polyMap_monic <;> assumption)
