import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianMatricesDvdSq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_hermitian_matrices_dvd_sq : ∀ {A : Type} [CommRing A] [Finite A] (c : A →+* A), (∀ u, c (c u) = u) → ∀ (ω : A), IsUnit (ω - c ω) → ∀ (p : A), c p = p → ∀ (m : ℕ), Nat.card {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} ^ 2 = Nat.card {u : A // p ∣ u} ^ (m * m) := by
  first | exact @GlobalTheory.GramCount.card_hermitian_dvd_sq | exact GlobalTheory.GramCount.card_hermitian_dvd_sq | (intros; apply GlobalTheory.GramCount.card_hermitian_dvd_sq <;> assumption)
