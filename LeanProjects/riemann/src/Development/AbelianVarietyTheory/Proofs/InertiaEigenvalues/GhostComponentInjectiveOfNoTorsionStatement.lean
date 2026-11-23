import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GhostComponentInjectiveOfNoTorsion
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittVector_eq_of_ghostComponent_eq_of_no_torsion : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A], (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) → ∀ x y : WittVector l A, (∀ n, WittVector.ghostComponent n x = WittVector.ghostComponent n y) → x = y := by
  first | exact @GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion | exact GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion | (intros; apply GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion <;> assumption)
