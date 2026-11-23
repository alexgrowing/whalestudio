import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealBilinFormEqSumAdditiveImageIntForms
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
open GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realBilinForm_eq_sum_additive_image_intForms : ∀ {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] (B : L →ₗ[ℤ] L →ₗ[ℤ] ℝ), ∃ (n : ℕ) (w : Fin n → ℝ) (Q : Fin n → LinearMap.BilinForm ℤ L), B = ∑ j, w j • toReal (Q j) ∧ ∀ j, ∃ g : ℝ →+ ℝ, ∀ y z, (Q j y z : ℝ) = g (B y z) := by
  first | exact @GlobalTheory.PolFan.exists_sum_toReal_additive_images | exact GlobalTheory.PolFan.exists_sum_toReal_additive_images | (intros; apply GlobalTheory.PolFan.exists_sum_toReal_additive_images <;> assumption)
