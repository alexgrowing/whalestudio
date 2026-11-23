import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMulPowLeFinrankOfPowerSeries
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_mul_pow_le_finrank_of_prod_mem : ∀ (D n : ℕ) (A : Type) [CommRing A] [Algebra ℂ A] (φ : Fin n → (A →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)) (x : Fin D → A) (c : Fin D → ℂ), (∀ u : A, (∀ j, φ j u = 0) → u = 0) → (∀ j i, φ j (x i) = MvPowerSeries.X i + MvPowerSeries.C (c i)) → ∀ (F G : Submodule ℂ A) [Module.Finite ℂ F] [Module.Finite ℂ G] (m : ℕ), 0 < m → (∀ (f : Fin m → A) (a : Fin D → ℕ), (∀ l, f l ∈ F) → (∀ i, a i < m) → (∏ l, f l) * ∏ i, x i ^ a i ∈ G) → Module.finrank ℂ F * m ^ D ≤ Module.finrank ℂ G := by
  first | exact @GlobalTheory.finrank_mul_pow_le_finrank_of_powerSeries | exact GlobalTheory.finrank_mul_pow_le_finrank_of_powerSeries | (intros; apply GlobalTheory.finrank_mul_pow_le_finrank_of_powerSeries <;> assumption)
