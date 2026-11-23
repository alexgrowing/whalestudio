import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmBilinFormEqZeroOfWeightedQuadraticSumLifts
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symm_bilinForm_eq_zero_of_weightedQuadraticSum_lifts : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (∀ c, qW W b (μ c) = 0) → b = 0 := by
  first | exact @GlobalTheory.Poinc.symm_eq_zero_of_qW_lifts | exact GlobalTheory.Poinc.symm_eq_zero_of_qW_lifts | (intros; apply GlobalTheory.Poinc.symm_eq_zero_of_qW_lifts <;> assumption)
