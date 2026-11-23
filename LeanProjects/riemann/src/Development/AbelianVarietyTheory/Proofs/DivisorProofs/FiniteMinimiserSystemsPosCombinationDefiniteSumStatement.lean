import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsPosCombinationDefiniteSum
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
open GlobalTheory.PolFan GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_minimiserSystems_posCombination_definiteSum : ∀ (Y : Type) [AddCommGroup Y] (n N : ℕ) [NeZero N] (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ Y), (∀ j x y, γ j x y = γ j y x) → (∀ j y, 0 ≤ γ j y y) → (∀ x, x ≠ 0 → 0 < ∑ j, γ j x x) → ∃ S : Finset ((Fin n → ZMod N) → Y), ∀ (b : LinearMap.BilinForm ℤ Y) (k : ℕ) (cf : Fin m → ℕ), 0 < k → (∀ j, 0 < cf j) → k • b = ∑ j, cf j • γ j → ∀ μ : (Fin n → ZMod N) → Y, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → μ ∈ S := by
  first | exact @GlobalTheory.Poinc.MinSysLat.finite_minimiser_systems_lat | exact GlobalTheory.Poinc.MinSysLat.finite_minimiser_systems_lat | (intros; apply GlobalTheory.Poinc.MinSysLat.finite_minimiser_systems_lat <;> assumption)
