import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSmulProdChoose
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_prod_choose_smul_of_choose_relation : ∀ (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M], (∀ m : M, ∃ m', p • m' = m) → (∀ n : ℕ, Nat.Coprime n p → Function.Bijective fun m : M => n • m) → ∀ (d : ℕ) (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M), (∀ a, a ≤ n → c a = c (n - a)) → (∀ a b, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n → (∏ i, Nat.choose ((a + b : Fin d →₀ ℕ) i) (a i)) • c (a + b) = (∏ i, Nat.choose ((n - a : Fin d →₀ ℕ) i) (b i)) • c a) → ∃ g : M, ∀ a, a ≤ n → a ≠ 0 → a ≠ n → c a = (∏ i, Nat.choose (n i) (a i)) • g := by
  first | exact @GlobalTheory.SymCocycleMV.exists_eq_smul_prod_choose | exact GlobalTheory.SymCocycleMV.exists_eq_smul_prod_choose | (intros; apply GlobalTheory.SymCocycleMV.exists_eq_smul_prod_choose <;> assumption)
