import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersOfGenerators
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPreDividedPowers_of_generators : ∀ (B ι : Type) [CommRing B] (x : ι → B) (g : ι → ℕ → B), (∀ i, g i 0 = 1) → (∀ i, g i 1 = x i) → (∀ i n, n ≠ 0 → g i n ∈ Ideal.span (Set.range x)) → (∀ i m n, g i m * g i n = ((m + n).choose m : B) * g i (m + n)) → (∀ c : ι →₀ B, (c.sum fun i a ↦ a * x i) = 0 → (c.prod fun i a ↦ PowerSeries.mk fun n ↦ a ^ n * g i n) = 1) → ∃ γ : ℕ → B → B, IsPreDP (Ideal.span (Set.range x)) γ ∧ ∀ i n, γ n (x i) = g i n := by
  first | exact @GlobalTheory.PDA.exists_isPreDividedPowers_of_generators₂ | exact GlobalTheory.PDA.exists_isPreDividedPowers_of_generators₂ | (intros; apply GlobalTheory.PDA.exists_isPreDividedPowers_of_generators₂ <;> assumption)
