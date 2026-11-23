import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamifiedDivisibilityOfUnramifiedDivisibility
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral
open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramified_divisibility_of_unramified_divisibility : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (v : Valuation Ω ℝ≥0) (ψ : O0 p →+* Ω) (E F : ℕ) (π : Ω) (κ : Fin F → Ω), 1 ≤ E → 0 < v (p : Ω) → v (p : Ω) < 1 → v π ^ E = v (p : Ω) → (∀ j, v (κ j) ≤ 1) → (∀ y, v (ψ y) ≤ 1) → (∀ b : Fin F → Lau p, v (∑ j, κ j * ψ (algebraMap (Lau p) (O0 p) (b j))) < 1 → ∀ j, (p : Lau p) ∣ b j) → ∀ b : Fin F → Fin E → Lau p, v (∑ j, ∑ s : Fin E, κ j * π ^ (s : ℕ) * ψ (algebraMap (Lau p) (O0 p) (b j s))) ≤ v (p : Ω) → ∀ j s, (p : Lau p) ∣ b j s := by
  first | exact @GlobalTheory.KZ.ramified_divisible_of_unramified | exact GlobalTheory.KZ.ramified_divisible_of_unramified | (intros; apply GlobalTheory.KZ.ramified_divisible_of_unramified <;> assumption)
