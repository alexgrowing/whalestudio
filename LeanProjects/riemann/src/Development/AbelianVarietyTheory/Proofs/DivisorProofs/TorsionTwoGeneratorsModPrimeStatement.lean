import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTwoGeneratorsModPrime
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_two_generators_mod_prime : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N → Finite {x : M // N • x = 0} →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
    Nat.card {x : M // ∀ a ∈ 𝔭, a • x = 0} ≤ Ideal.absNorm 𝔭 ^ 2 →
    ∃ u v : M, N • u = 0 ∧ N • v = 0 ∧ ∀ x : M, N • x = 0 → ∃ a b : 𝓞 F,
      x - a • u - b • v ∈ 𝔭 • Submodule.torsionBy (𝓞 F) M (N : 𝓞 F) := by
  first | exact @GlobalTheory.torsionBy_two_generators_mod_prime | exact GlobalTheory.torsionBy_two_generators_mod_prime | (intros; apply GlobalTheory.torsionBy_two_generators_mod_prime <;> assumption)
