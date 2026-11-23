import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLiftNumberFieldModuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCountLogConcavePrimePowersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCountMultiplicativePrimePowersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogConcaveMultiplicativeGrowthBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTwoGeneratorsModPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTwoGeneratorsGlobalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionBasisRelationsDivisibleStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RankTwoTorsion

theorem ptorsion_sub (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M]
    (N : ℕ) (𝔭 : Ideal (𝓞 F)) (hN𝔭 : (N : 𝓞 F) ∈ 𝔭) (n : ℕ) (x : M) (hx : ∀ a ∈ 𝔭 ^ n, a • x = 0) :
    (N ^ n) • x = 0 := by
  have := hx _ (Ideal.pow_mem_pow hN𝔭 n)
  rwa [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at this

theorem rank_two_torsion (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M]
    (N : ℕ) (hN : 1 ≤ N)
    (h2 : ∀ j : ℕ, Nat.card {x : M // (N ^ j) • x = 0} = (N ^ j) ^ (2 * Module.finrank ℚ F))
    (h3 : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 → ∃ C : ℕ, ∀ n : ℕ,
      Nat.card {x : M // ∀ a ∈ 𝔭 ^ n, a • x = 0} ≤ C * Ideal.absNorm 𝔭 ^ (2 * n)) :
    ∃ p : Fin 2 → M, (∀ i, N • p i = 0) ∧
      (∀ a b : 𝓞 F, a • p 0 + b • p 1 = 0 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧
      ∀ y : M, N • y = 0 → ∃ a b : 𝓞 F, y = a • p 0 + b • p 1 := by
  have hfin : ∀ j : ℕ, Finite {x : M // (N ^ j) • x = 0} := fun j => by
    apply Nat.finite_of_card_ne_zero
    rw [h2 j]; positivity
  have hdiv := GlobalTheory.T.torsion_lift_number_field_module F M N hN h2
  have hfin1 : Finite {x : M // N • x = 0} := by simpa using hfin 1
  have hp : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
      Nat.card {x : M // ∀ a ∈ 𝔭, a • x = 0} ≤ Ideal.absNorm 𝔭 ^ 2 := by
    intro 𝔭 h𝔭 hN𝔭
    obtain ⟨C, hC⟩ := h3 𝔭 h𝔭 hN𝔭
    obtain ⟨e, he, hblk⟩ := GlobalTheory.T.torsion_count_multiplicative_prime_powers F M N hN hfin hdiv 𝔭 h𝔭 hN𝔭
    have hfinp : ∀ n, Finite {x : M // ∀ a ∈ 𝔭 ^ n, a • x = 0} := fun n =>
      Finite.of_injective (fun x => (⟨x.1, ptorsion_sub F M N 𝔭 hN𝔭 n x.1 x.2⟩ :
        {x : M // (N ^ n) • x = 0})) (fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h))
    have h0 : Nat.card {x : M // ∀ a ∈ 𝔭 ^ 0, a • x = 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨0, fun a _ => smul_zero a⟩⟩⟩
      have hx := x.2 1 (by simp); have hy := y.2 1 (by simp)
      simp only [one_smul] at hx hy; rw [hx, hy]
    have := GlobalTheory.T.log_concave_multiplicative_growth_bound (fun n => Nat.card {x : M // ∀ a ∈ 𝔭 ^ n, a • x = 0}) e C
      (Ideal.absNorm 𝔭 ^ 2) he h0
      (fun n => by
        haveI := hfinp n
        haveI : Nonempty {x : M // ∀ a ∈ 𝔭 ^ n, a • x = 0} := ⟨⟨0, fun a _ => smul_zero a⟩⟩
        exact Nat.card_pos (α := {x : M // ∀ a ∈ 𝔭 ^ n, a • x = 0}))
      (fun k => GlobalTheory.T.torsion_count_log_concave_prime_powers F M 𝔭 h𝔭 k (hfinp (k + 2))) hblk
      (fun n => by rw [← pow_mul]; exact hC n)
    simpa using this
  obtain ⟨p, hpN, hgen⟩ := GlobalTheory.T.torsion_two_generators_global F M N hN hfin1
    (fun 𝔭 h𝔭 hN𝔭 => GlobalTheory.T.torsion_two_generators_mod_prime F M N hN hfin1 𝔭 h𝔭 hN𝔭 (hp 𝔭 h𝔭 hN𝔭))
  exact ⟨p, hpN, GlobalTheory.T.torsion_basis_relations_divisible F M N hN (by simpa using h2 1) p hpN hgen, hgen⟩

end GlobalTheory.RankTwoTorsion
