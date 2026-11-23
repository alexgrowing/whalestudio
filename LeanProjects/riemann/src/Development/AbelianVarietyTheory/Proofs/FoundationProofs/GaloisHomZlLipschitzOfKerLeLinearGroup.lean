import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicHomSmallOnDeepCongruenceSubgroupsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimePowMulDeepCongruenceLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LipschitzPadicHomOfContractionPerLevelStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem norm_natPrime_pow (l : ℕ) [Fact l.Prime] (m : ℕ) : ‖((l : ℕ) : Qbar l) ^ m‖ = ((l : ℝ)⁻¹) ^ m := by
  rw [norm_pow]
  congr 1
  have : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [this, norm_algebraMap', Padic.norm_p]

theorem hom_lipschitz_of_ker_le : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)) (lam : Γ →* Multiplicative ℤ_[l]), Continuous r → (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → Continuous lam → r.ker ≤ lam.ker → ∃ C : ℝ, ∀ (m : ℕ) (g : Γ), (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖) → ‖(lam g).toAdd‖ ≤ C * ‖((l : ℕ) : Qbar l) ^ m‖ := by
  intro l _ c Γ _ _ _ _ r lam hr hO hlam hker
  obtain ⟨C, hC⟩ := GlobalTheory.T.lipschitz_padicHom_of_contraction_per_level l Γ
    (fun m g => ∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖) lam
    (fun m g h i j => (h i j).trans (by
      rw [norm_natPrime_pow, norm_natPrime_pow, pow_succ]
      have h1 : (0 : ℝ) ≤ (l : ℝ)⁻¹ := by positivity
      have h2 : (l : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le)
      exact mul_le_of_le_one_right (pow_nonneg h1 _) h2))
    (GlobalTheory.T.padicHom_small_on_deep_congruence_subgroups l Γ r lam hr hlam hker) (GlobalTheory.T.exists_prime_pow_mul_deep_congruenceLevel l c Γ r hO)
  exact ⟨C, fun m g hg => by rw [norm_natPrime_pow]; exact hC m g hg⟩

end GlobalTheory.Ord2
