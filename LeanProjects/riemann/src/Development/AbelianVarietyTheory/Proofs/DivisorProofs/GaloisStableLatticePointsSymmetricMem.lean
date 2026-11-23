import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntermediateFieldOfForallComplexAutFixedStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem stable_sym_mem (F : IntermediateField ℚ ℂ) (L : PeriodPair) (ι : Type) [Fintype ι] (T : ι → ℂ) :
    L.g₂ ∈ F → L.g₃ ∈ F → Stable L F T → (∀ i, T i ∉ L.lattice) →
    (∑ i, L.weierstrassP (T i)) ∈ F ∧ (∑ i, L.derivWeierstrassP (T i) / 2) ∈ F ∧
    (∑ i, (3 * L.weierstrassP (T i) ^ 2 + -L.g₂ / 4) / (2 * (L.derivWeierstrassP (T i) / 2))) ∈ F ∧
    ((∀ i, 2 * T i ∉ L.lattice) → (∏ i, (L.weierstrassP (T i) - L.weierstrassP (2 * T i))) ∈ F) := by
  intro h₂ h₃ hS hT
  have key : ∀ σ : ℂ ≃+* ℂ, (∀ x ∈ F, σ x = x) → ∃ e : ι ≃ ι,
      (∀ i, σ (L.weierstrassP (T i)) = L.weierstrassP (T (e i))) ∧
      (∀ i, σ (L.derivWeierstrassP (T i)) = L.derivWeierstrassP (T (e i))) ∧
      ((∀ i, 2 * T i ∉ L.lattice) → ∀ i, σ (L.weierstrassP (2 * T i)) = L.weierstrassP (2 * T (e i))) ∧
      σ L.g₂ = L.g₂ := by
    intro σ hσ
    obtain ⟨e, he⟩ := hS σ hσ
    have g₂e : L.g₂ = σ L.g₂ := (hσ _ h₂).symm
    have g₃e : L.g₃ = σ L.g₃ := (hσ _ h₃).symm
    refine ⟨e, fun i ↦ ?_, fun i ↦ ?_, fun h2 i ↦ ?_, hσ _ h₂⟩
    · exact (((he i).resolve_left fun h ↦ hT i h.1).2.2.1).symm
    · exact (((he i).resolve_left fun h ↦ hT i h.1).2.2.2).symm
    · have := GlobalTheory.ConjPoint.IsConj.add g₂e g₃e (he i) (he i)
      rw [← two_mul, ← two_mul] at this
      exact ((this.resolve_left fun h ↦ h2 i h.1).2.2.1).symm
  refine ⟨GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed F _ fun σ hσ ↦ ?_, GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed F _ fun σ hσ ↦ ?_,
    GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed F _ fun σ hσ ↦ ?_, fun h2 ↦ GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed F _ fun σ hσ ↦ ?_⟩
  · obtain ⟨e, a, -, -, -⟩ := key σ hσ
    rw [map_sum]; simp only [a]; exact Equiv.sum_comp e (fun i ↦ L.weierstrassP (T i))
  · obtain ⟨e, -, b, -, -⟩ := key σ hσ
    rw [map_sum]; simp only [map_div₀, map_ofNat, b]
    exact Equiv.sum_comp e (fun i ↦ L.derivWeierstrassP (T i) / 2)
  · obtain ⟨e, a, b, -, g⟩ := key σ hσ
    rw [map_sum]
    simp only [map_div₀, map_add, map_mul, map_pow, map_neg, map_ofNat, a, b, g]
    exact Equiv.sum_comp e (fun i ↦ (3 * L.weierstrassP (T i) ^ 2 + -L.g₂ / 4) / (2 * (L.derivWeierstrassP (T i) / 2)))
  · obtain ⟨e, a, -, c, -⟩ := key σ hσ
    rw [map_prod]; simp only [map_sub, a, c h2]
    exact Equiv.prod_comp e (fun i ↦ L.weierstrassP (T i) - L.weierstrassP (2 * T i))

end GlobalTheory.CMModel
