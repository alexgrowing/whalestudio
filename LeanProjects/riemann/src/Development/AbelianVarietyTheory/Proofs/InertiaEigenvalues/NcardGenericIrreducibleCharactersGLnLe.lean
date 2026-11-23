import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GelfandGraevCharacterGLnNormAndReciprocityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEqStatement

noncomputable section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.GenericCount

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem ip_comm {G : Type} [Group G] [Fintype G] (α β : G → ℂ) : ip α β = ip β α := by
  unfold ip
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun x => by simp [mul_comm])

theorem tr_finset_sum {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (S : Finset (G → ℂ))
    (c : (G → ℂ) → ℂ) : tr a (∑ ρ ∈ S, c ρ • ρ) = ∑ ρ ∈ S, c ρ * tr a ρ := by
  unfold tr
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun x _ => by ring

theorem gg_isClass {g : ℕ} [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (n : ℕ) : IsClass (gg ψ n) := by
  intro x z
  simp only [gg]
  congr 1
  symm
  refine Fintype.sum_equiv (Equiv.mulLeft z) _ _ (fun y => ?_)
  have h : (z * y)⁻¹ * (z * x * z⁻¹) * (z * y) = y⁻¹ * x * y := by group
  simp only [Equiv.coe_mulLeft, h]

end GlobalTheory.GLq.GenericCount

namespace GlobalTheory.GLq

open GlobalTheory.GLq.GenericCount in

theorem card_generic_irr_le : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ n : ℕ, 0 < n →
    Set.ncard {ρ : Gn g n → ℂ | IsIrr ρ ∧ wh ψ ρ ≠ 0} ≤ g ^ n - g ^ (n - 1) := by
  intro g _ ψ hψ n hn
  obtain ⟨hfin, -⟩ := GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one (Gn g n)
  set S := hfin.toFinset with hS
  have hmemS : ∀ ρ, ρ ∈ S ↔ IsIrr ρ := fun ρ => by rw [hS, Set.Finite.mem_toFinset]; rfl
  have hnorm := GlobalTheory.T.gelfandGraevCharacterGLn_norm_and_reciprocity g ψ hψ n hn
  have hdec := (GlobalTheory.T.character_decomposition_and_classFunction_expansion (Gn g n) (gg ψ n)).2.1 (gg_isClass ψ n)
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hdec
  have hirrC : ∀ ρ : Gn g n → ℂ, IsIrr ρ → IsClass ρ := fun ρ h =>
    (GlobalTheory.T.character_decomposition_and_classFunction_expansion (Gn g n) ρ).2.2.1 (isChar_of_isIrr h)
  have hnat : ∀ ρ : Gn g n → ℂ, IsIrr ρ → ∃ m : ℕ, wh ψ ρ = m := fun ρ h =>
    (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g n) (eU g n ψ) ρ).1 (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g n 0 0 ψ).1 (isChar_of_isIrr h)
  choose! m hm using hnat
  have hsum : ((∑ ρ ∈ S, m ρ ^ 2 : ℕ) : ℂ) = ((g ^ n - g ^ (n - 1) : ℕ) : ℂ) := by
    rw [Nat.cast_sub (Nat.pow_le_pow_right (Nat.Prime.pos Fact.out) (Nat.sub_le n 1))]
    push_cast
    rw [← hnorm.1]
    have hw : wh ψ (gg ψ n) = ∑ ρ ∈ S, ip (gg ψ n) ρ * wh ψ ρ := by
      conv_lhs => rw [hdec]
      unfold wh
      exact tr_finset_sum _ _ _
    rw [hw]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have hI := (hmemS ρ).1 hρ
    rw [ip_comm, hnorm.2 ρ (hirrC ρ hI), hm ρ hI]
    ring
  have hsumN : ∑ ρ ∈ S, m ρ ^ 2 = g ^ n - g ^ (n - 1) := by exact_mod_cast hsum
  have hset : {ρ : Gn g n → ℂ | IsIrr ρ ∧ wh ψ ρ ≠ 0} = ↑(S.filter fun ρ => m ρ ≠ 0) := by
    ext ρ
    simp only [Set.mem_setOf_eq, Finset.coe_filter, hmemS]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h0 => h2 (by rw [hm ρ h1, h0, Nat.cast_zero])⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h0 => h2 (by rw [hm ρ h1] at h0; exact_mod_cast h0)⟩
  rw [hset, Set.ncard_coe_finset, ← hsumN, Finset.card_eq_sum_ones]
  calc ∑ ρ ∈ S.filter (fun ρ => m ρ ≠ 0), 1 ≤ ∑ ρ ∈ S.filter (fun ρ => m ρ ≠ 0), m ρ ^ 2 :=
        Finset.sum_le_sum fun ρ hρ => Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (Finset.mem_filter.1 hρ).2)
    _ ≤ ∑ ρ ∈ S, m ρ ^ 2 := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end GlobalTheory.GLq
