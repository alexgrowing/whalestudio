import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NpOfOddPrimeDegreeStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NpOfFinrankTwoStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormPrincipleOfCyclicTowerStatement

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem np_of_finrank_one (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (h : Module.finrank F E = 1) : NP F E := by
  intro x _ _
  refine ⟨algebraMap F E x, ?_⟩
  rw [Algebra.norm_algebraMap, h, pow_one]

theorem np_of_finrank_prime (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsGalois F E] (hp : p.Prime) (h : Module.finrank F E = p) :
    NP F E := by
  by_cases h2 : p = 2
  · exact GlobalTheory.T.np_of_finrank_two' F E (h2 ▸ h)
  · exact GlobalTheory.T.np_of_odd_prime_degree' p F E hp h2 h

theorem hasseNormPrinciple_cyclic_of_finrank (n : ℕ) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E], Module.finrank F E = n → IsGalois F E → IsCyclic (E ≃ₐ[F] E) → NP F E := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F E _ _ _ _ _ hn hG hC
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  by_cases h1 : n = 1
  · exact np_of_finrank_one F E (hn.trans h1)
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = n := (IsGalois.card_aut_eq_finrank F E).trans hn
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := E ≃ₐ[F] E) p (hcard ▸ hpn)
  set H : Subgroup (E ≃ₐ[F] E) := Subgroup.zpowers g with hH
  have hHc : Nat.card H = p := by rw [hH, Nat.card_zpowers, hg]
  have : H.Normal := by
    constructor
    intro a ha b
    have hc : b * a = a * b := by
      obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
      obtain ⟨i, rfl⟩ := hs a
      obtain ⟨j, rfl⟩ := hs b
      exact (Commute.zpow_zpow_self s j i).eq
    rw [hc, mul_inv_cancel_right]
    exact ha
  let M : IntermediateField F E := IntermediateField.fixedField H
  have : NumberField M := NumberField.of_module_finite F M
  have hME : Module.finrank M E = p :=
    (IntermediateField.finrank_fixedField_eq_card H).trans hHc
  have : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  have hFM : IsGalois F M := IsGalois.of_fixedField_normal_subgroup H
  have hCM : IsCyclic (M ≃ₐ[F] M) :=
    isCyclic_of_surjective (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) M)
      (AlgEquiv.restrictNormalHom_surjective E)
  have hmul : Module.finrank F M * Module.finrank M E = n :=
    (Module.finrank_mul_finrank F M E).trans hn
  have hpos : 0 < Module.finrank F M := Module.finrank_pos
  have hlt : Module.finrank F M < n := by
    rw [← hmul, hME]
    exact lt_mul_of_one_lt_right hpos hp.one_lt
  exact GlobalTheory.T.hasseNormPrinciple_of_cyclic_tower F M E hC (np_of_finrank_prime p M E hp hME) (ih _ hlt F M rfl hFM hCM)

theorem np_cyclic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E], IsGalois F E → IsCyclic (E ≃ₐ[F] E) → NP F E :=
  fun F E _ _ _ _ _ hG hC => hasseNormPrinciple_cyclic_of_finrank _ F E rfl hG hC

end GlobalTheory.CNorm
