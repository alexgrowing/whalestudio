import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationNatCastEqOneOfCoprimeStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_sq_add_prime_odd_mod_three_unit :
    ∀ (p : ℕ) (V : ValuationSubring ℂ), p.Prime → 3 < p →
      ∃ a N : ℕ, N = a ^ 2 + p ∧ Odd N ∧ N % 3 = 2 ∧ V.valuation (N : ℂ) = 1 := by
  intro p V hp h3
  have h2 : p % 2 = 1 := by
    by_contra h
    rcases hp.eq_one_or_self_of_dvd 2 (by omega) with h' | h' <;> omega
  have h3' : p % 3 ≠ 0 := by
    intro h
    rcases hp.eq_one_or_self_of_dvd 3 (by omega) with h' | h' <;> omega
  rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with h1 | h1
  · have hcop : Nat.Coprime (2 ^ 2 + p) (4 ^ 2 + p) := by
      have hg1 := Nat.gcd_dvd_left (2 ^ 2 + p) (4 ^ 2 + p)
      have hg2 := Nat.gcd_dvd_right (2 ^ 2 + p) (4 ^ 2 + p)
      have h12 : Nat.gcd (2 ^ 2 + p) (4 ^ 2 + p) ∣ 12 := by
        have := Nat.dvd_sub hg2 hg1
        have e : 4 ^ 2 + p - (2 ^ 2 + p) = 12 := by omega
        rwa [e] at this
      have hle := Nat.le_of_dvd (by norm_num) h12
      unfold Nat.Coprime
      generalize Nat.gcd (2 ^ 2 + p) (4 ^ 2 + p) = g at hg1 hg2 h12 hle
      norm_num at hg1 hg2
      interval_cases g <;> omega
    rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V _ _ hcop with hv | hv
    · exact ⟨2, 2 ^ 2 + p, rfl, by rw [Nat.odd_iff]; omega, by omega, by exact_mod_cast hv⟩
    · exact ⟨4, 4 ^ 2 + p, rfl, by rw [Nat.odd_iff]; omega, by omega, by exact_mod_cast hv⟩
  · have hcop : Nat.Coprime (0 ^ 2 + p) (6 ^ 2 + p) := by
      have hg1 := Nat.gcd_dvd_left (0 ^ 2 + p) (6 ^ 2 + p)
      have hg2 := Nat.gcd_dvd_right (0 ^ 2 + p) (6 ^ 2 + p)
      have h36 : Nat.gcd (0 ^ 2 + p) (6 ^ 2 + p) ∣ 36 := by
        have := Nat.dvd_sub hg2 hg1
        have e : 6 ^ 2 + p - (0 ^ 2 + p) = 36 := by omega
        rwa [e] at this
      have hle := Nat.le_of_dvd (by norm_num) h36
      unfold Nat.Coprime
      generalize Nat.gcd (0 ^ 2 + p) (6 ^ 2 + p) = g at hg1 hg2 h36 hle
      norm_num at hg1 hg2
      interval_cases g <;> omega
    rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V _ _ hcop with hv | hv
    · exact ⟨0, 0 ^ 2 + p, rfl, by rw [Nat.odd_iff]; omega, by omega, by exact_mod_cast hv⟩
    · exact ⟨6, 6 ^ 2 + p, rfl, by rw [Nat.odd_iff]; omega, by omega, by exact_mod_cast hv⟩

end GlobalTheory.CMModel
