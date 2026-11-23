import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqrtNegPrimeKernelCyclicStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

open GlobalTheory.ConjPoint PeriodPair in

theorem exists_conj_kernel_mul : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ σ : ℂ ≃+* ℂ, (∀ x ∈ F, σ x = x) → ∃ c : ℕ, ¬ p ∣ c ∧ ∀ k : ℕ, GlobalTheory.ConjPoint.IsConj L L σ ((k : ℂ) * t) ((k : ℂ) * ((c : ℂ) * t)) := by
  intro p F L t hp h4 h3 hD σ hσ
  have h₂ : L.g₂ = σ L.g₂ := (hσ _ hD.g₂_mem).symm
  have h₃ : L.g₃ = σ L.g₃ := (hσ _ hD.g₃_mem).symm
  obtain ⟨s, -, hc⟩ := exists_conjEquiv h₂ h₃
  obtain ⟨t', ht'⟩ := latticePoint_surjective L (s (latticePoint L t))
  have hct : IsConj L L σ t t' := (hc _ _).2 ht'.symm
  have ht'n : t' ∉ L.lattice := by
    rcases hct with h | h
    · exact (hD.notMem h.1).elim
    · exact h.2.1

  have hsq : (σ (sqrtNegNat p)) ^ 2 = (sqrtNegNat p) ^ 2 := by
    rw [← map_pow, sqrtNegNat_sq, map_neg, map_natCast]
  have hm := IsConj.mul h₂ h₃ hD.mul hct
  have hker : σ (sqrtNegNat p) * t' ∈ L.lattice := by
    rcases hm with h | h
    · exact h.2
    · exact (h.1 hD.ker).elim
  have hker' : sqrtNegNat p * t' ∈ L.lattice := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with e | e
    · rwa [e] at hker
    · rw [e, neg_mul] at hker
      simpa using neg_mem hker
  obtain ⟨-, hz, -⟩ := GlobalTheory.T.sqrtNegPrime_kernel_cyclic p F L t hp h4 h3 hD
  obtain ⟨c, hcp, hcl⟩ := hz t' hker'
  refine ⟨c, fun hdvd => ?_, fun k => ?_⟩
  · have hc0 : c = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hcp
    subst hc0
    exact ht'n (by simpa using hcl)
  · have hk := IsConj.mul h₂ h₃ (α := (k : ℂ))
      (fun l hl => by rw [← nsmul_eq_mul]; exact nsmul_mem hl k) hct
    rw [map_natCast] at hk
    have h0 : IsConj L L σ 0 ((k : ℂ) * ((c : ℂ) * t) - (k : ℂ) * t') := by
      left
      refine ⟨zero_mem _, ?_⟩
      have : (k : ℂ) * ((c : ℂ) * t) - (k : ℂ) * t' = -((k : ℂ) * (t' - (c : ℂ) * t)) := by ring
      rw [this, ← nsmul_eq_mul]
      exact neg_mem (nsmul_mem hcl k)
    have := IsConj.add h₂ h₃ hk h0
    simpa using this

end GlobalTheory.CMModel
