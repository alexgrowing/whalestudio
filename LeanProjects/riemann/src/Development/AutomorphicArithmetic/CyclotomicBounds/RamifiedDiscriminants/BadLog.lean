import Mathlib
import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
import Development.AutomorphicArithmetic.FrobeniusLocalisation.RadBounds2
import Development.AutomorphicArithmetic.FrobeniusLocalisation.RamEq
import Development.AutomorphicArithmetic.FrobeniusLocalisation.LogRdSum

open UpperTheory.HF
open NumberField Formalism.HC

theorem UpperTheory.KR.sum_log_bad_le :
    ∀ {φ : Frame} (H : HostAx φ) (M : ℕ) (S : Finset ℕ), M ≠ 0 →
      (∀ p ∈ S, p.Prime ∧ (p = 2 ∨ p = H.d ∨ p ∣ (discr H.E).natAbs ∨ p ∣ M)) →
        ∑ p ∈ S, Real.log p ≤ 2 * Real.log H.rd + Real.log M := by
  intro φ H M S hM hS
  have hD : (discr H.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero H.E)
  obtain ⟨hA, hB, -⟩ := UpperTheory.HF.ram_eq H
  have hsub : S ⊆ H.ram ∪ M.primeFactors := by
    intro p hp
    obtain ⟨hpp, h⟩ := hS p hp
    rw [Finset.mem_union]
    rcases h with h | h | h | h
    · exact Or.inl ((hA p).2 (Or.inl (h ▸ hB)))
    · exact Or.inl ((hA p).2 (Or.inr (Or.inr h)))
    · exact Or.inl (Nat.mem_primeFactors.2 ⟨hpp, h, hD⟩)
    · exact Or.inr (Nat.mem_primeFactors.2 ⟨hpp, h, hM⟩)
  have h1 : ∑ l ∈ H.ram, Real.log l ≤ 2 * Real.log H.rd := by
    simpa using (UpperTheory.HF.rad_bounds2 H).1 0 1 le_rfl zero_le_one
  have h2 : ∑ l ∈ M.primeFactors, Real.log l ≤ Real.log M := by
    have hne : ∀ l ∈ M.primeFactors, (l : ℝ) ≠ 0 := fun l hl =>
      Nat.cast_ne_zero.2 (Nat.prime_of_mem_primeFactors hl).ne_zero
    rw [← Real.log_prod hne, ← Nat.cast_prod]
    refine Real.log_le_log ?_ ?_
    · exact Nat.cast_pos.2 (Finset.prod_pos fun l hl => (Nat.prime_of_mem_primeFactors hl).pos)
    · exact Nat.cast_le.2 (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) (Nat.prod_primeFactors_dvd M))
  have h3 : ∑ p ∈ S, Real.log p ≤ ∑ p ∈ H.ram ∪ M.primeFactors, Real.log p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => Real.log_natCast_nonneg p
  have h4 := Finset.sum_union_inter (s₁ := H.ram) (s₂ := M.primeFactors) (f := fun p : ℕ => Real.log p)
  have h5 : 0 ≤ ∑ p ∈ H.ram ∩ M.primeFactors, Real.log p :=
    Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p
  linarith
