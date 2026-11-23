import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem sizeE_zpow_le_prod_inv_sq (r n B N : ℕ) (cs : List (Fin r)) (m : Fin r → ℕ)
    (hN : n * B + 2 ≤ N) (hc : ∀ i, cs.count i = N ∨ m i = 0) :
    sizeE (fun i => (m i : ℝ)) ^ ((n : ℤ) * (B : ℤ) - (cs.length : ℤ)) ≤
      ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := by
  have hcount : ∀ l : List (Fin r), ∑ i, l.count i = l.length := by
    intro l
    first
      | simpa using Multiset.sum_count_eq_card (l : Multiset (Fin r))
      | (induction l with
          | nil => simp
          | cons a t ih => simp [List.count_cons, Finset.sum_add_distrib, ih])
  set S := sizeE (fun i => (m i : ℝ)) with hSdef
  have hSval : S = 1 + ∑ i, (m i : ℝ) := rfl
  have hsum0 : 0 ≤ ∑ i, (m i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have hS1 : 1 ≤ S := by rw [hSval]; linarith
  have hmS : ∀ i, 1 + (m i : ℝ) ≤ S := by
    intro i
    rw [hSval]
    have := Finset.single_le_sum (f := fun j => (m j : ℝ)) (fun j _ => Nat.cast_nonneg (m j)) (Finset.mem_univ i)
    linarith
  set K := Finset.univ.filter (fun i => m i ≠ 0) with hKdef
  set k := K.card with hkdef
  have hg : ∏ i, (if m i ≠ 0 then (S ^ 2)⁻¹ else (1 : ℝ)) = ((S ^ 2)⁻¹) ^ k := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  have hle : ∏ i, (if m i ≠ 0 then (S ^ 2)⁻¹ else (1 : ℝ)) ≤ ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := by
    apply Finset.prod_le_prod
    · intro i _
      split_ifs
      · positivity
      · norm_num
    · intro i _
      split_ifs with hi
      · exact inv_anti₀ (by positivity) (by gcongr; exact hmS i)
      · rw [ne_eq, not_not] at hi
        simp [hi]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · have hm : ∀ i, m i = 0 := by
      intro i
      by_contra hi
      have hiK : i ∈ K := by simp [hKdef, hi]
      rw [Finset.card_eq_zero.mp hk] at hiK
      simp at hiK
    have hS : S = 1 := by rw [hSval]; simp [hm]
    calc S ^ ((n : ℤ) * (B : ℤ) - (cs.length : ℤ)) = ((S ^ 2)⁻¹) ^ k := by rw [hS, hk]; simp
      _ ≤ ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := by rw [← hg]; exact hle
  · have hKsum : ∑ i ∈ K, cs.count i = k * N := by
      have hKN : ∀ i ∈ K, cs.count i = N := fun i hi => (hc i).resolve_right (Finset.mem_filter.mp hi).2
      rw [Finset.sum_congr rfl hKN, Finset.sum_const, smul_eq_mul]
    have hLk : k * N ≤ cs.length := by
      rw [← hKsum, ← hcount cs]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ K)
    have h2 : n * B ≤ n * B * k := Nat.le_mul_of_pos_right _ hk
    have hA : n * B + 2 * k ≤ cs.length :=
      calc n * B + 2 * k ≤ n * B * k + 2 * k := Nat.add_le_add_right h2 _
        _ = (n * B + 2) * k := by ring
        _ ≤ N * k := Nat.mul_le_mul_right k hN
        _ = k * N := Nat.mul_comm _ _
        _ ≤ cs.length := hLk
    have hexp : (n : ℤ) * (B : ℤ) - (cs.length : ℤ) ≤ -(2 * (k : ℤ)) := by
      have hcast : ((n * B + 2 * k : ℕ) : ℤ) ≤ (cs.length : ℤ) := by exact_mod_cast hA
      push_cast at hcast
      linarith
    have hz : S ^ (-(2 * (k : ℤ))) = ((S ^ 2)⁻¹) ^ k := by
      rw [zpow_neg, show (2 * (k : ℤ)) = ((2 * k : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul, inv_pow]
    calc S ^ ((n : ℤ) * (B : ℤ) - (cs.length : ℤ)) ≤ S ^ (-(2 * (k : ℤ))) := zpow_le_zpow_right₀ hS1 hexp
      _ = ((S ^ 2)⁻¹) ^ k := hz
      _ = ∏ i, (if m i ≠ 0 then (S ^ 2)⁻¹ else (1 : ℝ)) := hg.symm
      _ ≤ ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := hle

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
