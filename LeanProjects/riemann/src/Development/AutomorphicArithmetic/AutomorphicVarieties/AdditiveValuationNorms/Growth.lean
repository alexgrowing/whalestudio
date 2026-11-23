import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.UnipPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.PowIn
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ImportsMore
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ImportsBis

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.growth :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (R : ℕ) (g : Module.End ℤ_[l] X), GenBy l R X → Unip g → ∀ m : ℕ,
      cokLen (g ^ l ^ m - 1) ≤ cokLen (g ^ l ^ jZero l R - 1) + ((R * (m - jZero l R) : ℕ) : ℕ∞) := by
  intro l _ X _ _ R g hG hU m
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  obtain ⟨k, hk⟩ : ∃ k, k = Nat.log l R + 1 := ⟨_, rfl⟩
  have hRk : R ≤ l ^ k := by
    rw [hk]
    exact (Nat.lt_pow_succ_log_self hl R).le
  have hA : InPow 1 ((g - 1) ^ l ^ k) := by
    have h0 := unipPow l X R g hG hU
    have hsplit : (g - 1) ^ l ^ k = (g - 1) ^ (l ^ k - R) * (g - 1) ^ R := by
      rw [← pow_add, Nat.sub_add_cancel hRk]
    intro x
    obtain ⟨y, hy⟩ := h0 x
    refine ⟨((g - 1) ^ (l ^ k - R)) y, ?_⟩
    rw [hsplit, Module.End.mul_apply, hy, map_smul]
  have hB : InPow 2 (g ^ l ^ (k + 1) - 1) := by
    have h := (powIn l X (g ^ l ^ k)).2 ((frob l X g k).1 hA)
    rwa [← pow_mul, ← pow_succ] at h
  have hC : ∀ n, k + 1 ≤ n → InPow 2 (g ^ l ^ n - 1) := by
    intro n hn
    have h := (powIn l X (g ^ l ^ (k + 1))).1 2 (l ^ (n - (k + 1))) hB
    rwa [← pow_mul, ← pow_add, Nat.add_sub_cancel' hn] at h
  have hstep : ∀ n, k + 1 ≤ n → cokLen (g ^ l ^ (n + 1) - 1) ≤ cokLen (g ^ l ^ n - 1) + R := by
    intro n hn
    have h := step l X R (g ^ l ^ n) hG (hC n hn)
    rwa [← pow_mul, ← pow_succ] at h
  have main : ∀ d, cokLen (g ^ l ^ (jZero l R + d) - 1) ≤
      cokLen (g ^ l ^ jZero l R - 1) + ((R * d : ℕ) : ℕ∞) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      calc cokLen (g ^ l ^ (jZero l R + (d + 1)) - 1) = cokLen (g ^ l ^ (jZero l R + d + 1) - 1) := rfl
        _ ≤ cokLen (g ^ l ^ (jZero l R + d) - 1) + R := hstep _ (by simp only [jZero]; omega)
        _ ≤ cokLen (g ^ l ^ jZero l R - 1) + ((R * d : ℕ) : ℕ∞) + R := add_le_add_left ih _
        _ = cokLen (g ^ l ^ jZero l R - 1) + ((R * (d + 1) : ℕ) : ℕ∞) := by
            push_cast
            ring
  rcases le_total m (jZero l R) with hm | hm
  · rw [Nat.sub_eq_zero_of_le hm, mul_zero, Nat.cast_zero, add_zero]
    exact mono l X g _ _ (pow_dvd_pow l hm)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [Nat.add_sub_cancel_left]
    exact main d
