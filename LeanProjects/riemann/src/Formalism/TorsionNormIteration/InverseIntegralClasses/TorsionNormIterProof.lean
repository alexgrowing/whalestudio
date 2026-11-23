import Formalism.TorsionNormIteration.Statement

noncomputable section

universe u

namespace Formalism.LT.TorsProof

open Polynomial

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

lemma norm_sum_lt {s : Finset ℕ} {f : ℕ → K} {c : ℝ} (hc : 0 < c)
    (h : ∀ i ∈ s, ‖f i‖ < c) : ‖∑ i ∈ s, f i‖ < c := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp [hs, hc]
  · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs f
    exact hle.trans_lt (h i hi)

section LT

variable {π : K} {q : ℕ} {e : Polynomial K}

lemma eval_eq (e : Polynomial K) (x : K) :
    e.eval x = ∑ i ∈ Finset.range (e.natDegree + 1), e.coeff i * x ^ i :=
  Polynomial.eval_eq_sum_range x

lemma term_le (he : IsLTPoly q π e) {x : K} (hx : ‖x‖ ≤ 1) {i : ℕ} (hiq : i ≠ q) :
    ‖e.coeff i * x ^ i‖ ≤ ‖π‖ * ‖x‖ := by
  obtain ⟨h0, h1, -, hrest⟩ := he
  rcases Nat.lt_or_ge i 1 with hi | hi
  · have : i = 0 := by omega
    subst this; simp [h0, mul_nonneg (norm_nonneg π) (norm_nonneg x)]
  · rcases eq_or_ne i 1 with rfl | hi1
    · simp [h1]
    · rw [norm_mul, norm_pow]
      have hxi : ‖x‖ ^ i ≤ ‖x‖ := pow_le_of_le_one (norm_nonneg x) hx (by omega)
      exact mul_le_mul (hrest i hi1 hiq) hxi (by positivity) (norm_nonneg π)

lemma one_mem (hπ : 0 < ‖π‖) (he : IsLTPoly q π e) : 1 ∈ Finset.range (e.natDegree + 1) := by
  have : e.coeff 1 ≠ 0 := by
    rw [he.2.1]; intro h; rw [h, norm_zero] at hπ; exact lt_irrefl _ hπ
  exact Finset.mem_range.2 (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero this))

lemma norm_eval_le (hq : 2 ≤ q) (he : IsLTPoly q π e) {x : K} (hx : ‖x‖ < 1)
    (hsmall : ‖x‖ ^ (q - 1) ≤ ‖π‖) : ‖e.eval x‖ ≤ ‖π‖ * ‖x‖ := by
  rw [eval_eq]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (norm_nonneg π) (norm_nonneg x))
  intro i _
  rcases eq_or_ne i q with rfl | hiq
  · rw [norm_mul, he.2.2.1, one_mul, norm_pow]
    have : ‖x‖ ^ i = ‖x‖ ^ (i - 1) * ‖x‖ := by rw [← pow_succ]; congr 1; omega
    rw [this]; exact mul_le_mul_of_nonneg_right hsmall (norm_nonneg x)
  · exact term_le he hx.le hiq

end LT

end Formalism.LT.TorsProof

open Formalism.LT.TorsProof
