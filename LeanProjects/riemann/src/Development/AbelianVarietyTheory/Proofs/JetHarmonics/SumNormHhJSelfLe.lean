import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

section
variable {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}

lemma hhJ_self_norm_le_sum_sq (ε : Fin n → Bool) (x : Fin n → M) :
    ‖hhJ ε x x‖ ≤ ∑ c, ‖x c‖ ^ 2 := by
  unfold hhJ
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [norm_mul, inner_self_eq_norm_sq_to_K]
  split_ifs <;> simp

lemma hhJ_self_im_eq_zero (ε : Fin n → Bool) (x : Fin n → M) :
    (hhJ ε x x).im = 0 := by
  unfold hhJ
  rw [Complex.im_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  have h : (⟪x c, x c⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) (x c)
  split_ifs <;> simp [-inner_self_eq_norm_sq_to_K, h]

lemma hhJ_finsum_finsum {ι : Type} (ε : Fin n → Bool) (y : ι → Fin n → M) (In : Finset ι) :
    hhJ ε (∑ s ∈ In, y s) (∑ s ∈ In, y s) = ∑ s ∈ In, ∑ t ∈ In, hhJ ε (y s) (y t) := by
  unfold hhJ
  simp only [Finset.sum_apply, sum_inner, inner_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]

end

theorem sum_norm_hhJ_self_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (y : Fin n → Fin n → M) (In : Finset (Fin n)) (Cc Cs Nn : ℝ), (∀ s t, s ≠ t → hhJ ε (y s) (y t) = 0) → (∀ s ∈ In, 0 ≤ (hhJ ε (y s) (y s)).re) → ∑ c, ‖(∑ s ∈ In, y s) c‖ ^ 2 ≤ Cc ^ 2 * Nn → (∀ s, s ∉ In → ∑ c, ‖y s c‖ ^ 2 ≤ Cs ^ 2 * Nn) → ∑ s, ‖hhJ ε (y s) (y s)‖ ≤ (Cc ^ 2 + (Inᶜ.card : ℝ) * Cs ^ 2) * Nn := by
  intro M _ _ n ε y In Cc Cs Nn horth hpos hIn hout
  rw [← Finset.sum_add_sum_compl In]
  have h1 : hhJ ε (∑ s ∈ In, y s) (∑ s ∈ In, y s) = ∑ s ∈ In, hhJ ε (y s) (y s) := by
    rw [hhJ_finsum_finsum]
    refine Finset.sum_congr rfl fun s hs => ?_
    exact Finset.sum_eq_single_of_mem s hs fun t _ hts => horth s t (Ne.symm hts)
  have h2 : ∑ s ∈ In, ‖hhJ ε (y s) (y s)‖ = (∑ s ∈ In, hhJ ε (y s) (y s)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [← Complex.abs_re_eq_norm.mpr (hhJ_self_im_eq_zero ε (y s)), abs_of_nonneg (hpos s hs)]
  have h3 : ∑ s ∈ In, ‖hhJ ε (y s) (y s)‖ ≤ Cc ^ 2 * Nn := by
    rw [h2, ← h1]
    exact (Complex.re_le_norm _).trans ((hhJ_self_norm_le_sum_sq ε _).trans hIn)
  have h4 : ∑ s ∈ Inᶜ, ‖hhJ ε (y s) (y s)‖ ≤ (Inᶜ.card : ℝ) * (Cs ^ 2 * Nn) := by
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun s hs => ?_
    exact (hhJ_self_norm_le_sum_sq ε _).trans (hout s (Finset.mem_compl.mp hs))
  calc _ ≤ Cc ^ 2 * Nn + (Inᶜ.card : ℝ) * (Cs ^ 2 * Nn) := add_le_add h3 h4
    _ = _ := by ring

end GlobalTheory
