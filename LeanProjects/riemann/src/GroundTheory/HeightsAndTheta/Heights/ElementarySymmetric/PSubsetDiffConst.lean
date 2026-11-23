import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StSubsetDiffConst
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Finset

noncomputable section

theorem sum_subsets_neg_one_pow_prod_indicator (n : ℕ) (a : Fin n → ℕ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) * ∏ i, (if i ∈ T then (1 : ℚ) else 0) ^ a i =
      ∏ i, (1 - (0 : ℚ) ^ a i) := by
  have h := Finset.prod_add (fun _ : Fin n => (1 : ℚ)) (fun i => -((0 : ℚ) ^ a i)) univ
  simp only [← sub_eq_add_neg, powerset_univ, prod_const_one, one_mul] at h
  rw [h]
  refine sum_congr rfl fun T _ => ?_
  rw [prod_neg, ← compl_eq_univ_sdiff, card_compl, Fintype.card_fin]
  congr 1
  rw [← prod_mul_prod_compl T]
  rw [prod_congr rfl (fun i hi => by rw [if_pos hi, one_pow]), prod_const_one, one_mul]
  exact prod_congr rfl fun i hi => by rw [if_neg (mem_compl.mp hi)]

theorem prod_snoc_snoc_pow (n : ℕ) (T : Finset (Fin n)) (m : ℕ) (c : ℤ) (e : Fin (n + 1 + 1) → ℕ) :
    ∏ j, (Fin.snoc (α := fun _ => ℚ)
        (fun j => ((Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m j : ℕ) : ℚ))
        (c : ℚ) j) ^ e j =
      (∏ i : Fin n, (if i ∈ T then (1 : ℚ) else 0) ^ e i.castSucc.castSucc) *
        (m : ℚ) ^ e (Fin.last n).castSucc * (c : ℚ) ^ e (Fin.last (n + 1)) := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  congr 2
  refine prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem subsetDiff_eq_sum_support (n : ℕ) (f : (Fin (n + 1) → ℕ) → ℤ → ℚ)
    (Q : MvPolynomial (Fin (n + 1 + 1)) ℚ)
    (hf : ∀ (x : Fin (n + 1) → ℕ) (c : ℤ),
      f x c = eval (Fin.snoc (α := fun _ => ℚ) (fun j => (x j : ℚ)) (c : ℚ)) Q)
    (m : ℕ) (c : ℤ) :
    subsetDiff n f m c = ∑ e ∈ Q.support, Q.coeff e *
      ((∏ i : Fin n, (1 - (0 : ℚ) ^ e i.castSucc.castSucc)) * (m : ℚ) ^ e (Fin.last n).castSucc *
        (c : ℚ) ^ e (Fin.last (n + 1))) := by
  unfold subsetDiff
  simp only [hf, eval_eq', prod_snoc_snoc_pow, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  have h := sum_subsets_neg_one_pow_prod_indicator n (fun i => e i.castSucc.castSucc)
  rw [← h, sum_mul, sum_mul, mul_sum]
  exact sum_congr rfl fun T _ => by ring

theorem sum_exponents_lt_of_mem_support {σ : Type*} [Fintype σ] {Q : MvPolynomial σ ℚ} {D : ℕ}
    (h : Q = 0 ∨ Q.totalDegree < D) {e : σ →₀ ℕ} (he : e ∈ Q.support) : ∑ j, e j < D := by
  rcases h with h | h
  · simp [h] at he
  · have := le_totalDegree he
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    exact lt_of_le_of_lt this h

theorem le_sum_of_prod_ne_zero (n : ℕ) (a : Fin n → ℕ) (h : (∏ i, (1 - (0 : ℚ) ^ a i)) ≠ 0) :
    n ≤ ∑ i, a i := by
  have hpos : ∀ i, 1 ≤ a i := fun i => by
    by_contra h0
    have h1 : a i = 0 := by omega
    exact h (prod_eq_zero (mem_univ i) (by rw [h1, pow_zero, sub_self]))
  calc n = ∑ _i : Fin n, 1 := by simp
    _ ≤ ∑ i, a i := sum_le_sum fun i _ => hpos i

theorem SubsetDiffConst.proof : SubsetDiffConst.Statement := by
  intro n f ⟨Q, hQ, hf⟩
  have split : ∀ e : Fin (n + 1 + 1) →₀ ℕ, ∑ j, e j =
      ∑ i : Fin n, e i.castSucc.castSucc + e (Fin.last n).castSucc + e (Fin.last (n + 1)) := fun e => by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  refine ⟨fun m m' c c' => ?_, fun ⟨Q', hQ', hf'⟩ m c => ?_⟩
  · rw [subsetDiff_eq_sum_support n f Q hf, subsetDiff_eq_sum_support n f Q hf]
    refine sum_congr rfl fun e he => ?_
    by_cases hp : (∏ i : Fin n, (1 - (0 : ℚ) ^ e i.castSucc.castSucc)) = 0
    · simp [hp]
    · have h1 := le_sum_of_prod_ne_zero n (fun i => e i.castSucc.castSucc) hp
      have h2 := sum_exponents_lt_of_mem_support hQ he
      rw [split] at h2
      have ha : e (Fin.last n).castSucc = 0 := by omega
      have hb : e (Fin.last (n + 1)) = 0 := by omega
      simp [ha, hb]
  · rw [subsetDiff_eq_sum_support n f Q' hf']
    refine sum_eq_zero fun e he => ?_
    by_cases hp : (∏ i : Fin n, (1 - (0 : ℚ) ^ e i.castSucc.castSucc)) = 0
    · simp [hp]
    · have h1 := le_sum_of_prod_ne_zero n (fun i => e i.castSucc.castSucc) hp
      have h2 := sum_exponents_lt_of_mem_support hQ' he
      rw [split] at h2
      omega

end

end GroundTheory.Heights₂.Heights.Kleiman
