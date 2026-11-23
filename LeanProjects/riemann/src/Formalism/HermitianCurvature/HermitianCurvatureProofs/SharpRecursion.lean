import Formalism.HermitianCurvature.Statement
import Mathlib

namespace Formalism.FourierDecayAlt.P.Rec

open Finset Real

lemma geom_le (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1/2) :
    ∀ i : ℕ, ∑ t ∈ Icc 2 i, a ^ (t-1) ≤ 2 * a := by
  have aux : ∀ k : ℕ, ∑ t ∈ Icc 2 (k+1), a ^ (t-1) + 2 * a ^ (k+1) ≤ 2 * a := by
    intro k
    induction k with
    | zero =>
      rw [Finset.Icc_eq_empty (by norm_num)]
      simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have e : k + 1 + 1 - 1 = k + 1 := by omega
      rw [e]
      have hp := pow_nonneg h0 (k+1)
      have hs : a ^ (k + 1 + 1) = a ^ (k+1) * a := pow_succ a (k+1)
      rw [hs]
      nlinarith [mul_le_mul_of_nonneg_left h1 hp]
  intro i
  rcases i with _ | k
  · rw [Finset.Icc_eq_empty (by norm_num)]; simp; linarith
  · have := aux k
    have hp := pow_nonneg h0 (k+1)
    linarith

noncomputable def Pp (e : ℕ → ℝ) (i : ℕ) : ℝ := ∏ l ∈ Icc 1 i, √(1 + e l)

lemma Pp_zero (e : ℕ → ℝ) : Pp e 0 = 1 := by
  simp [Pp]

lemma Pp_succ (e : ℕ → ℝ) (i : ℕ) : Pp e (i+1) = Pp e i * √(1 + e (i+1)) := by
  unfold Pp
  rw [Finset.prod_Icc_succ_top (by omega)]

lemma one_le_sqrt_e {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) (l : ℕ) : (1:ℝ) ≤ √(1 + e l) := by
  have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1 + e l by linarith [he l])
  rwa [Real.sqrt_one] at this

lemma one_le_Pp {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) : ∀ i, 1 ≤ Pp e i := by
  intro i
  induction i with
  | zero => rw [Pp_zero]
  | succ k ih =>
    rw [Pp_succ]
    have := one_le_sqrt_e he (k+1)
    nlinarith

lemma Pp_nonneg {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) (i : ℕ) : 0 ≤ Pp e i :=
  le_trans zero_le_one (one_le_Pp he i)

lemma Pp_mono {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) : Monotone (Pp e) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [Pp_succ]
  exact le_mul_of_one_le_right (Pp_nonneg he n) (one_le_sqrt_e he (n+1))

lemma Pp_sq {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) (i : ℕ) :
    Pp e i ^ 2 = ∏ l ∈ Icc 1 i, (1 + e l) := by
  unfold Pp
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro l _
  rw [Real.sq_sqrt (by linarith [he l])]

lemma growth (r : ℕ) (a ε : ℝ) (e σ : ℕ → ℝ) (ρ : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 1/2)
    (hε : 0 ≤ ε) (he : ∀ i, 0 ≤ e i) (hσ : ∀ i, 0 ≤ σ i)
    (hrec : ∀ i, 1 ≤ i → i ≤ r + 1 →
      σ i ≤ (1 + ε) * √(1 + e i) * σ (i - 1) + ∑ t ∈ Icc 2 i, a ^ (t - 1) * σ (i - t))
    (hρ1 : 1 + ε + 2 * a ≤ ρ) :
    ∀ i, i ≤ r + 1 → σ i ≤ Pp e i * ρ ^ i * σ 0 := by
  have hρ : (1:ℝ) ≤ ρ := by linarith
  have hσ0 := hσ 0
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases i with _ | k
    · simp [Pp_zero]
    · have h1 := hrec (k+1) (by omega) hi
      simp only [Nat.add_sub_cancel] at h1
      have hB : 0 ≤ Pp e (k+1) * ρ ^ k * σ 0 :=
        mul_nonneg (mul_nonneg (Pp_nonneg he _) (pow_nonneg (by linarith) _)) hσ0
      have hsum : ∑ t ∈ Icc 2 (k+1), a ^ (t-1) * σ (k+1-t) ≤
          2 * a * (Pp e (k+1) * ρ ^ k * σ 0) := by
        calc ∑ t ∈ Icc 2 (k+1), a ^ (t-1) * σ (k+1-t)
            ≤ ∑ t ∈ Icc 2 (k+1), a ^ (t-1) * (Pp e (k+1) * ρ ^ k * σ 0) := by
              apply Finset.sum_le_sum
              intro t ht
              have ht' := Finset.mem_Icc.mp ht
              apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha _)
              calc σ (k+1-t) ≤ Pp e (k+1-t) * ρ ^ (k+1-t) * σ 0 := ih _ (by omega) (by omega)
                _ ≤ Pp e (k+1) * ρ ^ k * σ 0 := by
                  apply mul_le_mul_of_nonneg_right _ hσ0
                  exact mul_le_mul (Pp_mono he (by omega)) (pow_le_pow_right₀ hρ (by omega))
                    (pow_nonneg (by linarith) _) (Pp_nonneg he _)
          _ = (∑ t ∈ Icc 2 (k+1), a ^ (t-1)) * (Pp e (k+1) * ρ ^ k * σ 0) := by
              rw [Finset.sum_mul]
          _ ≤ 2 * a * (Pp e (k+1) * ρ ^ k * σ 0) :=
              mul_le_mul_of_nonneg_right (geom_le a ha ha2 _) hB
      have h3 := ih k (by omega) (by omega)
      have hs1 : 0 ≤ √(1 + e (k+1)) := Real.sqrt_nonneg _
      have hc : 0 ≤ (1 + ε) * √(1 + e (k+1)) := mul_nonneg (by linarith) hs1
      calc σ (k+1) ≤ (1 + ε) * √(1 + e (k+1)) * σ k +
            ∑ t ∈ Icc 2 (k+1), a ^ (t-1) * σ (k+1-t) := h1
        _ ≤ (1 + ε) * √(1 + e (k+1)) * (Pp e k * ρ ^ k * σ 0) +
            2 * a * (Pp e (k+1) * ρ ^ k * σ 0) :=
            add_le_add (mul_le_mul_of_nonneg_left h3 hc) hsum
        _ = (1 + ε + 2 * a) * (Pp e (k+1) * ρ ^ k * σ 0) := by rw [Pp_succ]; ring
        _ ≤ ρ * (Pp e (k+1) * ρ ^ k * σ 0) := mul_le_mul_of_nonneg_right hρ1 hB
        _ = Pp e (k+1) * ρ ^ (k+1) * σ 0 := by rw [pow_succ]; ring

lemma quart (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : (1 + 2 * x) ^ 4 ≤ 1 + 80 * x := by
  have h2 : x ^ 2 ≤ x := by nlinarith
  have h3 : x ^ 3 ≤ x := by nlinarith
  have h4 : x ^ 4 ≤ x := by nlinarith
  nlinarith

lemma pow_bound (r : ℕ) (a ε : ℝ) (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (hx : ((r:ℝ) + 1) * (ε + a) ≤ 1) :
    ((1 + ε + 2 * a) ^ (r+1)) ^ 2 ≤ 1 + 80 * ((r:ℝ) + 1) * (ε + a) := by
  have hx0 : 0 ≤ ((r:ℝ) + 1) * (ε + a) := by positivity
  have h1 : 1 + ε + 2 * a ≤ Real.exp (2 * (ε + a)) := by
    have := Real.add_one_le_exp (2 * (ε + a)); linarith
  have h2 : (1 + ε + 2 * a) ^ (r+1) ≤ Real.exp (((r+1 : ℕ) : ℝ) * (2 * (ε + a))) := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (by linarith) h1 _
  have h3 : Real.exp (((r+1 : ℕ) : ℝ) * (2 * (ε + a))) =
      Real.exp (((r:ℝ) + 1) * (ε + a)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h3] at h2
  have hE := Real.abs_exp_sub_one_le (x := ((r:ℝ) + 1) * (ε + a))
    (by rw [abs_of_nonneg hx0]; exact hx)
  rw [abs_of_nonneg hx0] at hE
  have hE' : Real.exp (((r:ℝ) + 1) * (ε + a)) ≤ 1 + 2 * (((r:ℝ) + 1) * (ε + a)) := by
    linarith [le_abs_self (Real.exp (((r:ℝ) + 1) * (ε + a)) - 1)]
  have hEn : 0 ≤ Real.exp (((r:ℝ) + 1) * (ε + a)) := (Real.exp_pos _).le
  have hρn : 0 ≤ (1 + ε + 2 * a) ^ (r+1) := pow_nonneg (by linarith) _
  have s1 := pow_le_pow_left₀ hρn h2 2
  have s2 := pow_le_pow_left₀ hEn hE' 4
  have s3 := quart (((r:ℝ) + 1) * (ε + a)) hx0 hx
  have e4 : (Real.exp (((r:ℝ) + 1) * (ε + a)) ^ 2) ^ 2 =
      Real.exp (((r:ℝ) + 1) * (ε + a)) ^ 4 := by ring
  have e5 : 80 * ((r:ℝ) + 1) * (ε + a) = 80 * (((r:ℝ) + 1) * (ε + a)) := by ring
  rw [e5]
  linarith

end Formalism.FourierDecayAlt.P.Rec

namespace Formalism.FourierDecayAlt.P

open Finset Real Formalism.FourierDecayAlt.P.Rec

theorem sharp_recursion : Formalism.FourierDecayAlt.RecursionSharp := by
  refine ⟨80, ?_⟩
  intro r a ε e σ ha ha2 hε hx he hσ hrec
  have hg := growth r a ε e σ (1 + ε + 2 * a) ha ha2 hε he hσ hrec le_rfl (r+1) le_rfl
  have hpb := pow_bound r a ε ha hε hx
  have hsq := pow_le_pow_left₀ (hσ (r+1)) hg 2
  have hPs := Pp_sq he (r+1)
  have hσ0 : 0 ≤ σ 0 ^ 2 := sq_nonneg _
  have hprod : 0 ≤ ∏ i ∈ Icc 1 (r + 1), (1 + e i) := by rw [← hPs]; exact sq_nonneg _
  calc σ (r+1) ^ 2 ≤ (Pp e (r+1) * (1 + ε + 2 * a) ^ (r+1) * σ 0) ^ 2 := hsq
    _ = ((1 + ε + 2 * a) ^ (r+1)) ^ 2 * (Pp e (r+1) ^ 2) * σ 0 ^ 2 := by ring
    _ = ((1 + ε + 2 * a) ^ (r+1)) ^ 2 * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2 := by
        rw [hPs]
    _ ≤ (1 + 80 * ((r : ℝ) + 1) * (ε + a)) * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hσ0
        exact mul_le_mul_of_nonneg_right hpb hprod

end Formalism.FourierDecayAlt.P
