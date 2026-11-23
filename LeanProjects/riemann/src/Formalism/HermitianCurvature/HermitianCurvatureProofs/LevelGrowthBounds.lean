import Formalism.HermitianCurvature.LevelRecursionCondNeeded
import Mathlib

namespace Formalism.FourierDecayAlt.P.LevelGrowthBounds

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

lemma growth (r : ℕ) (ε δ : ℝ) (e a : ℕ → ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1/2)
    (he : ∀ i, 0 ≤ e i) (ha : ∀ i, 0 ≤ a i)
    (hrec : ∀ i, 1 ≤ i → i ≤ r + 1 →
      a i ≤ √(1 + e i) * ((1 + ε) * a (i - 1) + ∑ s ∈ Icc 2 i, δ ^ (s - 1) * a (i - s))) :
    ∀ i, i ≤ r + 1 → a i ≤ (1 + (ε + 2 * δ)) ^ i * Pp e i * a 0 := by
  set ρ : ℝ := 1 + (ε + 2 * δ) with hρdef
  have hρ : (1:ℝ) ≤ ρ := by rw [hρdef]; linarith
  have hρ0 : (0:ℝ) ≤ ρ := by linarith
  have ha0 := ha 0
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases i with _ | k
    · simp [Pp_zero]
    · have h1 := hrec (k+1) (by omega) hi
      simp only [Nat.add_sub_cancel] at h1
      have hB : 0 ≤ ρ ^ k * Pp e k * a 0 :=
        mul_nonneg (mul_nonneg (pow_nonneg hρ0 _) (Pp_nonneg he _)) ha0
      have hsum : ∑ s ∈ Icc 2 (k+1), δ ^ (s-1) * a (k+1-s) ≤
          2 * δ * (ρ ^ k * Pp e k * a 0) := by
        calc ∑ s ∈ Icc 2 (k+1), δ ^ (s-1) * a (k+1-s)
            ≤ ∑ s ∈ Icc 2 (k+1), δ ^ (s-1) * (ρ ^ k * Pp e k * a 0) := by
              apply Finset.sum_le_sum
              intro s hs
              have hs' := Finset.mem_Icc.mp hs
              apply mul_le_mul_of_nonneg_left _ (pow_nonneg hδ _)
              calc a (k+1-s) ≤ ρ ^ (k+1-s) * Pp e (k+1-s) * a 0 := ih _ (by omega) (by omega)
                _ ≤ ρ ^ k * Pp e k * a 0 := by
                  apply mul_le_mul_of_nonneg_right _ ha0
                  exact mul_le_mul (pow_le_pow_right₀ hρ (by omega)) (Pp_mono he (by omega))
                    (Pp_nonneg he _) (pow_nonneg hρ0 _)
          _ = (∑ s ∈ Icc 2 (k+1), δ ^ (s-1)) * (ρ ^ k * Pp e k * a 0) := by
              rw [Finset.sum_mul]
          _ ≤ 2 * δ * (ρ ^ k * Pp e k * a 0) :=
              mul_le_mul_of_nonneg_right (geom_le δ hδ hδ2 _) hB
      have h3 := ih k (by omega) (by omega)
      have hs1 : 0 ≤ √(1 + e (k+1)) := Real.sqrt_nonneg _
      have hc : (0:ℝ) ≤ 1 + ε := by linarith
      calc a (k+1) ≤ √(1 + e (k+1)) * ((1 + ε) * a k +
            ∑ s ∈ Icc 2 (k+1), δ ^ (s-1) * a (k+1-s)) := h1
        _ ≤ √(1 + e (k+1)) * ((1 + ε) * (ρ ^ k * Pp e k * a 0) +
            2 * δ * (ρ ^ k * Pp e k * a 0)) :=
            mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left h3 hc) hsum) hs1
        _ = ρ ^ (k+1) * Pp e (k+1) * a 0 := by rw [Pp_succ, pow_succ, hρdef]; ring

lemma pow_bound (r : ℕ) (η : ℝ) (hη : 0 ≤ η) (hx : ((r:ℝ) + 1) * η ≤ 1 / 2) :
    ((1 + η) ^ (r+1)) ^ 2 ≤ 1 + 4 * ((r:ℝ) + 1) * η := by
  have hx0 : 0 ≤ ((r:ℝ) + 1) * η := by positivity
  have h1 : 1 + η ≤ Real.exp η := by
    have := Real.add_one_le_exp η; linarith
  have h2 : ((1 + η) ^ (r+1)) ^ 2 ≤ Real.exp (2 * (((r:ℝ) + 1) * η)) := by
    rw [← pow_mul]
    have h3 : Real.exp (2 * (((r:ℝ) + 1) * η)) = Real.exp η ^ ((r+1) * 2) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h3]
    exact pow_le_pow_left₀ (by linarith) h1 _
  have hy0 : 0 ≤ 2 * (((r:ℝ) + 1) * η) := by linarith
  have hE := Real.abs_exp_sub_one_le (x := 2 * (((r:ℝ) + 1) * η))
    (by rw [abs_of_nonneg hy0]; linarith)
  rw [abs_of_nonneg hy0] at hE
  have hE' := le_abs_self (Real.exp (2 * (((r:ℝ) + 1) * η)) - 1)
  nlinarith

lemma half_bound (r : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 8) (hr : (r:ℝ) * (12 * u) ≤ 1) :
    ((r:ℝ) + 1) * (3 * u) ≤ 1 / 2 := by
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; simp; linarith
  · have h1 : (1:ℝ) ≤ r := by exact_mod_cast h
    nlinarith [mul_le_mul_of_nonneg_right h1 hu0]

end Formalism.FourierDecayAlt.P.LevelGrowthBounds

namespace Formalism.FourierDecayAlt.P

open Finset Real Formalism.FourierDecayAlt.P.LevelGrowthBounds

theorem level_recursion_lower_sum : Formalism.FourierDecayAlt.F7.LevelRecursionLS := by
  intro r ε δ e a hε hδ hδ2 he ha hrec
  have hg := growth r ε δ e a hε hδ hδ2 he ha hrec
  refine ⟨fun i hi => hg i hi, fun hx => ?_⟩
  have hη : 0 ≤ ε + 2 * δ := by linarith
  have hpb := pow_bound r (ε + 2 * δ) hη hx
  have hsq := pow_le_pow_left₀ (ha (r+1)) (hg (r+1) le_rfl) 2
  have hPs := Pp_sq he (r+1)
  have ha0 : 0 ≤ a 0 ^ 2 := sq_nonneg _
  have hprod : 0 ≤ ∏ i ∈ Icc 1 (r + 1), (1 + e i) := by rw [← hPs]; exact sq_nonneg _
  calc a (r+1) ^ 2 ≤ ((1 + (ε + 2 * δ)) ^ (r+1) * Pp e (r+1) * a 0) ^ 2 := hsq
    _ = ((1 + (ε + 2 * δ)) ^ (r+1)) ^ 2 * (Pp e (r+1) ^ 2) * a 0 ^ 2 := by ring
    _ = ((1 + (ε + 2 * δ)) ^ (r+1)) ^ 2 * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * a 0 ^ 2 := by
        rw [hPs]
    _ ≤ (1 + 4 * ((r : ℝ) + 1) * (ε + 2 * δ)) * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * a 0 ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ ha0
        exact mul_le_mul_of_nonneg_right hpb hprod

theorem levelRecursion_statement : Formalism.FourierDecayAlt.F7.LevelRecursion := by
  intro r ε δ e a hε hδ hδ2 he ha hrec
  refine level_recursion_lower_sum r ε δ e a hε hδ hδ2 he ha ?_
  intro i h1 h2
  have hS : 0 ≤ ∑ s ∈ Icc 2 i, δ ^ (s - 1) * a (i - s) :=
    Finset.sum_nonneg fun s _ => mul_nonneg (pow_nonneg hδ _) (ha _)
  have hq := one_le_sqrt_e he i
  have := hrec i h1 h2
  nlinarith [mul_le_mul_of_nonneg_right hq hS]

theorem levelRecursionCondNeeded_statement : Formalism.FourierDecayAlt.F7.LevelRecursionCondNeeded := by
  intro h
  have := h 2 (1/3) 0 (fun _ => 0) (fun i => (4/3 : ℝ) ^ i) (by norm_num) le_rfl (by norm_num)
    (fun _ => le_rfl) (fun _ => by norm_num) (fun i => by positivity)
    (by
      intro i h1 _
      have : ∑ s ∈ Icc 2 i, (0:ℝ) ^ (s - 1) * (4/3 : ℝ) ^ (i - s) = 0 := by
        apply Finset.sum_eq_zero
        intro s hs
        have : s - 1 ≠ 0 := by have := (Finset.mem_Icc.mp hs).1; omega
        simp [this]
      rw [this]
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      simp [pow_succ]; linarith [pow_pos (show (0:ℝ) < 4/3 by norm_num) k])
    (by norm_num)
  norm_num at this

theorem choice_of_constants : Formalism.FourierDecayAlt.F7.ChoiceOfConstants := by
  intro C₁ CE C' C Θ Kx f r hC₁ hCE hf hK hC' hC hΘ' hΘ hr
  have hΘ0 : 0 < Θ := by linarith
  have hf0 : f ≠ 0 := by omega

  have hd0 : 0 ≤ C₁ / Θ := by positivity
  have hc0 : 0 ≤ CE / Θ := by positivity
  have hu0 : 0 ≤ (C₁ + CE) / Θ := by positivity
  have hu8 : (C₁ + CE) / Θ ≤ 1 / 8 := by
    rw [div_le_iff₀ hΘ0]; linarith
  have hdu : C₁ / Θ ≤ (C₁ + CE) / Θ := by
    apply div_le_div_of_nonneg_right _ hΘ0.le; linarith
  have hcu : CE / Θ ≤ (C₁ + CE) / Θ := by
    apply div_le_div_of_nonneg_right _ hΘ0.le; linarith
  have hrp : Θ ^ (-(Kx - 5 / 2)) ≤ Θ⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hΘ (by linarith)
  have hrp0 : 0 ≤ Θ ^ (-(Kx - 5 / 2)) := Real.rpow_nonneg hΘ0.le _
  have he0 : 0 ≤ CE * Θ ^ (-(Kx - 5 / 2)) := mul_nonneg hCE.le hrp0
  have hec : CE * Θ ^ (-(Kx - 5 / 2)) ≤ CE / Θ := by
    rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hrp hCE.le

  have p1 : (C₁ / Θ) ^ f ≤ (1 / 8 : ℝ) ^ f := pow_le_pow_left₀ hd0 (hdu.trans hu8) f
  have p8 : (1 / 8 : ℝ) ^ f ≤ 1 / 8 := by
    have := pow_le_pow_of_le_one (show (0:ℝ) ≤ 1 / 8 by norm_num) (by norm_num) hf
    simpa using this
  have p3 : (CE * Θ ^ (-(Kx - 5 / 2))) ^ f ≤ (CE / Θ) ^ f := pow_le_pow_left₀ he0 hec f
  have pdu : (C₁ / Θ) ^ f ≤ ((C₁ + CE) / Θ) ^ f := pow_le_pow_left₀ hd0 hdu f
  have pcu : (CE / Θ) ^ f ≤ ((C₁ + CE) / Θ) ^ f := pow_le_pow_left₀ hc0 hcu f
  have pu8 : ((C₁ + CE) / Θ) ^ f ≤ 1 / 8 := (pow_le_pow_left₀ hu0 hu8 f).trans p8
  have pu0 : 0 ≤ ((C₁ + CE) / Θ) ^ f := pow_nonneg hu0 f
  have p4 : (CE * Θ ^ (-(Kx - 5 / 2))) ^ f + 2 * (C₁ / Θ) ^ f ≤ 3 * ((C₁ + CE) / Θ) ^ f := by
    linarith

  have h12 : 12 * ((C₁ + CE) / Θ) ^ f ≤ (C / Θ) ^ f := by
    have a1 : (12:ℝ) ≤ 12 ^ f := by
      have := pow_le_pow_right₀ (show (1:ℝ) ≤ 12 by norm_num) hf
      simpa using this
    have a2 : (12 * ((C₁ + CE) / Θ)) ^ f ≤ (C / Θ) ^ f := by
      apply pow_le_pow_left₀ (by positivity)
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hC hΘ0.le
    rw [mul_pow] at a2
    nlinarith [mul_le_mul_of_nonneg_right a1 pu0]
  have hr12 : (r:ℝ) * (12 * ((C₁ + CE) / Θ) ^ f) ≤ 1 :=
    (mul_le_mul_of_nonneg_left h12 (Nat.cast_nonneg r)).trans hr
  have hh := half_bound r _ pu0 pu8 hr12
  refine ⟨p1, p1.trans p8, p3, p4, ?_⟩
  have hr1 : (0:ℝ) ≤ (r:ℝ) + 1 := by positivity
  exact (mul_le_mul_of_nonneg_left p4 hr1).trans hh

theorem constants_of_theorem_A : Formalism.FourierDecayAlt.F7.TheoremAConstants := by
  intro C₁ CE C' C Θ Kx f r e a hC₁ hCE hf hK hC' hC hΘ' hΘ hr he ha hrec
  obtain ⟨_, q2, _, q4, q5⟩ :=
    choice_of_constants C₁ CE C' C Θ Kx f r hC₁ hCE hf hK hC' hC hΘ' hΘ hr
  have hΘ0 : 0 < Θ := by linarith
  have hδ0 : 0 ≤ (C₁ / Θ) ^ f := by positivity
  have hε0 : 0 ≤ (CE * Θ ^ (-(Kx - 5 / 2))) ^ f :=
    pow_nonneg (mul_nonneg hCE.le (Real.rpow_nonneg hΘ0.le _)) _
  have hLS := (level_recursion_lower_sum r ((CE * Θ ^ (-(Kx - 5 / 2))) ^ f) ((C₁ / Θ) ^ f) e a
    hε0 hδ0 (by linarith) he ha (by
      intro i h1 h2
      refine (hrec i h1 h2).trans (le_of_eq ?_)
      rw [mul_add, Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro s _
        rw [pow_mul]; ring)).2 q5
  have ha0 : 0 ≤ a 0 ^ 2 := sq_nonneg _
  have hprod : 0 ≤ ∏ i ∈ Icc 1 (r + 1), (1 + e i) :=
    Finset.prod_nonneg fun i _ => by linarith [he i]
  have hr1 : (0:ℝ) ≤ (r:ℝ) + 1 := by positivity
  refine hLS.trans ?_
  apply mul_le_mul_of_nonneg_right _ ha0
  apply mul_le_mul_of_nonneg_right _ hprod
  nlinarith [mul_le_mul_of_nonneg_left q4 hr1]

end Formalism.FourierDecayAlt.P
