import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

namespace KCoord

section Mean

variable {S : Type*} [Fintype S]

theorem card_pos_real [Nonempty S] : (0 : ℝ) < Fintype.card S := by
  exact_mod_cast Fintype.card_pos

theorem finMean_mono [Nonempty S] {f h : S → ℝ} (hfh : ∀ s, f s ≤ h s) : finMean f ≤ finMean h :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun s _ => hfh s) card_pos_real.le

theorem finMean_add (f h : S → ℝ) : finMean (fun s => f s + h s) = finMean f + finMean h := by
  simp [finMean, Finset.sum_add_distrib, add_div]

theorem finMean_sub (f h : S → ℝ) : finMean (fun s => f s - h s) = finMean f - finMean h := by
  simp [finMean, Finset.sum_sub_distrib, sub_div]

theorem finMean_const_mul (c : ℝ) (f : S → ℝ) : finMean (fun s => c * f s) = c * finMean f := by
  simp [finMean, ← Finset.mul_sum, mul_div_assoc]

theorem finMean_const [Nonempty S] (c : ℝ) : finMean (fun _ : S => c) = c := by
  have h := (card_pos_real (S := S)).ne'
  simp only [finMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

end Mean

theorem mul_log_le (G a : ℝ) (hG : 0 ≤ G) (ha : 0 < a) :
    G * log (1 + a) ≤ π / 192 * a ^ 2 + 48 / π * G ^ 2 := by
  have h1 : log (1 + a) ≤ a := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + a by linarith)
    linarith
  have h2 : G * log (1 + a) ≤ G * a := mul_le_mul_of_nonneg_left h1 hG
  have hpi : 0 < π := Real.pi_pos
  have h3 : π / 192 * a ^ 2 + 48 / π * G ^ 2 - G * a = (π * a - 96 * G) ^ 2 / (192 * π) := by
    field_simp
    ring
  have h4 : 0 ≤ (π * a - 96 * G) ^ 2 / (192 * π) := by positivity
  linarith

theorem posLog_le_half_log (ρ : ℝ) (hρ : 0 < ρ) :
    posLog (1 / ρ) ≤ 1 / 2 * log (1 + (ρ ^ 2)⁻¹) := by
  have hx : 0 < 1 + (ρ ^ 2)⁻¹ := by positivity
  have h0 : 0 ≤ 1 / 2 * log (1 + (ρ ^ 2)⁻¹) := by
    have : 0 ≤ log (1 + (ρ ^ 2)⁻¹) := Real.log_nonneg (by
      have : 0 ≤ (ρ ^ 2)⁻¹ := by positivity
      linarith)
    linarith
  have h1 : log (1 / ρ) ≤ 1 / 2 * log (1 + (ρ ^ 2)⁻¹) := by
    have e : log (1 / ρ) = 1 / 2 * log ((ρ ^ 2)⁻¹) := by
      rw [one_div, Real.log_inv, Real.log_inv, Real.log_pow]
      push_cast
      ring
    rw [e]
    have : log ((ρ ^ 2)⁻¹) ≤ log (1 + (ρ ^ 2)⁻¹) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith
  simp only [Real.posLog]
  exact max_le h0 h1

end KCoord

theorem WeakMatrixArithmetic.intersectionNumber_baseChange : WeakMatrixArithmetic.Statement := by
  intro C₀ hC₀
  refine ⟨64 * (33 + C₀), by positivity, ?_⟩
  intro g _ S _ _ ρ Φ hρ hΦ hmean
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have hG : (0 : ℝ) ≤ g := by linarith
  set L := log (2 * (g : ℝ)) with hL
  have hLge : log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hlog2 : (1 / 2 : ℝ) < log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hLpos : 1 / 2 < L := by linarith
  have hpi3 : 3 < π := Real.pi_gt_three
  have hpi : 0 < π := Real.pi_pos
  set x : S → ℝ := fun s => (ρ s ^ 2)⁻¹ with hx
  set E : S → ℝ := fun s => g * log (1 + 1 / ρ s) + C₀ * g * L with hE
  set K : ℝ := 48 / π * (g : ℝ) ^ 2 + C₀ * g * L with hK

  have hEx : ∀ s, E s ≤ π / 192 * x s + K := by
    intro s
    have h := KCoord.mul_log_le (g : ℝ) (1 / ρ s) hG (by have := (hρ s).1; positivity)
    have e : (1 / ρ s) ^ 2 = x s := by simp [hx, one_div, inv_pow]
    rw [e] at h
    simp only [hE, hK]
    linarith

  have hK' : K ≤ (32 + C₀) * ((g : ℝ) ^ 2 * L) := by
    have h1 : 48 / π * (g : ℝ) ^ 2 ≤ 32 * ((g : ℝ) ^ 2 * L) := by
      have hg2 : 0 ≤ (g : ℝ) ^ 2 := by positivity
      have : 48 / π ≤ 16 := by
        rw [div_le_iff₀ hpi]; linarith
      have h16 : 16 * (g : ℝ) ^ 2 ≤ 32 * ((g : ℝ) ^ 2 * L) := by nlinarith
      nlinarith
    have h2 : C₀ * g * L ≤ C₀ * ((g : ℝ) ^ 2 * L) := by
      have : (g : ℝ) * L ≤ (g : ℝ) ^ 2 * L := by
        have : (g : ℝ) ≤ (g : ℝ) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this (by linarith)
      have := mul_le_mul_of_nonneg_left this hC₀
      linarith [mul_assoc C₀ (g : ℝ) L]
    simp only [hK]
    linarith
  have hgL : 0 ≤ (g : ℝ) ^ 2 * L := by have := sq_nonneg (g : ℝ); nlinarith

  have hmx : π / 192 * finMean x ≤ Φ + K := by
    have h1 : finMean (fun s => π / 96 * x s - E s) ≥ finMean (fun s => π / 192 * x s - K) :=
      KCoord.finMean_mono fun s => by have := hEx s; linarith
    have h2 : finMean (fun s => π / 192 * x s - K) = π / 192 * finMean x - K := by
      rw [KCoord.finMean_sub, KCoord.finMean_const_mul, KCoord.finMean_const]
    have h3 : finMean (fun s => π / 96 * x s - E s) ≤ Φ := hmean
    linarith
  have hmx' : finMean x ≤ 64 * (Φ + K) := by
    have : finMean x ≤ 192 / π * (Φ + K) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hpi]
      linarith
    have hΦK : 0 ≤ Φ + K := by
      have : 0 ≤ K := by simp only [hK]; positivity
      linarith
    have : 192 / π ≤ 64 := by rw [div_le_iff₀ hpi]; linarith
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  ·
    show finMean x ≤ _
    nlinarith
  ·
    show finMean E ≤ _
    have h0 : finMean E ≤ finMean (fun s => π / 192 * x s + K) := KCoord.finMean_mono hEx
    have h0' : finMean (fun s => π / 192 * x s + K) = π / 192 * finMean x + K := by
      rw [KCoord.finMean_add, KCoord.finMean_const_mul, KCoord.finMean_const]
    have h1 : finMean E ≤ π / 192 * finMean x + K := h0.trans h0'.le
    nlinarith
  ·
    have hpt : ∀ s, posLog (1 / ρ s) ≤ 1 / 2 * log (1 + x s) := fun s =>
      KCoord.posLog_le_half_log (ρ s) (hρ s).1
    have h1 := KCoord.finMean_mono hpt
    rw [KCoord.finMean_const_mul] at h1
    have hj : finMean (fun s => log (1 + x s)) ≤ log (1 + finMean x) := by
      have hcard := (KCoord.card_pos_real (S := S))
      have hJ := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := Finset.univ)
        (w := fun _ : S => (1 : ℝ) / Fintype.card S) (p := fun s => 1 + x s)
        (fun _ _ => by positivity)
        (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
        (fun s _ => by
          show (0 : ℝ) < 1 + x s
          have : 0 ≤ x s := by simp only [hx]; positivity
          linarith)
      simp only [smul_eq_mul] at hJ
      have e1 : ∑ s, 1 / (Fintype.card S : ℝ) * log (1 + x s) = finMean fun s => log (1 + x s) := by
        simp [finMean, ← Finset.mul_sum, div_eq_inv_mul]
      have e2 : ∑ s, 1 / (Fintype.card S : ℝ) * (1 + x s) = 1 + finMean x := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, finMean]
        field_simp
      rw [e1, e2] at hJ
      exact hJ
    linarith

end GroundTheory.Heights₂.Heights
