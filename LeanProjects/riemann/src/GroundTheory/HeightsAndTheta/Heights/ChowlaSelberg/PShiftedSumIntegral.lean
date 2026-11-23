import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.ShiftedSumIntegralStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open MeasureTheory Set Filter

noncomputable section

namespace ShiftedSumIntegral

theorem half_line {G : ℝ → ℝ} (anti : AntitoneOn G (Ici 0)) (hint : Integrable G)
    (nonneg : ∀ x, 0 ≤ G x) {w : ℝ} (hw : 0 ≤ w) :
    Summable (fun k : ℕ ↦ G (k + w)) ∧ ∫ x in Ioi w, G x ≤ ∑' k : ℕ, G (k + w) ∧
      ∑' k : ℕ, G (k + w) ≤ G w + ∫ x in Ioi w, G x := by
  have hshift : ∫ x in Ioi 0, G (x + w) = ∫ x in Ioi w, G x := by
    have A : MeasurableEmbedding fun x : ℝ ↦ x + w :=
      (Homeomorph.addRight w).isClosedEmbedding.measurableEmbedding
    have := A.setIntegral_map (μ := volume) G (Ioi w)
    rw [map_add_right_eq_self] at this
    rw [this]
    simp
  have anti' : AntitoneOn (fun x ↦ G (x + w)) (Ici 0) := fun x hx y hy hxy ↦
    anti (mem_Ici.2 (by linarith [mem_Ici.1 hx])) (mem_Ici.2 (by linarith [mem_Ici.1 hy]))
      (by linarith)
  have int' : IntegrableOn (fun x ↦ G (x + w)) (Ioi 0) := (hint.comp_add_right w).integrableOn
  have sm := anti'.summable_of_integrableOn_Ioi_zero int' (fun x _ ↦ nonneg _)
  refine ⟨sm, ?_, ?_⟩
  · rw [← hshift]
    exact anti'.integral_le_tsum sm (fun x _ ↦ nonneg _)
  · rw [← hshift]
    simpa using anti'.tsum_le_integral int' (fun x _ ↦ nonneg _)

theorem proof : ShiftedSumIntegral.Statement := by
  intro a u s ha hs
  set G : ℝ → ℝ := fun x ↦ (x ^ 2 + a ^ 2) ^ (-s) with hGdef
  show Summable (fun n : ℤ ↦ G (n + u)) ∧ |∑' n : ℤ, G (n + u) - ∫ t, G t| ≤ a ^ (-2 * s)
  have hpos : ∀ x, 0 < x ^ 2 + a ^ 2 := fun x ↦ by positivity
  have nonneg : ∀ x, 0 ≤ G x := fun x ↦ Real.rpow_nonneg (hpos x).le _
  have cont : Continuous G :=
    (by fun_prop : Continuous fun x : ℝ ↦ x ^ 2 + a ^ 2).rpow_const fun x ↦ Or.inl (hpos x).ne'
  have anti : AntitoneOn G (Ici 0) := fun x hx y hy hxy ↦
    Real.rpow_le_rpow_of_nonpos (hpos x) (by nlinarith [mem_Ici.1 hx]) (by linarith)
  have even : ∀ x, G (-x) = G x := fun x ↦ by simp only [hGdef, neg_sq]
  have hG0 : G 0 = a ^ (-2 * s) := by
    show ((0 : ℝ) ^ 2 + a ^ 2) ^ (-s) = a ^ (-2 * s)
    rw [show (0 : ℝ) ^ 2 + a ^ 2 = a ^ (2 : ℝ) by rw [Real.rpow_two]; ring,
      ← Real.rpow_mul ha.le]
    ring_nf
  have hint : Integrable G := by
    have hm : 0 < min 1 (a ^ 2) := lt_min one_pos (by positivity)
    refine ((integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * s)
      (by simp; linarith)).const_mul (min 1 (a ^ 2) ^ (-s))).mono' cont.aestronglyMeasurable
      (Eventually.of_forall fun t ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (nonneg t), Real.norm_eq_abs, sq_abs,
      show -(2 * s) / 2 = -s by ring, ← Real.mul_rpow hm.le (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (by nlinarith [min_le_left 1 (a ^ 2), min_le_right 1 (a ^ 2),
        mul_le_mul_of_nonneg_right (min_le_left 1 (a ^ 2)) (sq_nonneg t)]) (by linarith)
  have hJ : ∫ t, G t = 2 * ∫ x in Ioi 0, G x := by
    rw [← integral_comp_abs (f := G)]
    congr 1
    ext x
    simp only [hGdef, sq_abs]
  have hseg : ∀ y, 0 ≤ y → y * G y ≤ ∫ x in (0 : ℝ)..y, G x ∧ ∫ x in (0 : ℝ)..y, G x ≤ y * G 0 := by
    intro y hy
    constructor
    · have := intervalIntegral.integral_mono_on hy (intervalIntegrable_const (μ := volume))
        (cont.intervalIntegrable 0 y) (fun x hx ↦ anti (mem_Ici.2 hx.1) (mem_Ici.2 hy) hx.2)
      simpa using this
    · have := intervalIntegral.integral_mono_on hy (cont.intervalIntegrable 0 y)
        (intervalIntegrable_const (μ := volume)) (fun x hx ↦ anti (mem_Ici.2 le_rfl) (mem_Ici.2 hx.1) hx.1)
      simpa using this
  have htail : ∀ y, 0 ≤ y → ∫ x in Ioi y, G x = (∫ x in Ioi 0, G x) - ∫ x in (0 : ℝ)..y, G x :=
    fun y hy ↦ by
      have e : (∫ x in Ioi 0, G x) - (∫ x in Ioi y, G x) = ∫ x in (0 : ℝ)..y, G x :=
        intervalIntegral.integral_Ioi_sub_Ioi hint.integrableOn hy
      linarith

  have core : ∀ w : ℝ, 0 ≤ w → w < 1 →
      Summable (fun m : ℤ ↦ G (m + w)) ∧ |∑' m : ℤ, G (m + w) - ∫ t, G t| ≤ G 0 := by
    intro w hw0 hw1
    obtain ⟨sP, lP, uP⟩ := half_line anti hint nonneg hw0
    obtain ⟨sQ, lQ, uQ⟩ := half_line anti hint nonneg (by linarith : 0 ≤ 1 - w)
    have hneg : ∀ n : ℕ, G (((-((n : ℤ) + 1) : ℤ) : ℝ) + w) = G (n + (1 - w)) := fun n ↦ by
      rw [← even]; congr 1; push_cast; ring
    have sQ' : Summable (fun n : ℕ ↦ G (((-((n : ℤ) + 1) : ℤ) : ℝ) + w)) := by
      convert sQ using 1; funext n; exact hneg n
    have hT : ∑' m : ℤ, G (m + w) = ∑' k : ℕ, G (k + w) + ∑' k : ℕ, G (k + (1 - w)) := by
      rw [tsum_of_nat_of_neg_add_one (f := fun m : ℤ ↦ G (m + w)) (by exact_mod_cast sP) sQ']
      push_cast
      congr 1
      exact tsum_congr fun n ↦ by rw [← hneg n]; push_cast; ring_nf
    refine ⟨Summable.of_nat_of_neg_add_one (by exact_mod_cast sP) sQ', ?_⟩
    obtain ⟨lw, uw⟩ := hseg w hw0
    obtain ⟨lv, uv⟩ := hseg (1 - w) (by linarith)
    rw [htail w hw0] at lP uP
    rw [htail (1 - w) (by linarith)] at lQ uQ
    have gw : G w ≤ G 0 := anti (mem_Ici.2 le_rfl) (mem_Ici.2 hw0) hw0
    have gv : G (1 - w) ≤ G 0 := anti (mem_Ici.2 le_rfl) (mem_Ici.2 (by linarith)) (by linarith)
    have h1 : G w * (1 - w) ≤ G 0 * (1 - w) := mul_le_mul_of_nonneg_right gw (by linarith)
    have h2 : G (1 - w) * w ≤ G 0 * w := mul_le_mul_of_nonneg_right gv hw0
    rw [hT, hJ, abs_le]
    constructor
    · linarith
    · linarith
  have key : ∀ n : ℤ, G (n + u) =
      (fun m : ℤ ↦ G (m + Int.fract u)) (Equiv.addRight ⌊u⌋ n) := fun n ↦ by
    simp only [Equiv.coe_addRight, Int.cast_add]
    rw [add_assoc, Int.floor_add_fract]
  obtain ⟨hs', hb⟩ := core (Int.fract u) (Int.fract_nonneg u) (Int.fract_lt_one u)
  rw [← hG0]
  refine ⟨?_, ?_⟩
  · rw [show (fun n : ℤ ↦ G (n + u)) = _ from funext key]
    exact (Equiv.addRight ⌊u⌋).summable_iff.2 hs'
  · rw [tsum_congr key, (Equiv.addRight ⌊u⌋).tsum_eq (fun m : ℤ ↦ G (m + Int.fract u))]
    exact hb

end ShiftedSumIntegral

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
