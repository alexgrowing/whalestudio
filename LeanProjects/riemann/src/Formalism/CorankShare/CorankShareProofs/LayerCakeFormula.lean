import Mathlib
import Formalism.CorankShare.StatementFR

noncomputable section

namespace Formalism.CorankShareLayerCake.FR

open Finset MeasureTheory

namespace Pgsn2pfran

lemma ind_anti (c : ℝ) : Antitone (fun τ : ℝ => if τ < c then (1:ℝ) else 0) := by
  intro a b hab
  show (if b < c then (1:ℝ) else 0) ≤ (if a < c then (1:ℝ) else 0)
  by_cases h1 : b < c
  · have h2 : a < c := lt_of_le_of_lt hab h1
    simp [h1, h2]
  · by_cases h2 : a < c <;> simp [h1, h2]

lemma ind_int (c HH : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ HH) :
    ∫ τ in (0:ℝ)..HH, (if τ < c then (1:ℝ) else 0) = c := by
  have hi1 : IntervalIntegrable (fun τ : ℝ => if τ < c then (1:ℝ) else 0) volume 0 c :=
    (ind_anti c).intervalIntegrable
  have hi2 : IntervalIntegrable (fun τ : ℝ => if τ < c then (1:ℝ) else 0) volume c HH :=
    (ind_anti c).intervalIntegrable
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
    rw [ae_iff]
    simp
  have h1 : ∫ τ in (0:ℝ)..c, (if τ < c then (1:ℝ) else 0) = ∫ τ in (0:ℝ)..c, (1:ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hne] with x hx hmem
    rw [Set.uIoc_of_le hc0] at hmem
    have hxc : x < c := lt_of_le_of_ne hmem.2 hx
    simp [hxc]
  have h2 : ∫ τ in c..HH, (if τ < c then (1:ℝ) else 0) = ∫ τ in c..HH, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hc] at hx
    simp [not_lt.mpr hx.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, h1, h2]
  simp

lemma ind_lb (a xj HH : ℝ) (h : a - HH ≤ xj) (hHH : 0 ≤ HH) :
    a - xj ≤ ∫ τ in (0:ℝ)..HH, (if τ < a - xj then (1:ℝ) else 0) := by
  rcases le_total (a - xj) 0 with h0 | h0
  · have hpos : 0 ≤ ∫ τ in (0:ℝ)..HH, (if τ < a - xj then (1:ℝ) else 0) := by
      apply intervalIntegral.integral_nonneg hHH
      intro u _
      split_ifs <;> norm_num
    linarith
  · exact le_of_eq (ind_int (a - xj) HH h0 (by linarith)).symm

end Pgsn2pfran

open Pgsn2pfran

theorem layer_cake_formula : LayerCake := by
  unfold LayerCake
  intro D x a HH w hD hHH hx hw hcnt
  have hDpos : (0:ℝ) < D := by exact_mod_cast hD
  have hcount : ∀ τ : ℝ, ∑ j, (if τ < a - x j then (1:ℝ) else 0) =
      ((Finset.univ.filter fun j => x j < a - τ).card : ℝ) := by
    intro τ
    rw [Finset.sum_boole]
    have hf : (Finset.univ.filter fun j => τ < a - x j) =
        (Finset.univ.filter fun j => x j < a - τ) :=
      Finset.filter_congr (fun j _ => by constructor <;> intro hh <;> linarith)
    rw [hf]
  have hanti : Antitone (fun τ : ℝ => ∑ j, (if τ < a - x j then (1:ℝ) else 0)) :=
    fun t1 t2 ht => Finset.sum_le_sum fun j _ => ind_anti (a - x j) ht
  have hint : ∫ τ in (0:ℝ)..HH, ∑ j, (if τ < a - x j then (1:ℝ) else 0) =
      ∑ j, ∫ τ in (0:ℝ)..HH, (if τ < a - x j then (1:ℝ) else 0) :=
    intervalIntegral.integral_finset_sum fun j _ => (ind_anti (a - x j)).intervalIntegrable
  have hsum : ∑ j, (a - x j) ≤ ∑ j, ∫ τ in (0:ℝ)..HH, (if τ < a - x j then (1:ℝ) else 0) :=
    Finset.sum_le_sum fun j _ => ind_lb a (x j) HH (hx j) hHH
  have hL : ∑ j, (a - x j) = (D:ℝ) * a - ∑ j, x j := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmono : ∫ τ in (0:ℝ)..HH, ∑ j, (if τ < a - x j then (1:ℝ) else 0) ≤
      ∫ τ in (0:ℝ)..HH, (D:ℝ) * min 1 (w τ) := by
    apply intervalIntegral.integral_mono_on hHH hanti.intervalIntegrable (hw.const_mul (D:ℝ))
    intro τ hτ
    show ∑ j, (if τ < a - x j then (1:ℝ) else 0) ≤ (D:ℝ) * min 1 (w τ)
    rw [hcount τ]
    have hc1 : (Finset.univ.filter fun j => x j < a - τ).card ≤ D := by
      calc _ ≤ (Finset.univ : Finset (Fin D)).card := Finset.card_filter_le _ _
        _ = D := by simp
    have hc1' : ((Finset.univ.filter fun j => x j < a - τ).card : ℝ) ≤ D := by
      exact_mod_cast hc1
    have hc2 := hcnt τ hτ
    rcases le_total 1 (w τ) with hw1 | hw1
    · rw [min_eq_left hw1]
      linarith
    · rw [min_eq_right hw1]
      linarith
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [le_div_iff₀ hDpos]
  linarith

end Formalism.CorankShareLayerCake.FR
