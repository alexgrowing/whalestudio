import Formalism.LogFactorialIndices.StatementSize

noncomputable section

namespace Formalism.LatticeIndexTer

open Finset

lemma ph_zero : ph 0 = 0 := by
  simp [ph]

lemma ph_ge_neg_one {x : ℝ} (hx : 0 ≤ x) : -1 ≤ ph x := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp [ph]
  · have h1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hx')
    rw [Real.log_inv] at h1
    have h2 : x * x⁻¹ = 1 := mul_inv_cancel₀ hx'.ne'
    have h3 := mul_le_mul_of_nonneg_left h1 hx
    rw [mul_sub, h2, mul_one, mul_neg] at h3
    unfold ph
    linarith

lemma le_ph_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * Real.log a ≤ ph b - ph a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 hb.le
  have h3 : b * (a / b - 1) = a - b := by field_simp <;> ring
  rw [h3] at h2
  unfold ph
  linarith

lemma ph_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : ph a ≤ ph b := by
  have h1 := le_ph_sub (by linarith : (0 : ℝ) < a) hab
  have h2 : 0 ≤ Real.log a := Real.log_nonneg ha
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) h2]

lemma one_le_log {t : ℝ} (ht : 3 ≤ t) : 1 ≤ Real.log t := by
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log t := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])

theorem alt_bound {α : Type*} [Preorder α] (f : α → ℝ) (hf : Monotone f) :
    ∀ (k : ℕ) (a : Fin (k + 1) → α) (b : Fin k → α),
      (∀ i : Fin k, b i ≤ a i.castSucc ∧ a i.succ ≤ b i) →
      f (a (Fin.last k)) ≤ (∑ i, f (a i)) - ∑ i, f (b i) ∧
      (∑ i, f (a i)) - ∑ i, f (b i) ≤ f (a 0) := by
  intro k
  induction k with
  | zero =>
    intro a b _
    refine ⟨?_, ?_⟩ <;> simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, sub_zero] <;> exact le_rfl
  | succ k ih =>
    intro a b hab
    have ih' := ih (fun i => a i.castSucc) (fun i => b i.castSucc)
      (fun i => ⟨(hab i.castSucc).1, (hab i.castSucc).2⟩)
    simp only [Fin.castSucc_zero] at ih'
    obtain ⟨h1, h2⟩ := hab (Fin.last k)
    have m1 := hf h1
    have m2 := hf h2
    rw [Fin.succ_last] at m2
    rw [Fin.sum_univ_castSucc (fun i => f (a i)), Fin.sum_univ_castSucc (fun i => f (b i))]
    constructor <;> linarith [ih'.1, ih'.2]

def phm (x : ℝ) : ℝ := ph (max x 1)

lemma phm_mono : Monotone phm := by
  intro x y hxy
  unfold phm
  exact ph_mono (le_max_right _ _) (max_le (le_trans hxy (le_max_left _ _)) (le_max_right _ _))

lemma phm_ge {x : ℝ} : -1 ≤ phm x := ph_ge_neg_one (le_trans zero_le_one (le_max_right x 1))

theorem sumInterlacedBound : Interlace := by
  intro k c c' S w hI hw
  obtain ⟨hc, hc'⟩ := hI
  have hS : 0 ≤ S := le_trans (hc 0).1 (hc 0).2
  have e1 : ∀ x : ℝ, 1 ≤ x → phm x = ph x := fun x hx => by unfold phm; rw [max_eq_left hx]
  have hb : phm (w + c (Fin.last k)) ≤ (∑ i, phm (w + c i)) - ∑ i, phm (w + c' i) ∧
      (∑ i, phm (w + c i)) - ∑ i, phm (w + c' i) ≤ phm (w + c 0) :=
    alt_bound phm phm_mono k (fun i => w + c i) (fun i => w + c' i)
      (fun i => ⟨by show w + c' i ≤ w + c i.castSucc; linarith [(hc' i).1],
        by show w + c i.succ ≤ w + c' i; linarith [(hc' i).2]⟩)
  have s1 : (∑ i, phm (w + c i)) = ∑ i, ph (w + c i) :=
    Finset.sum_congr rfl fun i _ => e1 _ (by linarith [(hc i).1])
  have s2 : (∑ i, phm (w + c' i)) = ∑ i, ph (w + c' i) :=
    Finset.sum_congr rfl fun i _ => e1 _ (by linarith [(hc' i).2, (hc i.succ).1])
  rw [s1, s2] at hb
  have e0 : phm (w + c 0) = ph (w + c 0) := e1 _ (by linarith [(hc 0).1])
  have up : ph (w + c 0) ≤ ph (w + S) := ph_mono (by linarith [(hc 0).1]) (by linarith [(hc 0).2])
  have lo : -1 ≤ phm (w + c (Fin.last k)) := phm_ge
  have hL : 1 ≤ Real.log (w + S + 2) := one_le_log (by linarith)
  have hphS : ph (w + S) ≤ (w + 2 * S) * Real.log (w + S + 2) := by
    have hl := Real.log_le_log (by linarith : 0 < w + S) (by linarith : w + S ≤ w + S + 2)
    unfold ph
    nlinarith [mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ w + S),
      mul_nonneg hS (by linarith : 0 ≤ Real.log (w + S + 2))]
  have hp : 1 ≤ (w + 2 * S) * Real.log (w + S + 2) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ w + 2 * S - 1) (by linarith : 0 ≤ Real.log (w + S + 2) - 1)]
  rw [abs_le]
  constructor
  · linarith [hb.1]
  · linarith [hb.2]

def chi (n : ℕ) : ℝ := if n = 0 then -1 else 0

end Formalism.LatticeIndexTer
