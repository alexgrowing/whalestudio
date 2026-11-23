import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorHensel
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorSub

noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {l : ℕ} [Fact l.Prime] {g2 g3 : ℂ_[l]}

theorem cubic_close {C : Type} [NormedField C] [IsUltrametricDist C] {x a p q : C} (hx : ‖x‖ ≤ 1)
    (ha : ‖a‖ ≤ 1) (hp : ‖p‖ ≤ 1) (hxa : ‖x - a‖ < 1) :
    ‖(a ^ 3 + p * a + q) - (x ^ 3 + p * x + q)‖ < 1 := by
  have e : (a ^ 3 + p * a + q) - (x ^ 3 + p * x + q) = (a - x) * (a ^ 2 + a * x + x ^ 2 + p) := by ring
  rw [e, norm_mul]
  have h1 : ‖a ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
  have h2 : ‖a * x‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hx
  have h3 : ‖x ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
  have hb : ‖a ^ 2 + a * x + x ^ 2 + p‖ ≤ 1 :=
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)) h3)) hp)
  rw [norm_sub_rev] at hxa
  calc ‖a - x‖ * ‖a ^ 2 + a * x + x ^ 2 + p‖ ≤ ‖a - x‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact hxa

theorem norm_one_of_close {C : Type} [NormedField C] [IsUltrametricDist C] {c d : C} (hd : ‖d‖ = 1)
    (h : ‖c - d‖ < 1) : ‖c‖ = 1 := by
  have hne : ‖d‖ ≠ ‖c - d‖ := by rw [hd]; exact (ne_of_lt h).symm
  have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [add_sub_cancel, hd] at h2
  rw [h2]
  exact max_eq_left h.le

theorem tor_lift (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (hP0 : P ≠ 0)
    (hx : ‖px _ P‖ ≤ 1) (hy : ‖py _ P‖ = 1) :
    ∃ Q : (shortW g2 g3).toAffine.Point, InSub (MaximalUnramifiedExtension l) Q ∧ InFormalGroupPoints (P - Q) := by
  have hI := good_int h
  have hC := good_coeff h
  obtain ⟨-, -, -, h4, h6, -⟩ := hI
  obtain ⟨-, -, -, m4, m6⟩ := hC
  have hl2 : l ≠ 2 := by have := h.five; omega
  cases P with
  | zero => exact absurd rfl hP0
  | some x y hns =>
    change ‖x‖ ≤ 1 at hx
    change ‖y‖ = 1 at hy
    obtain ⟨a, haT, hxa⟩ := res_full l x hx
    have haK : a ∈ MaximalUnramifiedExtension l := tch_mem_kur l haT
    have ha1 : ‖a‖ ≤ 1 := tch_norm_le l haT
    have hE : y ^ 2 = x ^ 3 + (shortW g2 g3).a₄ * x + (shortW g2 g3).a₆ := by
      have := (WeierstrassCurve.Affine.equation_iff _ _).1 hns.1
      simpa [shortW] using this
    set p := (shortW g2 g3).a₄ with hp
    set q := (shortW g2 g3).a₆ with hq
    have hc1 : ‖a ^ 3 + p * a + q‖ = 1 := by
      refine norm_one_of_close (d := y ^ 2) (by rw [norm_pow, hy, one_pow]) ?_
      rw [hE]
      exact cubic_close hx ha1 h4 hxa
    have hcK : a ^ 3 + p * a + q ∈ MaximalUnramifiedExtension l :=
      add_mem (add_mem (pow_mem haK 3) (mul_mem m4 haK)) m6
    obtain ⟨b, hbK, hb2, hb1⟩ := exists_sqrt l hl2 _ hcK hc1
    have hb0 : b ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hb1
      exact zero_ne_one hb1
    have hQns : (shortW g2 g3).toAffine.Nonsingular a b := by
      rw [WeierstrassCurve.Affine.nonsingular_iff]
      refine ⟨?_, Or.inr ?_⟩
      · rw [WeierstrassCurve.Affine.equation_iff]
        simp only [shortW] at hb2 hp hq ⊢
        rw [hb2, hp, hq]
        ring
      · simp only [shortW]
        intro hh
        apply hb0
        have h2 : (2 : ℂ_[l]) * b = 0 := by linear_combination hh
        rcases mul_eq_zero.1 h2 with h3 | h3
        · exact absurd h3 two_ne_zero
        · exact h3
    set P : (shortW g2 g3).toAffine.Point := .some x y hns with hPdef
    set Q : (shortW g2 g3).toAffine.Point := .some a b hQns with hQdef
    have hQS : InSub (MaximalUnramifiedExtension l) Q := ⟨haK, hbK⟩
    by_cases h1 : InFormalGroupPoints (P - Q)
    · exact ⟨Q, hQS, h1⟩
    by_cases h2 : InFormalGroupPoints (P + Q)
    · exact ⟨-Q, inSub_neg _ _ (good_coeff h) Q hQS, by rwa [sub_neg_eq_add]⟩
    exfalso
    obtain ⟨d0, dx, -⟩ := integral_of_not_mem_formalGroup h _ h1
    obtain ⟨s0, sx, -⟩ := integral_of_not_mem_formalGroup h _ h2
    have hu := Formalism.L2.Th1.E.UnitDiff_of Formalism.L2.Th1.E.nonsingular_norm ℂ_[l] (shortW g2 g3) (good_int h) P Q
      hP0 (WeierstrassCurve.Affine.Point.some_ne_zero _) s0 d0 hx hy.le ha1 hb1.le sx dx
    change ‖x - a‖ = 1 at hu
    exact absurd hu hxa.ne

end ReciprocityTheory.ChartRestriction.L1
