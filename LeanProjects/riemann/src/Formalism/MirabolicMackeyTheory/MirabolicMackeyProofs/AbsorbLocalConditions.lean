import Mathlib
import Formalism.MirabolicMackeyTheory.StatementT
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.BoundsChain

open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

theorem errGood_nonneg (Y X2 A1 A2 kw T : ℝ) (th add : ℕ → ℝ) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (hkw : 0 ≤ kw) (hT : 0 ≤ T) (hth : ∀ p, 0 ≤ th p) (hadd : ∀ p, 0 ≤ add p) (p : ℕ) :
    0 ≤ errGood Y X2 A1 A2 kw T th add p := by
  have hp : (0:ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have e1 : 0 ≤ A1 / (p : ℝ) := div_nonneg hA1 hp
  have e2 : 0 ≤ kw * th p := mul_nonneg hkw (hth p)
  have e3 : 0 ≤ T * add p := mul_nonneg hT (hadd p)
  have e4 : 0 ≤ A2 / (p : ℝ) ^ 2 := div_nonneg hA2 (by positivity)
  unfold errGood
  split_ifs <;> linarith

theorem onSum_of (hP : PlaceSum) (hR : RamBasic) (hE : ErrSumGood) : OnSum := by
  unfold OnSum
  intro K _ _ _ S Bad eb heb Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hPS
    errl herr
  set X : ℕ → ℝ := fun p => if p ∈ Bad then eb p else errGood Y X2 A1 A2 kw T th add p with hX
  have hX0 : ∀ p, 0 ≤ X p := fun p => by
    simp only [hX]
    split_ifs
    · exact heb p
    · exact errGood_nonneg Y X2 A1 A2 kw T th add hA1 hA2 hkw hT hth hadd p
  have hlw : ∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ lw w := fun w => by
    unfold lw
    exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have hram : ∀ w : HeightOneSpectrum (𝓞 K), (0:ℝ) ≤ (ramw w : ℝ) := fun w => by
    have h1 := (hR K w).2.1
    exact_mod_cast (le_trans (by norm_num) h1)
  have step1 : ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w) ≤
      ∑ w ∈ S, lw w * ((ramw w : ℝ) * X (plc w)) :=
    Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (herr w hw) (hram w)) (hlw w)
  have step2 := hP K S X hX0
  have hsplit := Finset.sum_filter_add_sum_filter_not (S.image plc) (fun p => p ∈ Bad)
    (fun p => Real.log (p : ℝ) * X p)
  have step3 : ∑ p ∈ (S.image plc).filter (fun p => p ∈ Bad), Real.log (p : ℝ) * X p ≤
      ∑ p ∈ Bad, Real.log (p : ℝ) * eb p := by
    calc _ = ∑ p ∈ (S.image plc).filter (fun p => p ∈ Bad), Real.log (p : ℝ) * eb p :=
          Finset.sum_congr rfl fun p hp => by
            rw [Finset.mem_filter] at hp
            simp only [hX, if_pos hp.2]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.mp hp).2)
          (fun p _ _ => mul_nonneg (Real.log_natCast_nonneg p) (heb p))
  have step4 : ∑ p ∈ (S.image plc).filter (fun p => p ∉ Bad), Real.log (p : ℝ) * X p ≤
      2 * (A1 * Real.log Y + kw * Cth + Cadd + 2.04 * A2 / X2 + 1.02 * Y) := by
    have hprime : ∀ p ∈ (S.image plc).filter (fun p => p ∉ Bad), p.Prime := by
      intro p hp
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hp).1
      exact (hR K w).1
    calc _ = ∑ p ∈ (S.image plc).filter (fun p => p ∉ Bad),
            Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p :=
          Finset.sum_congr rfl fun p hp => by
            rw [Finset.mem_filter] at hp
            simp only [hX, if_neg hp.2]
      _ ≤ _ := hE _ hprime Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hPS
  linarith

theorem absorb_local_conditions : AbsorbOn := by
  unfold AbsorbOn
  intro C Cb L xe f m b k ws Se Y X2 bad hC hCb hL hLx hf hm hb hk hlk hws0 hws hSe hkSe hY hlY
    hYmb hkX hbad
  have hC0 : (0:ℝ) ≤ C := by linarith
  have hf0 : (0:ℝ) ≤ f := by linarith
  have hm0 : (0:ℝ) ≤ m := by linarith
  have hL0 : (0:ℝ) ≤ L := by linarith
  have hk0 : (0:ℝ) < k := by linarith
  have hX2 : (0:ℝ) < X2 := by linarith
  have hxe : (1:ℝ) ≤ xe := by linarith
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg hk
  have hfmb : 0 ≤ f * m * b := mul_nonneg (mul_nonneg hf0 hm0) hb.le
  have hQ : 0 ≤ f * m * b * L := mul_nonneg hfmb hL0
  have hLxe : 1 ≤ L * xe := one_le_mul_of_one_le_of_one_le hL hxe
  have fmb_le : f * m * b ≤ f * m * b * L * xe := by
    have := mul_le_mul_of_nonneg_left hLxe hfmb
    linarith
  have QL_le : f * m * b * L * L ≤ f * m * b * L * xe := mul_le_mul_of_nonneg_left hLx hQ
  have hQx : 0 ≤ f * m * b * L * xe := by linarith
  have hA0 : 0 ≤ Real.log k * m * ws := mul_nonneg (mul_nonneg hlogk hm0) hws0
  have hB0 : 0 ≤ f * k * Se := mul_nonneg (mul_nonneg hf0 hk0.le) hSe
  have a1 : Real.log k * (m * ws) ≤ L * (m * (2 * f * b)) :=
    mul_le_mul hlk (mul_le_mul_of_nonneg_left hws hm0) (mul_nonneg hm0 hws0) hL0
  have a2 : f * (k * Se * L) ≤ f * (m * b) := mul_le_mul_of_nonneg_left hkSe hf0
  have t1a : (Real.log k * m * ws + f * k * Se) * Real.log Y ≤
      (Real.log k * m * ws + f * k * Se) * (2 * L) :=
    mul_le_mul_of_nonneg_left hlY (add_nonneg hA0 hB0)
  have t1b : Real.log k * m * ws * (2 * L) ≤ 2 * (f * m * b * L) * (2 * L) := by
    have h1 : Real.log k * m * ws ≤ 2 * (f * m * b * L) := by linarith
    exact mul_le_mul_of_nonneg_right h1 (by linarith)
  have t1 : (Real.log k * m * ws + f * k * Se) * Real.log Y ≤ 6 * (f * m * b * L * xe) := by
    linarith
  have u1 : C * ((Real.log k * m * ws + f * k * Se) * Real.log Y) ≤
      C * (6 * (f * m * b * L * xe)) := mul_le_mul_of_nonneg_left t1 hC0
  have fb_le : f * b ≤ f * m * b := by
    have := mul_le_mul_of_nonneg_left hm (mul_nonneg hf0 hb.le)
    linarith
  have ws_le : ws ≤ 2 * (f * m * b * L * xe) := by linarith
  have u2 : C ^ 2 * ws ≤ C ^ 2 * (2 * (f * m * b * L * xe)) :=
    mul_le_mul_of_nonneg_left ws_le (by positivity)
  have mb_le : m * b ≤ f * m * b * L * xe := by
    have := mul_le_mul_of_nonneg_left hf (mul_nonneg hm0 hb.le)
    linarith
  have u3 : C * (m * b) ≤ C * (f * m * b * L * xe) := mul_le_mul_of_nonneg_left mb_le hC0
  have u4 : C * ws ≤ C * (2 * (f * m * b * L * xe)) := mul_le_mul_of_nonneg_left ws_le hC0
  have u5a : f * m * b * L * xe ≤ C * (f * m * b * L * xe) := le_mul_of_one_le_left hQx hC
  have u6a : Cb * (f * m * b * L) ≤ Cb * (f * m * b * L * xe) := by
    have := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hQ hxe) hCb
    linarith
  have u8 : 0 ≤ C * (f * m * b * L * xe) := mul_nonneg hC0 hQx
  have t2e : C * k * ws * (C / k) = C ^ 2 * ws := by
    have : k ≠ 0 := hk0.ne'
    field_simp
  have t4 : 2.04 * (C * k * ws) / X2 ≤ 2.04 * (C * ws) := by
    rw [div_le_iff₀ hX2]
    have := mul_le_mul_of_nonneg_left hkX (mul_nonneg hC0 hws0)
    linarith
  linarith

end Formalism.EigenvalueLevelCeiling
