import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LandherrUnitNorm.UnitNormLoc
import Lemmata.GeneralBFactLeft.Imports

noncomputable section

open NumberField IsDedekindDomain
open PI.Landherr₃

namespace PI.OmLocU.Nrm

theorem ff_binary {k : Type} [Field k] [Fintype k] (t m e : k) (hD : t ^ 2 - 4 * m ≠ 0) :
    ∃ x y : k, x ^ 2 + t * x * y + m * y ^ 2 = e := by
  first | exact Bl.general_b_fact_left.goal1 .. | (apply Bl.general_b_fact_left.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left.goal1 <;> assumption)

theorem near_root {K : Type} [NormedField K] [IsUltrametricDist K] (α β γ y₀ y : K)
    (hg : ‖2 * α * y₀ + β‖ = 1) (hf : ‖α * y₀ ^ 2 + β * y₀ + γ‖ < 1) (hy : α * y ^ 2 + β * y + γ = 0) :
    ∃ z, α * z ^ 2 + β * z + γ = 0 ∧ ‖z - y₀‖ < 1 := by
  by_cases hα : α = 0
  · subst hα
    refine ⟨y, hy, ?_⟩
    have hβ : ‖β‖ = 1 := by simpa using hg
    have e : β * (y - y₀) = -(0 * y₀ ^ 2 + β * y₀ + γ) := by linear_combination hy
    have := congrArg norm e
    rw [norm_mul, hβ, one_mul, norm_neg] at this
    rw [this]; exact hf
  · set y' := -(β / α) - y with hy'
    have hq : α * y' ^ 2 + β * y' = α * y ^ 2 + β * y := by rw [hy']; field_simp; ring
    have hroot' : α * y' ^ 2 + β * y' + γ = 0 := by linear_combination hq + hy
    obtain ⟨a, ha_def⟩ : ∃ a, a = α * (y₀ - y) := ⟨_, rfl⟩
    obtain ⟨b, hb_def⟩ : ∃ b, b = α * (y₀ - y') := ⟨_, rfl⟩
    have hb' : b = α * y₀ + β + α * y := by rw [hb_def, hy']; field_simp; ring
    have hab : a + b = 2 * α * y₀ + β := by rw [ha_def, hb']; ring
    have hprod : a * b = α * (α * y₀ ^ 2 + β * y₀ + γ) := by
      rw [ha_def, hb']; linear_combination (-α) * hy
    have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
    have hpr : ‖a * b‖ < ‖α‖ := by
      rw [hprod, norm_mul]
      calc ‖α‖ * ‖α * y₀ ^ 2 + β * y₀ + γ‖ < ‖α‖ * 1 := by gcongr
        _ = ‖α‖ := mul_one _
    have hmax : 1 ≤ max ‖a‖ ‖b‖ := by
      rw [← hg, ← hab]; exact IsUltrametricDist.norm_add_le_max a b
    rcases le_max_iff.mp hmax with ha | hb
    · refine ⟨y', hroot', ?_⟩
      have hb : ‖b‖ < ‖α‖ := by
        have : ‖b‖ ≤ ‖a * b‖ := by
          rw [norm_mul a b]; exact le_mul_of_one_le_left (norm_nonneg b) ha
        exact this.trans_lt hpr
      have : ‖α‖ * ‖y₀ - y'‖ < ‖α‖ * 1 := by
        rw [← norm_mul, mul_one, ← hb_def]; exact hb
      rw [← norm_neg, neg_sub]
      exact lt_of_mul_lt_mul_left this hαpos.le
    · refine ⟨y, hy, ?_⟩
      have ha : ‖a‖ < ‖α‖ := by
        have : ‖a‖ ≤ ‖a * b‖ := by
          rw [norm_mul a b]; exact le_mul_of_one_le_right (norm_nonneg a) hb
        exact this.trans_lt hpr
      have : ‖α‖ * ‖y₀ - y‖ < ‖α‖ * 1 := by
        rw [← norm_mul, mul_one, ← ha_def]; exact ha
      rw [← norm_neg, neg_sub]
      exact lt_of_mul_lt_mul_left this hαpos.le

theorem norm_le_of_near {K : Type} [NormedField K] [IsUltrametricDist K] {z y₀ : K} (h : ‖z - y₀‖ < 1)
    (h0 : ‖y₀‖ ≤ 1) : ‖z‖ ≤ 1 := by
  have e : z = (z - y₀) + y₀ := by ring
  rw [e]; exact unitNormLoc_add_le h.le h0

theorem solve_int {K : Type} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (T M ε x₀ y₀ : K) (hT : ‖T‖ ≤ 1) (hM : ‖M‖ ≤ 1) (hD : ‖T ^ 2 - 4 * M‖ = 1) (hε : ‖ε‖ = 1)
    (hx : ‖x₀‖ ≤ 1) (hy : ‖y₀‖ ≤ 1) (h0 : ‖x₀ ^ 2 + T * x₀ * y₀ + M * y₀ ^ 2 - ε‖ < 1) :
    ∃ x y : K, ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧ x ^ 2 + T * x * y + M * y ^ 2 = ε := by
  have h2 : ‖(2 : K)‖ ≤ 1 := unitNormLoc_norm_two_le
  have hgx : ‖2 * x₀ + T * y₀‖ ≤ 1 :=
    unitNormLoc_add_le (unitNormLoc_mul_le h2 hx) (unitNormLoc_mul_le hT hy)
  rcases hgx.lt_or_eq with hlt | heq
  · have hgy : ‖2 * M * y₀ + T * x₀‖ = 1 := by
      have hle : ‖2 * M * y₀ + T * x₀‖ ≤ 1 :=
        unitNormLoc_add_le (unitNormLoc_mul_le (unitNormLoc_mul_le h2 hM) hy) (unitNormLoc_mul_le hT hx)
      rcases hle.lt_or_eq with hlt' | h'
      · exfalso
        have ey : (T ^ 2 - 4 * M) * y₀ = T * (2 * x₀ + T * y₀) + (-2) * (2 * M * y₀ + T * x₀) := by ring
        have ex : (T ^ 2 - 4 * M) * x₀ = T * (2 * M * y₀ + T * x₀) + (-2 * M) * (2 * x₀ + T * y₀) := by ring
        have hn2 : ‖(-2 : K)‖ ≤ 1 := by rw [norm_neg]; exact h2
        have hy1 : ‖y₀‖ < 1 := by
          have := unitNormLoc_add_lt (unitNormLoc_mul_lt hT hlt) (unitNormLoc_mul_lt hn2 hlt')
          rwa [← ey, norm_mul, hD, one_mul] at this
        have hx1 : ‖x₀‖ < 1 := by
          have := unitNormLoc_add_lt (unitNormLoc_mul_lt hT hlt')
            (unitNormLoc_mul_lt (unitNormLoc_mul_le hn2 hM) hlt)
          rwa [← ex, norm_mul, hD, one_mul] at this
        have hq : ‖x₀ ^ 2 + T * x₀ * y₀ + M * y₀ ^ 2‖ < 1 := by
          refine unitNormLoc_add_lt (unitNormLoc_add_lt ?_ ?_) ?_
          · rw [pow_two]; exact unitNormLoc_mul_lt hx hx1
          · exact unitNormLoc_mul_lt (unitNormLoc_mul_le hT hx) hy1
          · rw [pow_two, ← mul_assoc]; exact unitNormLoc_mul_lt (unitNormLoc_mul_le hM hy) hy1
        have : ‖ε‖ < 1 := by
          have e : ε = (x₀ ^ 2 + T * x₀ * y₀ + M * y₀ ^ 2) + -(x₀ ^ 2 + T * x₀ * y₀ + M * y₀ ^ 2 - ε) := by ring
          rw [e]; exact unitNormLoc_add_lt hq (by rw [norm_neg]; exact h0)
        rw [hε] at this; exact lt_irrefl _ this
      · exact h'
    have hf : ‖M * y₀ ^ 2 + T * x₀ * y₀ + (x₀ ^ 2 - ε)‖ < 1 := by
      have e : M * y₀ ^ 2 + T * x₀ * y₀ + (x₀ ^ 2 - ε) = x₀ ^ 2 + T * x₀ * y₀ + M * y₀ ^ 2 - ε := by ring
      rw [e]; exact h0
    obtain ⟨y, hy'⟩ := unitNormLoc_newton M (T * x₀) (x₀ ^ 2 - ε) y₀ hM (by rw [hgy, one_pow]; exact hf)
    obtain ⟨z, hz, hzn⟩ := near_root M (T * x₀) (x₀ ^ 2 - ε) y₀ y hgy hf hy'
    exact ⟨x₀, z, hx, norm_le_of_near hzn hy, by linear_combination hz⟩
  · have hf : ‖1 * x₀ ^ 2 + T * y₀ * x₀ + (M * y₀ ^ 2 - ε)‖ < 1 := by
      have e2 : 1 * x₀ ^ 2 + T * y₀ * x₀ + (M * y₀ ^ 2 - ε) = x₀ ^ 2 + T * x₀ * y₀ + M * y₀ ^ 2 - ε := by ring
      rw [e2]; exact h0
    have hg : ‖2 * 1 * x₀ + T * y₀‖ = 1 := by rw [mul_one]; exact heq
    obtain ⟨x, hx'⟩ := unitNormLoc_newton 1 (T * y₀) (M * y₀ ^ 2 - ε) x₀ (by rw [norm_one])
      (by rw [hg, one_pow]; exact hf)
    obtain ⟨z, hz, hzn⟩ := near_root 1 (T * y₀) (M * y₀ ^ 2 - ε) x₀ x hg hf hx'
    exact ⟨z, y₀, norm_le_of_near hzn hx, hy, by linear_combination hz⟩

end PI.OmLocU.Nrm
