import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.ThetaRunParameters

theorem exists_large_nat (B c₁ c₂ d C : ℝ) (hB : 0 < B) (hd : 0 ≤ d) :
    ∃ q : ℕ, 1 ≤ q ∧ c₁ < q ∧ c₂ ≤ (q : ℝ) / 2 ∧ 1 ≤ (q : ℝ) / B ∧
      4 * (7 + Real.log q) + d + 1 ≤ q * ((q : ℝ) / B) ∧ C ≤ q * ((q : ℝ) / B) := by
  obtain ⟨q, hq⟩ := exists_nat_gt (1 + |c₁| + 2 * |c₂| + B * (33 + d + |C|))
  have h1 := abs_nonneg c₁
  have h2 := abs_nonneg c₂
  have h3 := abs_nonneg C
  have h1' := le_abs_self c₁
  have h2' := le_abs_self c₂
  have h3' := le_abs_self C
  have h4 : 0 ≤ B * (33 + d + |C|) := by positivity
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hK : 33 + d + |C| ≤ (q : ℝ) / B := by
    rw [le_div_iff₀ hB]; linarith
  have hlog : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hm : (q : ℝ) * (33 + d + |C|) ≤ q * ((q : ℝ) / B) :=
    mul_le_mul_of_nonneg_left hK (by linarith)
  have hqd : d ≤ q * d := le_mul_of_one_le_left hd hq1
  have hqC : |C| ≤ q * |C| := le_mul_of_one_le_left h3 hq1
  refine ⟨q, by exact_mod_cast hq1, by linarith, by linarith, by linarith, ?_, ?_⟩
  · nlinarith
  · nlinarith

theorem exists_par : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r m : ℕ),
    2 ≤ PT.f E * r → 1 ≤ m → m ^ 4 ≤ PT.f E → (PT.f E : ℝ) ≤ PT.rd E →
    (PT.f E : ℝ) ^ 2 ≤ PT.rd E → 16 ≤ PT.rd E →
    ∃ (q : ℕ) (R0 : ℝ), 0 < th (E := E) q R0 ∧ ∀ X : PT E, X.r = r → (∃ τ, X.dim τ ≤ m) →
      ∃ P : Par X 1, P.q = q ∧ P.R0 = R0 ∧ P.m = m := by
  intro E _ _ _ r m hfr hm1 hmf hfrd hf2 hrd
  have hf : 0 < PT.f E := by
    rcases Nat.eq_zero_or_pos (PT.f E) with h | h
    · rw [h] at hfr; omega
    · exact h
  have hfR : (0 : ℝ) < PT.f E := by exact_mod_cast hf
  have hrd0 : 0 < PT.rd E := by linarith
  have hRR : 0 < RR (E := E) := by unfold RR; positivity
  set S : ℝ := 270 + 90 * (((PT.f E * r : ℕ) : ℝ) + 1) with hS
  have hS0 : 0 < S := by positivity
  have hsq : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS0.le
  have hB : 0 < Real.sqrt S ^ 2 * RR (E := E) ^ 4 := by rw [hsq]; positivity
  have hA : 0 < PT.f E * Real.sqrt S ^ 2 * RR (E := E) ^ 3 := by rw [hsq]; positivity
  obtain ⟨q, hq1, hc1, hc2, hb, h5, h6⟩ := exists_large_nat (Real.sqrt S ^ 2 * RR (E := E) ^ 4)
    ((dstar (E := E) m : ℝ) ^ 2 * omStar (E := E) * (PT.f E * Real.sqrt S ^ 2 * RR (E := E) ^ 3))
    (M1 (E := E) m) (dstar (E := E) m)
    (((PT.f E * r : ℕ) : ℝ) * Real.log 2 + 2 * dstar (E := E) m + 3 +
      (1 + 1) * (r * Real.log r + 3 * r + 3)) hB (Nat.cast_nonneg _)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  refine ⟨q, Real.sqrt S, Real.sqrt_pos.mpr (div_pos hA hq0), ?_⟩
  intro X hX hdim
  subst hX
  refine ⟨⟨q, Real.sqrt S, m, hq1, le_rfl, hfr, hdim, hm1, hmf, hfrd, hf2, hrd, ?_, ?_, hb, hc2,
    hq1, ?_, ?_⟩, rfl, rfl, rfl⟩
  · rw [hsq, hS]
    unfold PT.gA
    have : (0 : ℝ) ≤ ((PT.f E * X.r : ℕ) : ℝ) := Nat.cast_nonneg _
    constructor
    · linarith
    · rw [Nat.cast_one]; linarith
  · unfold th
    rw [Real.sq_sqrt (div_pos hA hq0).le, ← mul_div_assoc, div_lt_one hq0]
    exact hc1
  · unfold t0 b0
    rw [Nat.cast_one, mul_one, mul_one]
    exact h5
  · unfold t0 b0 PT.gA
    rw [Nat.cast_one]
    exact h6

end GlobalTheory.ThetaRunParameters
