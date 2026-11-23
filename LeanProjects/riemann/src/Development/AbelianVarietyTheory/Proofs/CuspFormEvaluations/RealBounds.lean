import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RunParametersOfLower

theorem real_bounds (f r m ρ w D q t : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hm : 1 ≤ m) (hmf : m ≤ f)
    (hf2 : f ^ 2 ≤ ρ) (hρ : 16 ≤ ρ) (hw0 : 0 ≤ w) (hw : w ≤ f ^ 2) (hD : 1 ≤ D)
    (hq : (ρ ^ 7) ^ 4 * (90 * (f * r + D)) * D * r ≤ q)
    (ht : t = q * (q / (90 * (f * r + D) * (ρ ^ 7) ^ 4))) :
    (2 * f * m) ^ 2 * (2 * w * ρ) * (f * (90 * (f * r + D)) * (ρ ^ 7) ^ 3) < q ∧
    1 ≤ q / (90 * (f * r + D) * (ρ ^ 7) ^ 4) ∧
    90 * m ^ 2 * (2 * f * m) ^ 2 * ρ ≤ q / 2 ∧ D ≤ q ∧
    4 * D * (7 + Real.log (q * D)) + 2 * f * m + 1 ≤ t ∧
    f * r * Real.log 2 + 2 * (2 * f * m) + 3 + (D + 1) * (r * Real.log r + 3 * r + 3) ≤ t := by
  have hρ1 : (1 : ℝ) ≤ ρ := by linarith
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hN : r ≤ f * r := by nlinarith
  have hN1 : 1 ≤ f * r := by linarith
  have hfρ : f ≤ ρ := by nlinarith
  have hfm : f * m ≤ ρ := by nlinarith
  have hm2 : m ^ 2 ≤ ρ := by nlinarith
  have hd0 : 0 ≤ 2 * f * m := by positivity
  have hd : 2 * f * m ≤ 2 * ρ := by linarith
  have hwρ : w ≤ ρ := hw.trans hf2
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hlogr : Real.log r ≤ r := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < r by linarith); linarith
  have h3' : f * r * Real.log 2 ≤ f * r * 1 := by gcongr
  obtain ⟨N, hNdef⟩ : ∃ N, N = f * r := ⟨_, rfl⟩
  rw [← hNdef] at hq ht hN hN1 h3' ⊢
  obtain ⟨S, hS⟩ : ∃ S, S = 90 * (N + D) := ⟨_, rfl⟩
  rw [← hS] at hq ht ⊢
  have hS180 : 180 ≤ S := by linarith
  have hS0 : 0 < S := by linarith
  have hB : 0 < S * (ρ ^ 7) ^ 4 := by positivity
  have hDr : 1 ≤ D * r := one_le_mul_of_one_le_of_one_le hD hr
  have hDDr : D ≤ D * r := by nlinarith
  have hrDr : r ≤ D * r := by nlinarith
  have hq' : D * r * (S * (ρ ^ 7) ^ 4) ≤ q := by linarith
  have hBq : S * (ρ ^ 7) ^ 4 ≤ q := by
    have := mul_le_mul_of_nonneg_right hDr hB.le
    linarith
  have hq0 : 0 < q := by linarith
  have hb : D * r ≤ q / (S * (ρ ^ 7) ^ 4) := by rw [le_div_iff₀ hB]; exact hq'
  have htq : q * (D * r) ≤ t := by rw [ht]; gcongr
  have hT : ρ ^ 5 ≤ (ρ ^ 7) ^ 4 := by
    rw [← pow_mul]; exact pow_le_pow_right₀ hρ1 (by norm_num)
  have hT4 : 16 * ρ ^ 4 ≤ ρ ^ 5 := by
    rw [pow_succ' ρ 4]; gcongr
  have hT1 : ρ ≤ ρ ^ 4 := le_self_pow₀ hρ1 (by norm_num)
  have hqT : 180 * (ρ ^ 7) ^ 4 ≤ q := by
    have : 180 * (ρ ^ 7) ^ 4 ≤ S * (ρ ^ 7) ^ 4 := by gcongr
    linarith
  have hSρ : S * ρ ≤ q := by
    have : S * ρ ≤ S * (ρ ^ 7) ^ 4 := by
      have : ρ ≤ (ρ ^ 7) ^ 4 := by linarith
      gcongr
    linarith
  have hS16 : S * 16 ≤ S * ρ := by gcongr
  have hDq : D ≤ q := by linarith
  refine ⟨?_, by linarith, ?_, hDq, ?_, ?_⟩
  · have h1 : (2 * f * m) ^ 2 * (2 * w * ρ) * (f * S * (ρ ^ 7) ^ 3) ≤
        (2 * ρ) ^ 2 * (2 * ρ * ρ) * (ρ * S * (ρ ^ 7) ^ 3) := by
      gcongr
    have h2 : (2 * ρ) ^ 2 * (2 * ρ * ρ) * (ρ * S * (ρ ^ 7) ^ 3) = 8 * (S * ρ ^ 26) := by ring
    have h3 : S * (ρ ^ 7) ^ 4 = ρ ^ 2 * (S * ρ ^ 26) := by ring
    have h4 : 0 < S * ρ ^ 26 := by positivity
    have h5 : 8 * (S * ρ ^ 26) < ρ ^ 2 * (S * ρ ^ 26) :=
      mul_lt_mul_of_pos_right (by nlinarith) h4
    linarith
  · have h1 : 90 * m ^ 2 * (2 * f * m) ^ 2 * ρ ≤ 90 * ρ * (2 * ρ) ^ 2 * ρ := by gcongr
    have h2 : 90 * ρ * (2 * ρ) ^ 2 * ρ = 360 * ρ ^ 4 := by ring
    linarith
  · have h1 : Real.log q = Real.log (q / 16) + Real.log 16 := by
      rw [Real.log_div hq0.ne' (by norm_num)]; ring
    have h2 : Real.log (q / 16) ≤ q / 16 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : Real.log 16 ≤ 16 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h4 : Real.log D ≤ Real.log q := Real.log_le_log (by linarith) hDq
    have h5 : Real.log (q * D) = Real.log q + Real.log D := Real.log_mul hq0.ne' (by linarith)
    have h6 : 4 * D * (7 + Real.log (q * D)) ≤ 4 * D * (q / 8 + 37) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    have h7 : (2 * ρ + 1) * 1 ≤ (2 * ρ + 1) * D := by gcongr
    have h8 : (q / 2 + 148 + (2 * ρ + 1)) * D ≤ q * D := by
      apply mul_le_mul_of_nonneg_right _ (by linarith); linarith
    have h9 : q * D ≤ q * (D * r) := by gcongr
    linarith
  · have h2' : 0 ≤ Real.log r := Real.log_nonneg hr
    have h4 : r * Real.log r + 3 * r + 3 ≤ r * (N + 6) := by
      have : r * Real.log r ≤ r * N := by
        apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
      linarith
    have h5 : (D + 1) * (r * Real.log r + 3 * r + 3) ≤ (2 * D) * (r * (N + 6)) := by
      apply mul_le_mul (by linarith) h4 (by positivity) (by positivity)
    have h6 : (N + 4 * ρ + 3) * 1 ≤ (N + 4 * ρ + 3) * (D * r) := by gcongr
    have h7 : (N + 4 * ρ + 3 + 2 * (N + 6)) * (D * r) ≤ q * (D * r) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith); linarith
    linarith

theorem runOK_of_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r DF q m : ℕ), 1 ≤ DF → 2 ≤ I2.PT.f E * r → 1 ≤ m → m ^ 4 ≤ I2.PT.f E → (I2.PT.f E : ℝ) ^ 2 ≤ I2.PT.rd E → 16 ≤ I2.PT.rd E → I2.RR (E := E) ^ 4 * (90 * (I2.PT.f E * r + DF)) * DF * r ≤ q → RunOK E r DF q (Real.sqrt (90 * (I2.PT.f E * r + DF))) m := by
  intro E _ _ _ r DF q m hDF hfr hm1 hmf hf2 hrd hlo
  have hf : 1 ≤ I2.PT.f E := by
    rcases Nat.eq_zero_or_pos (I2.PT.f E) with h | h
    · rw [h] at hfr; omega
    · exact h
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h] at hfr; omega
    · exact h
  have hmf' : m ≤ I2.PT.f E := (Nat.le_self_pow (by norm_num) m).trans hmf
  have hfR : (1 : ℝ) ≤ I2.PT.f E := by exact_mod_cast hf
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hDR : (1 : ℝ) ≤ DF := by exact_mod_cast hDF
  have hmfR : (m : ℝ) ≤ I2.PT.f E := by exact_mod_cast hmf'
  have hfrR : (2 : ℝ) ≤ I2.PT.f E * r := by exact_mod_cast hfr
  have hfrd : (I2.PT.f E : ℝ) ≤ I2.PT.rd E := by nlinarith
  have hw : (I2.PT.f E : ℝ) ^ ((3 : ℝ) / 2) ≤ (I2.PT.f E : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hfR (by norm_num)
  have hS0 : (0 : ℝ) < 90 * (I2.PT.f E * r + DF) := by positivity
  have hsq : Real.sqrt (90 * (I2.PT.f E * r + DF)) ^ 2 = 90 * (I2.PT.f E * r + DF) := Real.sq_sqrt hS0.le
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := real_bounds (I2.PT.f E) r m (I2.PT.rd E) _ DF q
    (I2.t0 (E := E) q (Real.sqrt (90 * (I2.PT.f E * r + DF)))) hfR hrR hmR hmfR hf2 hrd
    (by positivity) hw hDR hlo (by unfold I2.t0 I2.b0 I2.RR; rw [hsq])
  have hc4 : DF ≤ q := by exact_mod_cast c4
  have hq1 : 1 ≤ q := hDF.trans hc4
  have hq0 : (0 : ℝ) < q := by linarith
  have hρ0 : 0 < I2.PT.rd E := by linarith
  have hd : (I2.dstar (E := E) m : ℝ) = 2 * I2.PT.f E * m := by unfold I2.dstar; push_cast; ring
  intro X hX hdim
  subst hX
  refine ⟨⟨q, _, m, hq1, hDF, hfr, hdim, hm1, hmf, hfrd, hf2, hrd, ?_, ?_, ?_, ?_,
    hc4, ?_, ?_⟩, rfl, rfl, rfl⟩
  · rw [hsq]
    unfold I2.PT.gA
    push_cast
    constructor <;> linarith
  · unfold I2.th I2.omStar I2.RR
    rw [Real.sq_sqrt (by positivity), ← mul_div_assoc, div_lt_one hq0, hsq, hd]
    exact c1
  · unfold I2.b0 I2.RR; rw [hsq]; exact c2
  · unfold I2.M1
    rw [hd]; exact c3
  · rw [hd]; linarith
  · unfold I2.PT.gA
    rw [hd]
    push_cast
    linarith

end GlobalTheory.RunParametersOfLower
