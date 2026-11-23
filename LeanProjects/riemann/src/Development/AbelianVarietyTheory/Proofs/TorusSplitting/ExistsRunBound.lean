import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RunParametersBound

theorem real_bounds (f r m ρ w q : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hm : 1 ≤ m) (hmf : m ≤ f)
    (hf2 : f ^ 2 ≤ ρ) (hρ : 16 ≤ ρ) (hw0 : 0 ≤ w) (hw : w ≤ f ^ 2)
    (hq : 135 * (f * r) * (ρ ^ 7) ^ 4 * (r + 1) ≤ q) :
    (2 * f * m) ^ 2 * (2 * w * ρ) * (f * (135 * (f * r)) * (ρ ^ 7) ^ 3) < q ∧
    2 ≤ q / (135 * (f * r) * (ρ ^ 7) ^ 4) ∧
    90 * m ^ 2 * (2 * f * m) ^ 2 * ρ ≤ q / 2 ∧
    4 * (7 + Real.log q) + 2 * f * m + 1 ≤ q * 2 ∧
    f * r * Real.log 2 + 2 * (2 * f * m) + 3 + (1 + 1) * (r * Real.log r + 3 * r + 3) ≤ q := by
  have hρ1 : (1 : ℝ) ≤ ρ := by linarith
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hN : r ≤ f * r := by nlinarith
  have hN1 : 1 ≤ f * r := by linarith
  have hfρ : f ≤ ρ := by nlinarith
  have hfm : f * m ≤ ρ := by nlinarith
  have hm2 : m ^ 2 ≤ ρ := by nlinarith
  have hd0 : 0 ≤ 2 * f * m := by positivity
  have hd : 2 * f * m ≤ 2 * ρ := by linarith
  have hd2 : (2 * f * m) ^ 2 ≤ (2 * ρ) ^ 2 := by gcongr
  have hB : 0 < 135 * (f * r) * (ρ ^ 7) ^ 4 := by positivity
  have h2B : 135 * (f * r) * (ρ ^ 7) ^ 4 * 2 ≤ q :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith) hB.le) hq
  have hT : ρ ^ 5 ≤ (ρ ^ 7) ^ 4 := by
    rw [← pow_mul]; exact pow_le_pow_right₀ hρ1 (by norm_num)
  have hT4 : 16 * ρ ^ 4 ≤ ρ ^ 5 := by
    rw [pow_succ' ρ 4]; gcongr
  have hT1 : ρ ≤ ρ ^ 4 := le_self_pow₀ hρ1 (by norm_num)
  have hqT : 270 * (ρ ^ 7) ^ 4 ≤ q := by
    have : 135 * 1 * (ρ ^ 7) ^ 4 * 2 ≤ 135 * (f * r) * (ρ ^ 7) ^ 4 * 2 := by gcongr
    linarith
  have hq0 : 0 < q := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h1 : (2 * f * m) ^ 2 * (2 * w * ρ) * (f * (135 * (f * r)) * (ρ ^ 7) ^ 3) ≤
        (2 * ρ) ^ 2 * (2 * ρ * ρ) * (ρ * (135 * (f * r)) * (ρ ^ 7) ^ 3) := by
      have hwρ : w ≤ ρ := hw.trans hf2
      gcongr
    have h2 : (2 * ρ) ^ 2 * (2 * ρ * ρ) * (ρ * (135 * (f * r)) * (ρ ^ 7) ^ 3) =
        8 * (135 * (f * r) * ρ ^ 26) := by ring
    have h3 : 135 * (f * r) * (ρ ^ 7) ^ 4 = ρ ^ 2 * (135 * (f * r) * ρ ^ 26) := by ring
    have h4 : 0 < 135 * (f * r) * ρ ^ 26 := by positivity
    have h5 : 8 * (135 * (f * r) * ρ ^ 26) ≤ ρ ^ 2 * (135 * (f * r) * ρ ^ 26) :=
      mul_le_mul_of_nonneg_right (by nlinarith) h4.le
    linarith
  · rw [le_div_iff₀ hB]; linarith
  · have h1 : 90 * m ^ 2 * (2 * f * m) ^ 2 * ρ ≤ 90 * ρ * (2 * ρ) ^ 2 * ρ := by gcongr
    have h2 : 90 * ρ * (2 * ρ) ^ 2 * ρ = 360 * ρ ^ 4 := by ring
    linarith
  · have h1 : Real.log q = Real.log (q / 4) + Real.log 4 := by
      rw [Real.log_div hq0.ne' (by norm_num)]; ring
    have h2 : Real.log (q / 4) ≤ q / 4 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : Real.log 4 ≤ 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  · have h1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have h2 : Real.log r ≤ r := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < r by linarith); linarith
    have h3 : f * r * Real.log 2 ≤ f * r * 1 := by gcongr
    have h2' : 0 ≤ Real.log r := Real.log_nonneg hr
    have h4 : r * Real.log r ≤ (f * r) * r := by gcongr
    have h5 : 135 * (f * r) * ρ * (r + 1) ≤ 135 * (f * r) * (ρ ^ 7) ^ 4 * (r + 1) := by
      have : ρ ≤ (ρ ^ 7) ^ 4 := by linarith
      gcongr
    have h6 : (f * r) * 1 * r ≤ (f * r) * ρ * r := by gcongr
    have h7 : 1 * ρ ≤ (f * r) * ρ := by gcongr
    have h8 : (f * r) * 16 ≤ (f * r) * ρ := by gcongr
    have h9 : 0 ≤ (f * r) * r := by positivity
    nlinarith

theorem exists_run_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r m : ℕ), 2 ≤ I2.PT.f E * r → 1 ≤ m → m ^ 4 ≤ I2.PT.f E → (I2.PT.f E : ℝ) ^ 2 ≤ I2.PT.rd E → 16 ≤ I2.PT.rd E → ∃ (q : ℕ) (R0 : ℝ), 1 ≤ q ∧ Real.log q ≤ 28 * Real.log (I2.PT.rd E) + 2 * Real.log (I2.PT.f E * r) + 7 ∧ RunOK E r 1 q R0 m := by
  intro E _ _ _ r m hfr hm1 hmf hf2 hrd
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
  have hmfR : (m : ℝ) ≤ I2.PT.f E := by exact_mod_cast hmf'
  have hfrR : (2 : ℝ) ≤ I2.PT.f E * r := by exact_mod_cast hfr
  have hfrd : (I2.PT.f E : ℝ) ≤ I2.PT.rd E := by nlinarith
  have hw : (I2.PT.f E : ℝ) ^ ((3 : ℝ) / 2) ≤ (I2.PT.f E : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hfR (by norm_num)
  have hρ0 : 0 < I2.PT.rd E := by linarith
  set S : ℝ := 135 * ((I2.PT.f E : ℝ) * r) with hS
  have hS0 : 0 < S := by positivity
  have hsq : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS0.le
  set B : ℝ := S * (I2.PT.rd E ^ 7) ^ 4 with hB
  have hB1 : 1 ≤ B := by
    have h1 : (1 : ℝ) ≤ (I2.PT.rd E ^ 7) ^ 4 := one_le_pow₀ (one_le_pow₀ (by linarith))
    have h2 : (1 : ℝ) ≤ S := by linarith
    exact one_le_mul_of_one_le_of_one_le h2 h1
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = ⌈B⌉₊ * (r + 1) := ⟨_, rfl⟩
  have hqR : (q : ℝ) = (⌈B⌉₊ : ℝ) * (r + 1) := by rw [hq]; push_cast; ring
  have hlo : B * (r + 1) ≤ q := by
    rw [hqR]; gcongr; exact Nat.le_ceil B
  have hqR1 : (1 : ℝ) ≤ q := by nlinarith
  have hq1 : 1 ≤ q := by exact_mod_cast hqR1
  have hq0 : (0 : ℝ) < q := by linarith
  have hhi : (q : ℝ) ≤ I2.PT.rd E ^ 28 * ((I2.PT.f E : ℝ) * r) ^ 2 * 540 := by
    have h1 : (⌈B⌉₊ : ℝ) ≤ 2 * B := by
      have := Nat.ceil_lt_add_one (show 0 ≤ B by linarith); linarith
    have h2 : (r : ℝ) + 1 ≤ 2 * ((I2.PT.f E : ℝ) * r) := by nlinarith
    calc (q : ℝ) = (⌈B⌉₊ : ℝ) * (r + 1) := hqR
      _ ≤ (2 * B) * (2 * ((I2.PT.f E : ℝ) * r)) := by gcongr
      _ = _ := by rw [hB, hS]; ring
  obtain ⟨c1, c2, c3, c5, c6⟩ := real_bounds (I2.PT.f E) r m (I2.PT.rd E) _ q hfR hrR hmR hmfR hf2 hrd
    (by positivity) hw hlo
  have hb0 : 2 ≤ I2.b0 (E := E) q (Real.sqrt S) := by
    unfold I2.b0 I2.RR; rw [hsq]; exact c2
  have ht0 : (q : ℝ) * 2 ≤ I2.t0 (E := E) q (Real.sqrt S) := by
    unfold I2.t0; gcongr
  have hd : (I2.dstar (E := E) m : ℝ) = 2 * I2.PT.f E * m := by unfold I2.dstar; push_cast; ring
  refine ⟨q, Real.sqrt S, hq1, ?_, ?_⟩
  · have h7 : Real.log 540 ≤ 7 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h1 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
      have h2 : (2.7 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
      have h3 : (2.7 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := by gcongr
      rw [h1]; exact le_trans (by norm_num) h3
    have h1 := Real.log_le_log hq0 hhi
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    linarith
  · intro X hX hdim
    subst hX
    refine ⟨⟨q, Real.sqrt S, m, hq1, le_rfl, hfr, hdim, hm1, hmf, hfrd, hf2, hrd, ?_, ?_, by linarith, ?_,
      hq1, ?_, ?_⟩, rfl, rfl, rfl⟩
    · rw [hsq, hS]
      unfold I2.PT.gA
      push_cast
      constructor <;> linarith
    · unfold I2.th I2.omStar I2.RR
      rw [Real.sq_sqrt (by positivity), ← mul_div_assoc, div_lt_one hq0, hsq, hd]
      exact c1
    · unfold I2.M1
      rw [hd]; exact c3
    · rw [Nat.cast_one, _root_.mul_one, _root_.mul_one, hd]
      linarith
    · unfold I2.PT.gA
      rw [Nat.cast_one, hd]
      push_cast
      linarith

end GlobalTheory.RunParametersBound
