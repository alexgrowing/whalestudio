import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal

namespace GlobalTheory.CompanionTheory.ShellSum

lemma shell_exponent_identity (q A : ℝ) (L m n : ℤ) (hq : 1 < q) :
    A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2) * q ^ (L - n)
      = A * q ^ L * q ^ ((m : ℝ) / 4) * q ^ (-(n : ℝ) / 4) := by
  have hq0 : 0 < q := by linarith
  have e1 : q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2) * q ^ (((L - n : ℤ)) : ℝ)
      = q ^ (L : ℝ) * q ^ ((m : ℝ) / 4) * q ^ (-(n : ℝ) / 4) := by
    rw [← Real.rpow_add hq0, ← Real.rpow_add hq0, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
    congr 1
    push_cast
    ring
  rw [Real.rpow_intCast, Real.rpow_intCast] at e1
  linear_combination A * e1

theorem lintegral_le_of_shells :
    ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (q A τ : ℝ) (L : ℤ) (c T₁ T₂ : ℝ≥0∞)
      (S : ℤ → ℤ → Set X) (Φ : X → ℝ≥0∞), 1 < q → 0 ≤ A → 0 < τ →
      (∀ m n, MeasurableSet (S m n)) →
      (∀ m n, n ≤ L → μ (S m n) ≤ ENNReal.ofReal (q ^ (L - n)) * c) →
      (∑' m : ℤ, (if m ≤ L then ENNReal.ofReal (q ^ ((m : ℝ) / 4)) else 0)) ≤ T₁ →
      (∑' n : ℤ, (if τ * q ^ (-n) ≤ q ^ L then ENNReal.ofReal (q ^ (-(n : ℝ) / 4)) else 0)) ≤ T₂ →
      (∀ y, Φ y ≠ 0 → ∃ m n : ℤ, m ≤ L ∧ n ≤ L ∧ τ * q ^ (-n) ≤ q ^ L ∧ y ∈ S m n ∧
        Φ y ≤ ENNReal.ofReal (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2))) →
      ∫⁻ y, Φ y ∂μ ≤ ENNReal.ofReal (A * q ^ L) * T₁ * T₂ * c := by
  intro X _ μ q A τ L c T₁ T₂ S Φ hq hA hτ hS hμ hT1 hT2 hΦ
  have hq0 : 0 < q := by linarith
  let a : ℤ → ℝ≥0∞ := fun m => if m ≤ L then ENNReal.ofReal (q ^ ((m : ℝ) / 4)) else 0
  let b : ℤ → ℝ≥0∞ := fun n =>
    if τ * q ^ (-n) ≤ q ^ L then ENNReal.ofReal (q ^ (-(n : ℝ) / 4)) else 0
  let w : ℤ × ℤ → ℝ≥0∞ := fun p =>
    if p.1 ≤ L ∧ p.2 ≤ L ∧ τ * q ^ (-p.2) ≤ q ^ L then
      ENNReal.ofReal (A * q ^ (((p.2 : ℝ) - p.1) / 4) * q ^ (((p.1 : ℝ) + p.2) / 2))
    else 0
  have hpt : ∀ y, Φ y ≤ ∑' p : ℤ × ℤ, (S p.1 p.2).indicator (fun _ => w p) y := by
    intro y
    by_cases h0 : Φ y = 0
    · simp [h0]
    obtain ⟨m, n, h1, h2, h3, h4, h5⟩ := hΦ y h0
    refine le_trans ?_ (ENNReal.le_tsum (m, n))
    have hw : w (m, n) = ENNReal.ofReal
        (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2)) := by
      simp only [w]
      rw [if_pos ⟨h1, h2, h3⟩]
    rw [Set.indicator_of_mem (show y ∈ S (m, n).1 (m, n).2 from h4), hw]
    exact h5
  have hterm : ∀ p : ℤ × ℤ,
      w p * μ (S p.1 p.2) ≤ ENNReal.ofReal (A * q ^ L) * (a p.1 * b p.2 * c) := by
    rintro ⟨m, n⟩
    by_cases hc : m ≤ L ∧ n ≤ L ∧ τ * q ^ (-n) ≤ q ^ L
    · obtain ⟨h1, h2, h3⟩ := hc
      have hw : w (m, n) = ENNReal.ofReal
          (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2)) := by
        simp only [w]
        rw [if_pos ⟨h1, h2, h3⟩]
      have ha : a m = ENNReal.ofReal (q ^ ((m : ℝ) / 4)) := by
        simp only [a]
        rw [if_pos h1]
      have hb : b n = ENNReal.ofReal (q ^ (-(n : ℝ) / 4)) := by
        simp only [b]
        rw [if_pos h3]
      have hnn1 : 0 ≤ A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2) := by positivity
      have hnn2 : 0 ≤ A * q ^ L := by positivity
      have hnn3 : 0 ≤ q ^ ((m : ℝ) / 4) := by positivity
      show w (m, n) * μ (S m n) ≤ ENNReal.ofReal (A * q ^ L) * (a m * b n * c)
      rw [hw, ha, hb]
      calc ENNReal.ofReal (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2)) * μ (S m n)
          ≤ ENNReal.ofReal (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2)) *
              (ENNReal.ofReal (q ^ (L - n)) * c) := by
            gcongr
            exact hμ m n h2
        _ = ENNReal.ofReal (A * q ^ (((n : ℝ) - m) / 4) * q ^ (((m : ℝ) + n) / 2) * q ^ (L - n))
              * c := by
            rw [ENNReal.ofReal_mul hnn1]
            ring
        _ = ENNReal.ofReal (A * q ^ L * q ^ ((m : ℝ) / 4) * q ^ (-(n : ℝ) / 4)) * c := by
            rw [shell_exponent_identity q A L m n hq]
        _ = ENNReal.ofReal (A * q ^ L) *
              (ENNReal.ofReal (q ^ ((m : ℝ) / 4)) * ENNReal.ofReal (q ^ (-(n : ℝ) / 4)) * c) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hnn2]
            ring
    · have hw : w (m, n) = 0 := by
        simp only [w]
        rw [if_neg hc]
      show w (m, n) * μ (S m n) ≤ _
      rw [hw, zero_mul]
      exact zero_le
  have hfac : ∑' p : ℤ × ℤ, a p.1 * b p.2 * c = (∑' m, a m) * (∑' n, b n) * c := by
    rw [ENNReal.tsum_prod (f := fun m n => a m * b n * c)]
    simp only [mul_assoc]
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  calc ∫⁻ y, Φ y ∂μ
      ≤ ∫⁻ y, ∑' p : ℤ × ℤ, (S p.1 p.2).indicator (fun _ => w p) y ∂μ := lintegral_mono hpt
    _ = ∑' p : ℤ × ℤ, ∫⁻ y, (S p.1 p.2).indicator (fun _ => w p) y ∂μ :=
        lintegral_tsum fun p => (measurable_const.indicator (hS p.1 p.2)).aemeasurable
    _ = ∑' p : ℤ × ℤ, w p * μ (S p.1 p.2) := by
        refine tsum_congr fun p => ?_
        exact lintegral_indicator_const (hS p.1 p.2) (w p)
    _ ≤ ∑' p : ℤ × ℤ, ENNReal.ofReal (A * q ^ L) * (a p.1 * b p.2 * c) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (A * q ^ L) * ((∑' m, a m) * (∑' n, b n) * c) := by
        rw [ENNReal.tsum_mul_left, hfac]
    _ ≤ ENNReal.ofReal (A * q ^ L) * (T₁ * T₂ * c) := by
        gcongr
    _ = ENNReal.ofReal (A * q ^ L) * T₁ * T₂ * c := by ring

end GlobalTheory.CompanionTheory.ShellSum
