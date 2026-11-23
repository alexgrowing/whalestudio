import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltAddEstimateLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesRadiusSizeLawsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesAddSubLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltFrobeniusIntegerPowerLawsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLawsStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem untiltFrobeniusLaurentSeries_zero (l : ℕ) [Fact l.Prime] (h j : ℕ) : lam h j (0 : Fl l) = 0 := by
  unfold lam
  have h0 : ∀ n : ℤ, (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) (0 : Fl l)) = 0 := by
    intro n
    rw [(GlobalTheory.T.tiltFrobeniusIntegerPower_laws l).2.2.1, (GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l).2.1, mul_zero]
  simp only [h0, tsum_zero]

theorem norm_add_three_le {l : ℕ} [Fact l.Prime] (a b c : ℂ_[l]) (C : ℝ)
    (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) (hc : ‖c‖ ≤ C) : ‖a + b + c‖ ≤ C := by
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hc)
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

theorem untiltFrobeniusLaurentSeries_nsmul_approx (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (x : Fl l)
    (hh : 1 ≤ h) (hr0 : 0 ≤ r) (hr1 : r < 1) (hx : ‖sh x‖ ≤ r) (m : ℕ) :
    ‖sh (m • x)‖ ≤ r ∧ ‖lam h j (m • x) - (m : ℂ_[l]) * lam h j x‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
  have hC : 0 ≤ ‖(l : ℂ_[l])‖ * gam l h j r :=
    mul_nonneg (norm_nonneg _) (GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws l h j r hh hr0 hr1).2.2.1
  induction m with
  | zero =>
    simp only [zero_smul, Nat.cast_zero, zero_mul, sub_zero, untiltFrobeniusLaurentSeries_zero, norm_zero, (GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l).2.1]
    exact ⟨hr0, hC⟩
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [succ_nsmul]
    obtain ⟨hadd, hsh⟩ := GlobalTheory.T.tiltUntilt_add_estimate_le l r (m • x) x ih1 hx
    refine ⟨hsh, ?_⟩
    have hl := GlobalTheory.T.untiltFrobeniusLaurentSeries_add_sub_le l h j r (m • x) x hh hr1 ih1 hx
    have heq : lam h j (m • x + x) - ((m + 1 : ℕ) : ℂ_[l]) * lam h j x =
        (lam h j (m • x + x) - lam h j (m • x) - lam h j x) + (lam h j (m • x) - (m : ℂ_[l]) * lam h j x) + 0 := by
      push_cast; ring
    rw [heq]
    exact norm_add_three_le _ _ _ _ hl ih2 (by simpa using hC)

theorem untiltFrobeniusLaurentSeries_finset_sum_approx (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) {ι : Type*} [DecidableEq ι]
    (x : ι → Fl l) (n : ι → ℕ)
    (hh : 1 ≤ h) (hr0 : 0 ≤ r) (hr1 : r < 1) (hx : ∀ a, ‖sh (x a)‖ ≤ r) (s : Finset ι) :
    ‖sh (∑ a ∈ s, n a • x a)‖ ≤ r ∧
      ‖lam h j (∑ a ∈ s, n a • x a) - ∑ a ∈ s, (n a : ℂ_[l]) * lam h j (x a)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
  have hC : 0 ≤ ‖(l : ℂ_[l])‖ * gam l h j r :=
    mul_nonneg (norm_nonneg _) (GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws l h j r hh hr0 hr1).2.2.1
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, untiltFrobeniusLaurentSeries_zero, sub_zero, norm_zero, (GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l).2.1]
    exact ⟨hr0, hC⟩
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    obtain ⟨hu1, hu2⟩ := untiltFrobeniusLaurentSeries_nsmul_approx l h j r (x a) hh hr0 hr1 (hx a) (n a)
    obtain ⟨hadd, hsh⟩ := GlobalTheory.T.tiltUntilt_add_estimate_le l r (n a • x a) (∑ b ∈ s, n b • x b) hu1 ih1
    refine ⟨hsh, ?_⟩
    have hl := GlobalTheory.T.untiltFrobeniusLaurentSeries_add_sub_le l h j r (n a • x a) (∑ b ∈ s, n b • x b) hh hr1 hu1 ih1
    have heq : lam h j (n a • x a + ∑ b ∈ s, n b • x b) -
        ((n a : ℂ_[l]) * lam h j (x a) + ∑ b ∈ s, (n b : ℂ_[l]) * lam h j (x b)) =
        (lam h j (n a • x a + ∑ b ∈ s, n b • x b) - lam h j (n a • x a) - lam h j (∑ b ∈ s, n b • x b)) +
        (lam h j (n a • x a) - (n a : ℂ_[l]) * lam h j (x a)) +
        (lam h j (∑ b ∈ s, n b • x b) - ∑ b ∈ s, (n b : ℂ_[l]) * lam h j (x b)) := by ring
    rw [heq]
    exact norm_add_three_le _ _ _ _ hl hu2 ih2

theorem lamsum : ∀ (l : ℕ) [Fact l.Prime] (h j d : ℕ) (r : ℝ) (x : Fin d → Fl l) (n : Fin d → ℕ), 1 ≤ h → 0 ≤ r → r < 1 → (∀ a, ‖sh (x a)‖ ≤ r) → ‖sh (∑ a, n a • x a)‖ ≤ r ∧ ‖lam h j (∑ a, n a • x a) - ∑ a, (n a : ℂ_[l]) * lam h j (x a)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
  intro l _ h j d r x n hh hr0 hr1 hx
  exact untiltFrobeniusLaurentSeries_finset_sum_approx l h j r x n hh hr0 hr1 hx Finset.univ

end GlobalTheory.PSer
