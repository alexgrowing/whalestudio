import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
open scoped ComplexOrder

namespace GlobalTheory

theorem interp_weight_mul_rpow_le_inv (t r R κ c : ℝ) (hr : 1 ≤ r) (hrR : r ≤ Real.sqrt R)
    (hR : 1 ≤ R) (hc : 0 ≤ c) (hκ : 2 * c + 2 < κ) (ht : t ≤ (r / R) ^ κ) :
    t * r ^ c ≤ R⁻¹ := by
  have hR0 : 0 < R := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hκ0 : 0 ≤ κ := by linarith
  rw [Real.sqrt_eq_rpow] at hrR
  have h1 : r / R ≤ R ^ (-(1 / 2) : ℝ) := by
    rw [div_le_iff₀ hR0]
    have : R ^ (-(1 / 2) : ℝ) * R = R ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add_one hR0.ne']; norm_num
    rw [this]; exact hrR
  have h2 : (r / R) ^ κ ≤ R ^ (-(1 / 2) * κ) := by
    rw [Real.rpow_mul hR0.le]
    exact Real.rpow_le_rpow (div_nonneg hr0 hR0.le) h1 hκ0
  have h3 : r ^ c ≤ R ^ (1 / 2 * c) := by
    rw [Real.rpow_mul hR0.le]
    exact Real.rpow_le_rpow hr0 hrR hc
  calc t * r ^ c ≤ R ^ (-(1 / 2) * κ) * R ^ (1 / 2 * c) :=
        mul_le_mul (ht.trans h2) h3 (Real.rpow_nonneg hr0 _) (Real.rpow_nonneg hR0.le _)
    _ = R ^ (-(1 / 2) * κ + 1 / 2 * c) := (Real.rpow_add hR0 _ _).symm
    _ ≤ R ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR (by linarith)
    _ = R⁻¹ := Real.rpow_neg_one R

theorem interp_metric_close : ∀ (n : ℕ) (h h₀ : Matrix (Fin n) (Fin n) ℂ) (s r R κ c : ℝ), h.PosDef → h₀.PosSemidef → 1 ≤ r → r ≤ Real.sqrt R → 1 ≤ R → 0 ≤ c → 2 * c + 2 < κ → 0 ≤ 1 - s → 1 - s ≤ (r / R) ^ κ → (((r ^ c : ℝ) : ℂ) • h - h₀).PosSemidef → ((((1 + R⁻¹ : ℝ)) : ℂ) • h - (((s : ℝ) : ℂ) • h + (((1 - s : ℝ)) : ℂ) • h₀)).PosSemidef ∧ ((((s : ℝ) : ℂ) • h + (((1 - s : ℝ)) : ℂ) • h₀) - (((1 - R⁻¹ : ℝ)) : ℂ) • h).PosSemidef := by
  intro n h h₀ s r R κ c hh hh₀ hr hrR hR hc hκ hs ht hle
  have key := interp_weight_mul_rpow_le_inv (1 - s) r R κ c hr hrR hR hc hκ ht
  have h1 : 1 ≤ r ^ c := Real.one_le_rpow hr hc
  have key2 : 1 - s ≤ R⁻¹ := le_trans (le_mul_of_one_le_right hs h1) key
  have hs' : (0 : ℂ) ≤ ((1 - s : ℝ) : ℂ) := Complex.zero_le_real.mpr hs
  constructor
  · have e : (((1 + R⁻¹ : ℝ)) : ℂ) • h - (((s : ℝ) : ℂ) • h + (((1 - s : ℝ)) : ℂ) • h₀)
        = (((1 - s : ℝ)) : ℂ) • (((r ^ c : ℝ) : ℂ) • h - h₀)
          + ((R⁻¹ + (1 - s) - (1 - s) * r ^ c : ℝ) : ℂ) • h := by
      generalize r ^ c = a
      generalize R⁻¹ = b
      push_cast
      module
    rw [e]
    exact (hle.smul hs').add (hh.posSemidef.smul (Complex.zero_le_real.mpr (by linarith)))
  · have e : (((s : ℝ) : ℂ) • h + (((1 - s : ℝ)) : ℂ) • h₀) - (((1 - R⁻¹ : ℝ)) : ℂ) • h
        = (((1 - s : ℝ)) : ℂ) • h₀ + ((R⁻¹ - (1 - s) : ℝ) : ℂ) • h := by
      generalize R⁻¹ = b
      push_cast
      module
    rw [e]
    exact (hh₀.smul hs').add (hh.posSemidef.smul (Complex.zero_le_real.mpr (by linarith)))

end GlobalTheory
