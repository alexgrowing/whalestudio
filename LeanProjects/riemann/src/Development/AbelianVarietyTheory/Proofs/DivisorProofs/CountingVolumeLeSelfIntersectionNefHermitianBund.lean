import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory

open Filter Topology

theorem countVol_le_selfInter : ∀ (k : Type) [CommRing k] (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp k) (D d a : ℕ) (L : GlobalTheory.HermLB p) (A : ℝ) (m : ℕ → ℕ∞), GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.IsArithVar p D → L.IsNef D → L.IsSelfInter A → 0 < d → 0 < a → (∀ i : ℕ, 1 ≤ i → m (a * i) ≤ (L.pow (a * i)).smallSec.encard) → countVol D d a m ≤ ENNReal.ofReal (A / ((d : ℝ) * ((D : ℝ) + 1))) := by
  intro k _ X _ p D d a L A m hAHS hX hL hA hd ha hm
  have hmul : Tendsto (fun j : ℕ => a * j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left j ha) tendsto_id
  have h1 := ((hAHS.tendsto_of_triv hX hL hA).comp hmul).div_const ((d : ℝ) * ((D : ℝ) + 1))
  have h2 := ENNReal.tendsto_ofReal h1
  refine (limsup_le_limsup ?_).trans_eq h2.limsup_eq
  filter_upwards [hmul.eventually (hAHS.of_triv hX hL hA).1, eventually_ge_atTop 1] with j hfin hj
  have hx : 0 ≤ Real.log (((L.pow (a * j)).smallSec.ncard : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hN : (0 : ℝ) < ((a * j : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.mul_pos ha hj)
  have hd' : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.2 hd
  have hlog : logCard (m (a * j)) ≤ ENNReal.ofReal (Real.log (((L.pow (a * j)).smallSec.ncard : ℕ) : ℝ)) := by
    rw [← logCard_coe, hfin.cast_ncard_eq]
    exact EReal.toENNReal_le_toENNReal (ENNReal.log_monotone (ENat.toENNReal_le.2 (hm j hj)))
  have hden : (d : ℝ≥0∞) * ((a * j : ℕ) : ℝ≥0∞) ^ (D + 1) =
      ENNReal.ofReal ((d : ℝ) * ((a * j : ℕ) : ℝ) ^ (D + 1)) := by
    rw [ENNReal.ofReal_mul hd'.le, ENNReal.ofReal_pow hN.le, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  calc _ ≤ (D.factorial : ℝ≥0∞) * ENNReal.ofReal (Real.log (((L.pow (a * j)).smallSec.ncard : ℕ) : ℝ)) /
        ((d : ℝ≥0∞) * ((a * j : ℕ) : ℝ≥0∞) ^ (D + 1)) := by gcongr
    _ = _ := by
      rw [hden, ← ENNReal.ofReal_natCast (D.factorial), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_div_of_pos (by positivity)]
      simp only [Function.comp]
      congr 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp

end GlobalTheory
