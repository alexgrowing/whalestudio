import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersRoundedSizeBoundWindowStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxNonThickSizeShiftedValueAndBoundsStatement

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem mul_small_le_bHat {D : D7} (L : SizeData₂ D) (C C' : ℝ) (j : ℕ) (hR : Roomy L C') (hC : 0 ≤ C)
    (hCC : 2 * C ≤ C') (hj : 2 * j + 2 ≤ D.host.Lw) :
    C * ((j : ℝ) + 1) * (((wHat D + sHat L + etaHat L : ℕ) : ℝ) + 1) ≤ (bHat L : ℝ) := by
  have hlow := (GlobalTheory.T.roundedSizeBound_window L C' hR).1
  obtain ⟨-, hw2, hG⟩ := GlobalTheory.T.maxNonThickSizeShifted_value_and_bounds L C' hR
  obtain ⟨h100, -, -, -, -, hbig⟩ := hR
  have hw0 : (0 : ℝ) ≤ (wHat D : ℝ) := Nat.cast_nonneg _
  have heta := L.etaSz_pos
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hhalf : ((D.R.t : ℝ) + 1) / 2 ≤ L.sc.b' := by linarith
  have hb0 : 0 ≤ L.sc.b' := by linarith
  have hjN : (j + 1) * 2 ≤ D.host.Lw := by omega
  have hjL : ((j : ℝ) + 1) * 2 ≤ (D.host.Lw : ℝ) := by exact_mod_cast hjN
  have hj0 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  push_cast
  have s1 : C * ((j : ℝ) + 1) * ((wHat D : ℝ) + sHat L + etaHat L + 1)
      ≤ C * ((j : ℝ) + 1) * (2 * L.sc.b') :=
    mul_le_mul_of_nonneg_left hG (mul_nonneg hC hj0)
  have s2 : C * ((j : ℝ) + 1) * (2 * L.sc.b') ≤ C' * ((j : ℝ) + 1) * L.sc.b' := by
    have := mul_le_mul_of_nonneg_right hCC (mul_nonneg hj0 hb0)
    nlinarith
  have s3 : C' * ((j : ℝ) + 1) * L.sc.b' + L.sc.b' ≤ C' * ((D.host.Lw : ℝ) + 1) * L.sc.b' := by
    have hk : C' * ((j : ℝ) + 1) + 1 ≤ C' * ((D.host.Lw : ℝ) + 1) := by nlinarith
    nlinarith
  linarith

end GlobalTheory.HTW
