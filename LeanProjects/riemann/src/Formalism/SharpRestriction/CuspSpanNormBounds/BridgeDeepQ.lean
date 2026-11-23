import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndDiamOfKnown
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.SGauge
import Formalism.FlagUnipotentLattices.HeightThresholdInequalities

noncomputable section

namespace Formalism.MainNotions.BridgeDeepQ

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates
open Formalism.HermitianLatticeCounting.S7 (P0 b1 beP)

def dqRh (X : CData) (t : ℝ) : ℝ :=
  (X.I.n : ℝ) ^ 2 * Real.sqrt (X.I.f : ℝ) * (X.g : ℝ) * X.I.rd * (2 * t) ^ ((1 : ℝ) / (X.qq : ℝ)) / 4

def sobT (X : CData) (t volK : ℝ) : ℝ :=
  (6 * beP X.I.n (P0 X.I.n X.qq X.I.f + X.I.n ^ 2 * X.I.f) X.b) ^ (X.I.n ^ 2 * X.I.f) * Real.exp (X.I.f : ℝ) *
    (17 * Real.sqrt (X.I.n : ℝ) / t ^ 2) ^ (2 * X.I.n ^ 2 * X.I.f) * X.Dc / volK

def KerDeep (X : CData) (S : CSize X) (volK : ℝ) : Prop :=
  ∀ᵐ x ∂X.μ, S.tau1 x < 1 / 2 →
    |(X.kerD x).re| ≤ sobT X (S.tau1 x) volK ∧
      (dqRh X (S.tau1 x) ≤ Real.log 2 →
        |(X.kerD x).re| ≤ (∏ P ∈ Finset.range (P0 X.I.n X.qq X.I.f),
          (2 * dqRh X (S.tau1 x) * Real.sqrt (X.I.f : ℝ) * beP X.I.n P X.b)) ^ 2 * sobT X (S.tau1 x) volK)

def VolRatioK (X : CData) (volK Cv : ℝ) : Prop :=
  0 < volK ∧ X.I.vol X.μf X.fund / volK ≤ cn_Y X ^ (Cv * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ))

def VolRatio (X : CData) (Cv : ℝ) : Prop := VolRatioK X (X.I.volKg X.μf X.g) Cv

def Comparison (X : CData) : Prop := 2 * Real.sqrt (X.I.n : ℝ) ≤ X.b ^ 2

theorem beP₂ {n : ℕ} {b : ℝ} (hn : 1 ≤ n) (hc : 2 * Real.sqrt (n : ℝ) ≤ b ^ 2) (P : ℕ) :
    beP n P b ≤ 3 * (n : ℝ) * (b ^ 2 + (P : ℝ) * n) := by
  unfold beP
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h32 : (n : ℝ) ^ ((3 : ℝ) / 2) = n * Real.sqrt n := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hn0, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [h32]
  set s := Real.sqrt (n : ℝ)
  have hs1 : 1 ≤ s := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hn1
  have hss : s * s = n := Real.mul_self_sqrt hn0.le
  have hsn : s ≤ n := by nlinarith
  have hP : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  have e1 : s * b ^ 2 ≤ n * b ^ 2 := mul_le_mul_of_nonneg_right hsn hb2
  have e2 : 3 / 2 * (n * s) ≤ 3 / 4 * (n * b ^ 2) := by nlinarith
  have hnn : (1 : ℝ) ≤ n * n := by nlinarith
  have e3 : 3 * (P : ℝ) ≤ 3 * (P * n * n) := by nlinarith [mul_le_mul_of_nonneg_left hnn hP]
  nlinarith

end Formalism.MainNotions.BridgeDeepQ

end
