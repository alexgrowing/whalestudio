import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.EtaAn.archimedeanBoundTotalConstant_size : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r q m Nc : ℕ) (L : ℝ), 2 ≤ L → 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E → 1 ≤ r → 1 ≤ m → m ≤ r → 1 ≤ q → 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E → Real.log (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E) ≤ 2 * L → Real.log (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E) ≤ 2 * L → Real.log r ≤ L → Real.log q ≤ 70 * L → Real.log Nc ≤ 41 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r * L) ^ 2 → 0 ≤ _root_.GlobalTheory.EtaAn.p16 E r q m 5 (max 1 Nc * 5 ^ (8 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r ^ 2)) ∧ _root_.GlobalTheory.EtaAn.p16 E r q m 5 (max 1 Nc * 5 ^ (8 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r ^ 2)) ≤ 200000 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r * L) ^ 2 := by
  intro E _ _ _ r q m Nc L hL hf hr hm hmr hq hrd hlrd hlf hlr hlq hlN
  unfold _root_.GlobalTheory.EtaAn.p16 _root_.GlobalTheory.EtaAn.p3 _root_.ReciprocityTheory.ChartRestriction.G.I2.dstar _root_.ReciprocityTheory.ChartRestriction.G.I2.RR
  push_cast
  set f := _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E with hfdef
  set D := _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E with hDdef
  have hF : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hMR : (m : ℝ) ≤ r := by exact_mod_cast hmr
  have hQ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlM : Real.log m ≤ L := (Real.log_le_log (by positivity) hMR).trans hlr
  have hlFnn : 0 ≤ Real.log f := Real.log_nonneg hF
  have hlRnn : 0 ≤ Real.log r := Real.log_nonneg hR
  have hlMnn : 0 ≤ Real.log m := Real.log_nonneg hM
  have hlQnn : 0 ≤ Real.log q := Real.log_nonneg hQ
  have hlDnn : 0 ≤ Real.log D := Real.log_nonneg hrd
  have heOne := Real.exp_one_gt_d9
  have heTwo : (7.3 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
  have hlTwo : Real.log 2 ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; linarith
  have hlFive : Real.log 5 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; linarith
  have hlSix : Real.log 6 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; linarith
  have hlSeven : Real.log 7 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; linarith
  have hlTenThousand : Real.log 10000 ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num), show (10 : ℝ) = 2 * 5 by norm_num, Real.exp_mul]
    have : (7.3 : ℝ) ^ 5 ≤ Real.exp 2 ^ 5 := pow_le_pow_left₀ (by norm_num) heTwo 5
    rw [← Real.rpow_natCast] at this
    norm_num at this ⊢
    linarith
  have hlTwoNonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlFiveNonneg : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)

  have hy : (1 : ℝ) ≤ f * r * q :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hF hR) hQ
  have hsqrt : 1 ≤ √((f : ℝ) * r * q) := Real.one_le_sqrt.mpr hy
  have hlogSqrt : Real.log (1 + 6 * √((f : ℝ) * r * q)) ≤ 2 + 37 * L := by
    calc Real.log (1 + 6 * √((f : ℝ) * r * q)) ≤ Real.log (7 * √((f : ℝ) * r * q)) :=
          Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 7 + (Real.log f + Real.log r + Real.log q) / 2 := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by positivity),
            Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
      _ ≤ 2 + 37 * L := by linarith
  have hlogSqrtNonneg : 0 ≤ Real.log (1 + 6 * √((f : ℝ) * r * q)) :=
    Real.log_nonneg (by have := Real.sqrt_nonneg ((f : ℝ) * r * q); linarith)

  have hg : Real.log (3 * (2 * (f : ℝ) * m)) = Real.log 6 + Real.log f + Real.log m := by
    rw [show 3 * (2 * (f : ℝ) * m) = 6 * f * m by ring, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  have hlogFact : Real.log (2 * (3 * (2 * (f : ℝ) * m)) ^ (2 * f * m)) =
      Real.log 2 + 2 * f * m * Real.log (3 * (2 * (f : ℝ) * m)) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  have hgUpper : Real.log (3 * (2 * (f : ℝ) * m)) ≤ 2 + 3 * L := by rw [hg]; linarith
  have hgNonneg : 0 ≤ Real.log (3 * (2 * (f : ℝ) * m)) := by rw [hg]; linarith [Real.log_nonneg (show (1:ℝ) ≤ 6 by norm_num)]

  have hmaxOne : (1 : ℝ) ≤ max 1 (Nc : ℝ) := le_max_left _ _
  have hlogBig : Real.log (max 1 (Nc : ℝ) * 5 ^ (8 * f * r ^ 2)) =
      Real.log (max 1 (Nc : ℝ)) + 8 * f * r ^ 2 * Real.log 5 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hXnn : 0 ≤ 41 * ((f : ℝ) * r * L) ^ 2 := by positivity
  have hlogMax : Real.log (max 1 (Nc : ℝ)) ≤ 41 * ((f : ℝ) * r * L) ^ 2 := by
    rcases le_total (Nc : ℝ) 1 with h | h
    · rw [max_eq_left h, Real.log_one]; exact hXnn
    · rw [max_eq_right h]; exact hlN
  have hlogMaxNonneg : 0 ≤ Real.log (max 1 (Nc : ℝ)) := Real.log_nonneg hmaxOne

  have hlogLast : Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2))
      ≤ 10 + 24 * L := by
    rw [show 5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2) =
        10000 * r * f ^ 3 * m ^ 3 * D ^ 7 by ring]
    have hD : (0 : ℝ) < D := by linarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    linarith
  have hlogLastNonneg : 0 ≤ Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2)) := by
    apply Real.log_nonneg
    rw [show 5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2) =
        10000 * r * f ^ 3 * m ^ 3 * D ^ 7 by ring]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) hR)
        (one_le_pow₀ hF)) (one_le_pow₀ hM)) (one_le_pow₀ hrd)
  rw [hlogFact, hlogBig]

  have hFL : 2 ≤ (f : ℝ) * L := le_trans hL (le_mul_of_one_le_left (by linarith) hF)
  have hFRsq : 4 * ((f : ℝ) * r ^ 2) ≤ ((f : ℝ) * r * L) ^ 2 := by
    have hFLsq : 4 ≤ (f : ℝ) * L ^ 2 := by
      calc (4 : ℝ) = 1 * (2 * 2) := by ring
        _ ≤ f * (L * L) := mul_le_mul hF (mul_le_mul hL hL (by norm_num) (by linarith))
            (by norm_num) (by positivity)
        _ = f * L ^ 2 := by ring
    calc 4 * ((f : ℝ) * r ^ 2) ≤ (f * L ^ 2) * ((f : ℝ) * r ^ 2) :=
          mul_le_mul_of_nonneg_right hFLsq (by positivity)
      _ = ((f : ℝ) * r * L) ^ 2 := by ring
  have hFRsqL : 2 * ((f : ℝ) * r ^ 2 * L) ≤ ((f : ℝ) * r * L) ^ 2 := by
    calc 2 * ((f : ℝ) * r ^ 2 * L) ≤ (f * L) * ((f : ℝ) * r ^ 2 * L) :=
          mul_le_mul_of_nonneg_right hFL (by positivity)
      _ = ((f : ℝ) * r * L) ^ 2 := by ring
  have hRle : (r : ℝ) ≤ f * r ^ 2 := by
    calc (r : ℝ) = 1 * 1 * r := by ring
      _ ≤ f * r * r := mul_le_mul (mul_le_mul hF hR zero_le_one (by positivity)) le_rfl
          (by positivity) (by positivity)
      _ = f * r ^ 2 := by ring
  have hprodSqrt : (r : ℝ) * (f * r * Real.log (1 + 6 * √((f : ℝ) * r * q))) ≤
      r * (f * r * (2 + 37 * L)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogSqrt (by positivity)) (by positivity)
  have hprodFact : (r : ℝ) * (2 * f * m * Real.log (3 * (2 * (f : ℝ) * m))) ≤ r * (2 * f * r * (2 + 3 * L)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc 2 * (f : ℝ) * m * Real.log (3 * (2 * (f : ℝ) * m)) ≤ 2 * f * m * (2 + 3 * L) :=
          mul_le_mul_of_nonneg_left hgUpper (by positivity)
      _ ≤ 2 * f * r * (2 + 3 * L) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMR (by positivity)) (by linarith)
  have hprodRFM : (r : ℝ) * (2 * f * m) ≤ 2 * (f * r ^ 2) := by
    have := mul_le_mul_of_nonneg_left hMR (by positivity : (0 : ℝ) ≤ 2 * f * r)
    linarith
  have hprodLast : (5 : ℝ) ^ 4 * r * (2 * f * m) / 2 *
      Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2)) ≤
      625 * (f * r ^ 2) * (10 + 24 * L) := by
    calc (5 : ℝ) ^ 4 * r * (2 * f * m) / 2 *
          Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2))
        ≤ (5 : ℝ) ^ 4 * r * (2 * f * m) / 2 * (10 + 24 * L) :=
          mul_le_mul_of_nonneg_left hlogLast (by positivity)
      _ ≤ 625 * (f * r ^ 2) * (10 + 24 * L) :=
          mul_le_mul_of_nonneg_right (by linarith [hprodRFM]) (by linarith)
  have hprodFiveA : 8 * (f : ℝ) * r ^ 2 * Real.log 5 ≤ 16 * (f * r ^ 2) := by
    have := mul_le_mul_of_nonneg_left hlFive (by positivity : (0 : ℝ) ≤ f * r ^ 2)
    linarith
  have hprodFiveB : 2 * (f : ℝ) * r ^ 2 * Real.log 5 ≤ 4 * (f * r ^ 2) := by
    have := mul_le_mul_of_nonneg_left hlFive (by positivity : (0 : ℝ) ≤ f * r ^ 2)
    linarith
  have hnnSqrt : 0 ≤ (r : ℝ) * (f * r * Real.log (1 + 6 * √((f : ℝ) * r * q))) := by positivity
  have hnnFact : 0 ≤ (r : ℝ) * (2 * f * m * Real.log (3 * (2 * (f : ℝ) * m))) := by positivity
  have hnnLast : 0 ≤ (5 : ℝ) ^ 4 * r * (2 * f * m) / 2 *
      Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2)) := by
    positivity
  have hnnFive : 0 ≤ (f : ℝ) * r ^ 2 * Real.log 5 := by positivity
  have hnnTwo : 0 ≤ (r : ℝ) * Real.log 2 := by positivity
  have hRlogTwo : (r : ℝ) * Real.log 2 ≤ r := mul_le_of_le_one_right (by positivity) hlTwo
  have hrfm_nonneg : 0 ≤ (r : ℝ) * (2 * f * m) := by positivity
  have hRnn : (0 : ℝ) ≤ r := by positivity
  constructor
  · linarith
  · linarith

end GlobalTheory.EtaAn
