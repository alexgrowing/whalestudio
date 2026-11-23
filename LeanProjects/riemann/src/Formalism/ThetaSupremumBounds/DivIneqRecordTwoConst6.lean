import Formalism.ThetaSupremumBounds.LiftOperatorBoundOfFockJet
import Formalism.ThetaSupremumBounds.FinalJ
import Formalism.ThetaSupremumBounds.GaussianShiftBounds.GlobalBoundRefinements

open Finset
open scoped Real

namespace Formalism.DimensionVariation

open Formalism.LatticeIndexTer (ph)

theorem stepDi6 : StepDi6 := first_descent_explicit
theorem perEmbedding6 : PerEmbedding6 := per_embedding_explicit
theorem heightBound6 : HeightBound6 := heightBound6_statement
theorem heightRecord6 : HeightRecord6 := height_bound_complete
theorem divIneqExplicit6 : DivIneqExplicit6 := division_inequality_explicit
theorem divIneqTwoConst6 : DivIneqTwoConst6 := division_inequality_two_constants
theorem divIneqFine6 : DivIneqFine6 := division_inequality_fine
theorem divIneqRecord6 : DivIneqRecord6 := division_inequality_complete
theorem stepDiProd6 : StepDiProd6 := first_descent_product_explicit
theorem liftStepDi6 : LiftStepDi6 := lift_first_descent
theorem topNet6 : TopNet6 := top_net
theorem flatLineDegree6 : FlatLineDegree6 := flat_line_degree
theorem meanDev6 : MeanDev6 := mean_deviation
theorem weightSize6 : WeightSize6 := weight_size

theorem divIneqRecordFree6
    (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ)
    (muC mu0 Fo logT : ℝ) (aT : Pl → ℝ) (logH : J → Pl → ℝ)
    (x eps L b a rd La L' B0 m f k N nV S tt η w'' b' lam0 C C0 : ℝ)
    (Lpass Eb logOm : ℝ) (pq : J → ℝ) (w eE δ : J → Pl → ℝ)
    (q1 : muC ≤ mu0 + Lpass)
    (q2 : mu0 ≤ (∑ j, ∑ ρ, pq j * w j ρ * logOm) + 2 * Fo + Eb)
    (q6 : ∀ j ρ, (∑ i, ph (ν j ρ i)) - logH j ρ ≤ (if ρ ∈ TT then ph (aT ρ) else 0) + eE j ρ)
    (q7 : ∀ j ρ, (∑ i, ν j ρ i) = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ)
    (z1 : 1 ≤ x) (z2 : 0 < eps) (z3 : L = x ^ eps) (z4 : b = Real.exp L) (z5 : a = x * b)
    (z6 : 1 ≤ rd) (z7 : Real.log rd ≤ L) (z8 : Real.log x ≤ L) (z9 : La = Real.log (a * rd))
    (z10 : B0 = f * m * b * x ^ eps)
    (z13 : (Fintype.card J : ℝ) = m) (z14 : (Fintype.card Pl : ℝ) ≤ f) (z15 : 1 ≤ m) (z16 : 1 ≤ f)
    (z17 : 1 ≤ k) (z18 : 1 ≤ N) (z19 : 0 ≤ S) (z20 : 0 ≤ tt) (z21 : 0 ≤ η) (zb : 0 ≤ b')
    (z23 : ∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b)
    (z24 : ∀ j, |pq j - k| ≤ m) (z25 : |logOm| ≤ La)
    (z26 : lam0 ≤ b) (z27 : N ^ 2 ≤ b) (z28 : m ^ 3 * N ^ 2 * L ≤ b) (z29 : m * η * N * L ≤ b)
    (z30 : k * N ≤ b) (z31 : k * S ≤ w'') (z32 : m * (tt + 1) * η ≤ w'') (z33 : N * w'' ≤ b)
    (z34 : b' * N ≤ a) (z35 : m * k * b' ≤ a)
    (hC : 0 ≤ C) (hCC : C ≤ C0) (hnV : 0 ≤ nV) (hnVN : nV ≤ N) (hL' : 0 ≤ L') (hCL : C * L' ≤ C0 * La)
    (y1 : Lpass ≤ 1 + C0 * lam0)
    (y5 : ∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La)
    (y6 : ∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))) :
    muC + recordHu TT ν aT logH logT logOm f m N S η b' nV L La L' C - 2 * Fo ≤
      (∑ t ∈ TT, (m * (ph (aT t) - aT t * logOm) - aT t * logT)) +
      (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * B0 * x ^ eps) + Eb := by
  have key := division_inequality_complete J Pl TT r ν (muC - Eb) (mu0 - Eb) Fo logT aT logH x eps L b a
    rd La L' B0 0 (x ^ eps) m f k N nV S tt η w'' b' lam0 C C0 Lpass 0 logOm pq w eE δ
    (by linarith) (by linarith) q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 le_rfl le_rfl
    z13 z14 z15 z16 z17 z18 z19 z20 z21 zb
    z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35 hC hCC hnV hnVN hL' hCL y1 ?_ y5 y6
  · rw [add_zero] at key
    linarith
  · have hxe : 0 ≤ x ^ eps := Real.rpow_nonneg (by linarith) _
    have hb : 0 ≤ b := by rw [z4]; exact (Real.exp_pos _).le
    have hB0 : 0 ≤ B0 := by rw [z10]; positivity
    have hC0 : 0 ≤ C0 := le_trans hC hCC
    positivity

theorem divIneqRecordTwoConst6
    (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ)
    (muC mu0 Fo logT : ℝ) (aT : Pl → ℝ) (logH : J → Pl → ℝ)
    (x eps L b a rd La L' B0 Nc c m f k N nV S tt η w'' b' lam0 C C0 : ℝ)
    (Lpass Eb logOm : ℝ) (pq : J → ℝ) (w eE δ : J → Pl → ℝ)
    (q1 : muC ≤ mu0 + Lpass)
    (q2 : mu0 ≤ (∑ j, ∑ ρ, pq j * w j ρ * logOm) + 2 * Fo + Eb)
    (q6 : ∀ j ρ, (∑ i, ph (ν j ρ i)) - logH j ρ ≤ (if ρ ∈ TT then ph (aT ρ) else 0) + eE j ρ)
    (q7 : ∀ j ρ, (∑ i, ν j ρ i) = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ)
    (z1 : 1 ≤ x) (z2 : 0 < eps) (z3 : L = x ^ eps) (z4 : b = Real.exp L) (z5 : a = x * b)
    (z6 : 1 ≤ rd) (z7 : Real.log rd ≤ L) (z8 : Real.log x ≤ L) (z9 : La = Real.log (a * rd))
    (z10 : B0 = f * m * b * x ^ eps)
    (z13 : (Fintype.card J : ℝ) = m) (z14 : (Fintype.card Pl : ℝ) ≤ f) (z15 : 1 ≤ m) (z16 : 1 ≤ f)
    (z17 : 1 ≤ k) (z18 : 1 ≤ N) (z19 : 0 ≤ S) (z20 : 0 ≤ tt) (z21 : 0 ≤ η) (zb : 0 ≤ b')
    (z23 : ∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b)
    (z24 : ∀ j, |pq j - k| ≤ m) (z25 : |logOm| ≤ La)
    (z26 : lam0 ≤ b) (z27 : N ^ 2 ≤ b) (z28 : m ^ 3 * N ^ 2 * L ≤ b) (z29 : m * η * N * L ≤ b)
    (z30 : k * N ≤ b) (z31 : k * S ≤ w'') (z32 : m * (tt + 1) * η ≤ w'') (z33 : N * w'' ≤ b)
    (z34 : b' * N ≤ a) (z35 : m * k * b' ≤ a)
    (hC : 0 ≤ C) (hCC : C ≤ C0) (hnV : 0 ≤ nV) (hnVN : nV ≤ N) (hL' : 0 ≤ L') (hCL : C * L' ≤ C0 * La)
    (y1 : Lpass ≤ 1 + C0 * lam0)
    (y5 : ∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La)
    (y6 : ∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0)))
    (z11 : 0 ≤ Nc) (y2 : Eb ≤ c * m * x ^ eps * (B0 + Nc)) :
    muC + recordHu TT ν aT logH logT logOm f m N S η b' nV L La L' C - 2 * Fo ≤
      (∑ t ∈ TT, (m * (ph (aT t) - aT t * logOm) - aT t * logT)) +
      (50 * C0 + 10) * ((TT.card : ℝ) * a * La) + (50 * C0 + 10 + c) * (m * (B0 + Nc) * x ^ eps) := by
  have key := divIneqRecordFree6 J Pl TT r ν muC mu0 Fo logT aT logH x eps L b a rd La L' B0 m f k N nV
    S tt η w'' b' lam0 C C0 Lpass Eb logOm pq w eE δ q1 q2 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z13 z14 z15 z16 z17 z18
    z19 z20 z21 zb z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35 hC hCC hnV hnVN hL' hCL y1 y5 y6
  have hxe : 0 ≤ x ^ eps := Real.rpow_nonneg (by linarith) _
  have hC0 : 0 ≤ C0 := le_trans hC hCC
  have h1 : 0 ≤ (50 * C0 + 10) * (m * Nc * x ^ eps) := by positivity
  nlinarith

theorem divIneqRecordFine6
    (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ)
    (muC mu0 Fo logT : ℝ) (aT : Pl → ℝ) (logH : J → Pl → ℝ)
    (x eps L b a rd La L' B0 Nc c m f k N nV S tt η w'' b' lam0 C C0 : ℝ)
    (Lpass Eb logOm : ℝ) (pq : J → ℝ) (w eE δ : J → Pl → ℝ)
    (q1 : muC ≤ mu0 + Lpass)
    (q2 : mu0 ≤ (∑ j, ∑ ρ, pq j * w j ρ * logOm) + 2 * Fo + Eb)
    (q6 : ∀ j ρ, (∑ i, ph (ν j ρ i)) - logH j ρ ≤ (if ρ ∈ TT then ph (aT ρ) else 0) + eE j ρ)
    (q7 : ∀ j ρ, (∑ i, ν j ρ i) = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ)
    (z1 : 1 ≤ x) (z2 : 0 < eps) (z3 : L = x ^ eps) (z4 : b = Real.exp L) (z5 : a = x * b)
    (z6 : 1 ≤ rd) (z7 : Real.log rd ≤ L) (z8 : Real.log x ≤ L) (z9 : La = Real.log (a * rd))
    (z10 : B0 = f * m * b * x ^ eps)
    (z13 : (Fintype.card J : ℝ) = m) (z14 : (Fintype.card Pl : ℝ) ≤ f) (z15 : 1 ≤ m) (z16 : 1 ≤ f)
    (z17 : 1 ≤ k) (z18 : 1 ≤ N) (z19 : 0 ≤ S) (z20 : 0 ≤ tt) (z21 : 0 ≤ η) (zb : 0 ≤ b')
    (z23 : ∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b)
    (z24 : ∀ j, |pq j - k| ≤ m) (z25 : |logOm| ≤ La)
    (z26 : lam0 ≤ b) (z27 : N ^ 2 ≤ b) (z28 : m ^ 3 * N ^ 2 * L ≤ b) (z29 : m * η * N * L ≤ b)
    (z30 : k * N ≤ b) (z31 : k * S ≤ w'') (z32 : m * (tt + 1) * η ≤ w'') (z33 : N * w'' ≤ b)
    (z34 : b' * N ≤ a) (z35 : m * k * b' ≤ a)
    (hC : 0 ≤ C) (hCC : C ≤ C0) (hnV : 0 ≤ nV) (hnVN : nV ≤ N) (hL' : 0 ≤ L') (hCL : C * L' ≤ C0 * La)
    (y1 : Lpass ≤ 1 + C0 * lam0)
    (y5 : ∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La)
    (y6 : ∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0)))
    (z11 : 0 ≤ Nc) (y2 : Eb ≤ c * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc))) :
    muC + recordHu TT ν aT logH logT logOm f m N S η b' nV L La L' C - 2 * Fo ≤
      (∑ t ∈ TT, (m * (ph (aT t) - aT t * logOm) - aT t * logT)) +
      (50 * C0 + 10) * ((TT.card : ℝ) * a * La) +
      (50 * C0 + 10 + c) * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc)) := by
  have key := divIneqRecordFree6 J Pl TT r ν muC mu0 Fo logT aT logH x eps L b a rd La L' B0 m f k N nV
    S tt η w'' b' lam0 C C0 Lpass Eb logOm pq w eE δ q1 q2 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z13 z14 z15 z16 z17 z18
    z19 z20 z21 zb z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35 hC hCC hnV hnVN hL' hCL y1 y5 y6
  have hC0 : 0 ≤ C0 := le_trans hC hCC
  have h1 : 0 ≤ (50 * C0 + 10) * (m * (Real.log x ^ 2 * Nc)) := by positivity
  nlinarith

theorem fineToUniform6 (x eps B0 Nc m c' : ℝ) (hx : 1 ≤ x) (hB : 0 ≤ B0) (hN : 0 ≤ Nc) (hm : 0 ≤ m)
    (h1 : c' ≤ x ^ eps) (h2 : c' * Real.log x ^ 2 ≤ x ^ (2 * eps)) :
    c' * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc)) ≤ m * (B0 + Nc) * x ^ (2 * eps) := by
  have e : x ^ (2 * eps) = x ^ eps * x ^ eps := by
    rw [two_mul, Real.rpow_add (by linarith)]
  have hxe : 0 ≤ x ^ eps := Real.rpow_nonneg (by linarith) _
  have a1 : c' * (x ^ eps * B0) ≤ x ^ (2 * eps) * B0 := by
    rw [e]; nlinarith [mul_le_mul_of_nonneg_right h1 (mul_nonneg hxe hB)]
  have a2 : c' * (Real.log x ^ 2 * Nc) ≤ x ^ (2 * eps) * Nc := by
    nlinarith [mul_le_mul_of_nonneg_right h2 hN]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add a1 a2) hm]

theorem logPrimeBound6 (x L b a rd La g nV L' Cg : ℝ) (hx : 1 ≤ x) (hb : b = Real.exp L)
    (ha : a = x * b) (hrd : 1 ≤ rd) (hLa : La = Real.log (a * rd)) (hg : 0 < g) (hgl : Real.log g ≤ Cg * L)
    (hn : 0 < nV) (hnl : Real.log nV ≤ L) (hCg : 0 ≤ Cg) (hL' : L' = Real.log (b * rd * g * nV)) :
    L' ≤ (2 + Cg) * La := by
  have hbpos : 0 < b := by rw [hb]; exact Real.exp_pos _
  have hx0 : 0 < x := by linarith
  have hr0 : 0 < rd := by linarith
  have e1 : La = Real.log x + L + Real.log rd := by
    rw [hLa, ha, Real.log_mul (by positivity) hr0.ne', Real.log_mul hx0.ne' hbpos.ne', hb, Real.log_exp]
  have e2 : L' = L + Real.log rd + Real.log g + Real.log nV := by
    rw [hL', Real.log_mul (by positivity) hn.ne', Real.log_mul (by positivity) hg.ne',
      Real.log_mul hbpos.ne' hr0.ne', hb, Real.log_exp]
  have h1 := Real.log_nonneg hx
  have h2 := Real.log_nonneg hrd
  rw [e1, e2]
  nlinarith [mul_nonneg hCg h1, mul_nonneg hCg h2]

end Formalism.DimensionVariation
