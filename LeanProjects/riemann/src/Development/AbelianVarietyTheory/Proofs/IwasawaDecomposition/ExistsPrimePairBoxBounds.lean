import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsExcRat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.PageThm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Jutila
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeThreeModEightGoodStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeSevenModSixteenGoodStatement
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

theorem boundsAtX_mono_const {x eps C C' : ℝ} {f : ℕ → ℂ} {M : ℕ} (hx : 0 ≤ Real.log x) (hC : C ≤ C')
    (h : BoundsAtX x eps C f M) : BoundsAtX x eps C' f M := by
  intro N _ χ hχ
  obtain ⟨h1, h2⟩ := h N χ hχ
  exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right hC hx)⟩

theorem log_four_mul_nqd_le {x eps : ℝ} {n q d : ℕ} (he : 0 < eps) (he' : eps < 1 / 52)
    (hx : Real.exp 5 ≤ x) (hn1 : 1 ≤ n) (hq1 : 1 ≤ q) (hd1 : 1 ≤ d)
    (hn : (n : ℝ) ≤ 2 * x ^ (2 + 8 * eps)) (hq : (q : ℝ) ≤ GlobalTheoryTheory.X1 x eps) (hd : (d : ℝ) ≤ GlobalTheoryTheory.X2 x eps) :
    Real.log (4 * n * q * d) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 := by
  have hx0 : 0 < x := (Real.exp_pos 5).trans_le hx
  have hL : 5 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx
  have hy : 1 ≤ x ^ (eps / 5) := Real.one_le_rpow hx1 (by positivity)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hlq : Real.log q ≤ x ^ (eps / 5) := (Real.log_le_iff_le_exp hq0).2 hq
  have hld : Real.log d ≤ x ^ (eps / 5) * Real.log x ^ 2 := (Real.log_le_iff_le_exp hd0).2 hd
  have hln : Real.log n ≤ Real.log 2 + (2 + 8 * eps) * Real.log x := by
    have := Real.log_le_log hn0 hn
    rwa [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hx0 _).ne', Real.log_rpow hx0] at this
  have h4 : Real.log 4 ≤ 3 := by have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
  have h2 : Real.log 2 ≤ 1 := by have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  rw [Real.log_mul (by positivity) hd0.ne', Real.log_mul (by positivity) hq0.ne',
    Real.log_mul (by norm_num) hn0.ne']
  have h3 : (2 + 8 * eps) * Real.log x ≤ 3 * Real.log x :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h5 : 5 * Real.log x ≤ Real.log x ^ 2 := by nlinarith
  have h6 : Real.log x ^ 2 - 1 ≤ x ^ (eps / 5) * (Real.log x ^ 2 - 1) :=
    le_mul_of_one_le_left (by linarith) hy
  nlinarith

theorem exists_q_d_box_bounds_rows : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∃ q d : ℕ, Boxq x eps q d ∧ QDq x eps C q d ∧ ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ 2 * x ^ (2 + 8 * eps) → Rowq x eps n q d := by
  intro p1 p2 p3 p4 p5 p6 p7 p8 eps he he'
  obtain ⟨x1, C1, hC1, H1⟩ := GlobalTheory.T.exists_prime_three_mod_eight_good p1 p2 p3 p4 p5 p6 p7 p8 eps he he'
  obtain ⟨x2, C2, hC2, H2⟩ := GlobalTheory.T.exists_prime_seven_mod_sixteen_good p1 p2 p3 p4 p5 p6 p7 p8 eps he he'
  refine ⟨max (max x1 x2) (Real.exp 5), max C1 C2, lt_max_of_lt_left hC1, fun x hx => ?_⟩
  have hx1 : x1 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hx2 : x2 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx5 : Real.exp 5 ≤ x := (le_max_right _ _).trans hx
  have hL : 0 ≤ Real.log x := Real.log_nonneg (le_trans (Real.one_le_exp (by norm_num)) hx5)
  obtain ⟨q, hq, hq8, hql, hqu, Hq⟩ := H1 x hx1
  obtain ⟨d, hd, hd16, hdl, hdu, hk, hsp, hg, hb1, hb2⟩ := H2 x hx2 q hq hq8 hql hqu
  obtain ⟨g1, g2, b0⟩ := Hq d hd (by omega) (by rintro rfl; omega)
  refine ⟨q, d, ⟨g1, g2, ?_, ?_, ?_, ?_⟩,
    ⟨boundsAtX_mono_const hL (le_max_left _ _) b0, boundsAtX_mono_const hL (le_max_right _ _) hb1,
      boundsAtX_mono_const hL (le_max_right _ _) hb2⟩, fun n hn1 hn =>
    ⟨hq, hq8, hql, hqu, hd, hd16, hdl, hdu, hk, hsp,
      log_four_mul_nqd_le he he' hx5 hn1 hq.one_le hd.one_le hn hqu hdu⟩⟩
  · simpa using hg 0 0
  · simpa using hg 0 1
  · simpa using hg 1 0
  · simpa using hg 1 1

end GlobalTheory.Mem.An
