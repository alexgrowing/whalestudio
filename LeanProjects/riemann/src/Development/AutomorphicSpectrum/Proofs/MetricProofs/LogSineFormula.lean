import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.LogSin

theorem hermitian_pair_one_coordinates (G : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) :
    herm2 G ![1, a] ![1, b] =
      G 0 0 + G 0 1 * b + (starRingEnd ℂ) a * G 1 0 + (starRingEnd ℂ) a * G 1 1 * b := by
  simp [herm2, dotProduct, mulVec, Fin.sum_univ_two]
  ring

theorem gram_identity (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.IsHermitian) (a₀ a₁ : ℂ) :
    (herm2 G ![1, a₀] ![1, a₀]).re * (herm2 G ![1, a₁] ![1, a₁]).re - ‖herm2 G ![1, a₀] ![1, a₁]‖ ^ 2 =
      G.det.re * ‖a₁ - a₀‖ ^ 2 := by
  have h10 : G 1 0 = (starRingEnd ℂ) (G 0 1) := (hG.apply 1 0).symm
  have h00 : (G 0 0).im = 0 := Complex.conj_eq_iff_im.mp (hG.apply 0 0)
  have h11 : (G 1 1).im = 0 := Complex.conj_eq_iff_im.mp (hG.apply 1 1)
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, Matrix.det_fin_two,
    hermitian_pair_one_coordinates, hermitian_pair_one_coordinates, hermitian_pair_one_coordinates, h10]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, h00, h11]
  ring

theorem hermitian_pair_one_re_pos (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.PosDef) (a : ℂ) :
    0 < (herm2 G ![1, a] ![1, a]).re := by
  have hne : (![1, a] : Fin 2 → ℂ) ≠ 0 := fun h => by simpa using congrFun h 0
  have h := hG.dotProduct_mulVec_pos hne
  exact (Complex.lt_def.mp h).1

theorem det_re_pos (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.PosDef) : 0 < G.det.re :=
  (Complex.lt_def.mp hG.det_pos).1

theorem logSin_eq_log_add_xiPot (G : Matrix (Fin 2) (Fin 2) ℂ) (a₀ a₁ : ℂ) (hG : G.PosDef) (hne : a₀ ≠ a₁) :
    logSin G a₀ a₁ = Real.log ‖a₁ - a₀‖ + (1 / 2) * (xiPot G a₀ + xiPot G a₁) := by
  have hA := hermitian_pair_one_re_pos G hG a₀
  have hB := hermitian_pair_one_re_pos G hG a₁
  have hD := det_re_pos G hG
  have hn : 0 < ‖a₁ - a₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hid := gram_identity G hG.1 a₀ a₁
  unfold logSin xiPot
  set A := (herm2 G ![1, a₀] ![1, a₀]).re
  set B := (herm2 G ![1, a₁] ![1, a₁]).re
  set C := ‖herm2 G ![1, a₀] ![1, a₁]‖
  set D := G.det.re
  set n := ‖a₁ - a₀‖
  have harg : 1 - C ^ 2 / (A * B) = D * n ^ 2 / (A * B) := by
    rw [← hid]
    field_simp
  rw [harg, Real.log_div (by positivity) (by positivity), Real.log_mul hD.ne' (by positivity),
    Real.log_mul hA.ne' hB.ne', Real.log_pow]
  push_cast
  ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.LogSin
