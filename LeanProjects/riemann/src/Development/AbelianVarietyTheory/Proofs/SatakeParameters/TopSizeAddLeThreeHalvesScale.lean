import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.Ggeo

theorem bT_add_div_le_three_halves : ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), 4 ≤ L.sc.x →
    ∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ 3 / 2 * L.sc.b' := by
  intro D L P hx t
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hb' : 0 < L.sc.b' := by
    unfold Formalism.BasicNotions.Scale.b' Formalism.BasicNotions.Scale.a Formalism.BasicNotions.Scale.b Formalism.BasicNotions.Scale.X'
    positivity
  have hbT := P.bT_le t
  have hrho := P.rho_le
  unfold Formalism.BasicNotions.LevelStarExponents.rhoP at hrho
  have hLaG : 0 < L.LaG := by
    have h1 := P.S_le
    have h2 := L.Sc_pos
    by_contra hneg
    have hneg' : L.LaG ≤ 0 := le_of_not_gt hneg
    have h3 : L.LaG * L.sc.b' / (D.R.k : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hneg' hb'.le) (Nat.cast_nonneg _)
    linarith
  have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg (by linarith)
  have h2 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / (D.R.k : ℝ) := by
    have := P.Crho_pos
    positivity
  set T := Formalism.BasicNotions.LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / (D.R.k : ℝ) with hT
  have hT4 : 4 * T ≤ L.sc.x ^ (-2 : ℝ) := by
    have h4 : 4 * Formalism.BasicNotions.LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / (D.R.k : ℝ) = 4 * T := by
      rw [hT]
      ring
    linarith
  have hbT' : (L.bT t : ℝ) ≤ L.sc.b' + T * L.sc.b' := by
    have h5 : Formalism.BasicNotions.LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) = T * L.sc.b' := by
      rw [hT]
      ring
    linarith
  have hx2 : L.sc.x ^ (-2 : ℝ) ≤ 1 / 16 := by
    calc L.sc.x ^ (-2 : ℝ) = (L.sc.x ^ 2)⁻¹ := by rw [Real.rpow_neg hx0.le, Real.rpow_two]
      _ ≤ (16 : ℝ)⁻¹ := (inv_le_inv₀ (by positivity) (by norm_num)).mpr (by nlinarith)
      _ = 1 / 16 := by norm_num
  have hTb : T * L.sc.b' ≤ L.sc.b' / 64 := by
    have h6 : T ≤ 1 / 64 := by linarith
    nlinarith
  have hdiv : L.sc.b' / L.sc.x ≤ L.sc.b' / 4 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx
  linarith

end GlobalTheory.Ggeo
