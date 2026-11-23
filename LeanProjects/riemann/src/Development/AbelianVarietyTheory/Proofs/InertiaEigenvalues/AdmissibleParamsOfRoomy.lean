import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersPageLargeScaleBoundsOfLargeScaleStatement
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem admissible_params_of_roomy {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (h : Roomy L 100) :
    (L.etaSz + D.R.t + L.Sc + 2 < L.sc.w'' D.R.n ∧ L.sc.w'' D.R.n ≤ L.sc.b' ∧ 100 * L.sc.b' ≤ L.sc.b ∧
      (∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ 3 / 2 * L.sc.b') ∧ (D.R.t : ℝ) ≤ L.etaSz) ∧
      L.Sc + L.etaSz + D.R.t + 2 ≤ L.sc.b := by
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := h
  have he := L.etaSz_pos
  have hS := L.Sc_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ (D.host.Lw : ℝ) := by positivity
  have hb : (0 : ℝ) ≤ L.sc.b' := by linarith
  have hm : (0 : ℝ) ≤ (D.host.Lw : ℝ) * L.sc.b' := mul_nonneg hL hb
  have h6 : 100 * L.sc.b' ≤ L.sc.b := by nlinarith
  refine ⟨⟨by linarith, h3, h6, h4, P.t_le_eta⟩, by linarith⟩

theorem admissible_params_large : ∀ eps A : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), L.sc.eps = eps → P.CLw ≤ A → x0 ≤ L.sc.x → (L.etaSz + D.R.t + L.Sc + 2 < L.sc.w'' D.R.n ∧ L.sc.w'' D.R.n ≤ L.sc.b' ∧ 100 * L.sc.b' ≤ L.sc.b ∧ (∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ 3 / 2 * L.sc.b') ∧ (D.R.t : ℝ) ≤ L.etaSz) ∧ L.Sc + L.etaSz + D.R.t + 2 ≤ L.sc.b := by
  intro eps A heps
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.roomy_of_large_scale eps 100 A heps le_rfl
  exact ⟨x0, fun D L P h1 h2 h3 => admissible_params_of_roomy L P (hx0 D L P h1 h2 h3)⟩

end GlobalTheory.HTW
