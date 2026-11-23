import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsDegreeFrameLeLogDiscriminant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLgOfDetSymSubLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoArithmeticDegreeFlagHomogeneousStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.FlatObj

open Filter Topology in

theorem flat_line_onObj : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → ∃ Cf : ℝ, OnObj fun _ O A _ _ _ =>
    FewBad O.Y → FlatBd O.Y Cf ∧ ∀ Φ : ℝ → Fn O.Y, LimFam Φ → FlatVal A Φ := by
  intro hX h2 hH hSW
  obtain ⟨C₁, h1⟩ := GlobalTheory.T.abs_degree_frame_le_log_discriminant h2 hH hSW
  obtain ⟨C₂, hp⟩ := GlobalTheory.PlaceBd.placeBd h2 hH
  have hl := GlobalTheory.T.tendsto_arithmetic_degree_flag_homogeneous hX h2 hH hSW
  refine ⟨max C₁ 0 + max C₂ 0, fun D O hO hf A T H h hF => ⟨fun B hB c τ => ?_, fun Φ hL => ?_⟩⟩
  · have a1 := h1 D O hO hf A T H h c τ
    have a2 := hp D O hO hf A T H h hF B hB c τ
    have hrd1 : 0 ≤ Real.log D.host.rdE := by
      unfold Formalism.BasicNotions.Host.rdE
      refine Real.log_nonneg (Real.one_le_rpow ?_ (by positivity))
      have h0 : (NumberField.discr D.host.E) ≠ 0 := NumberField.discr_ne_zero _
      have : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs h0
      exact_mod_cast this
    have hrd : 0 < D.host.rdE := by
      unfold Formalism.BasicNotions.Host.rdE
      exact Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero _)) _
    have hlB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
    have hlg : lg D B = Real.log B + Real.log D.host.rdE + |dlogL D 1| := by
      unfold lg
      rw [Real.log_mul (by linarith) hrd.ne']
    have hN : (0 : ℝ) ≤ O.Y.N := Nat.cast_nonneg _
    have ha := abs_nonneg (dlogL D 1)
    have b1 : |GlobalTheory.ShFam.Pad.degFrame O.s O.Φ O.met.hm c τ| ≤ max C₁ 0 * O.Y.N * lg D B := by
      refine a1.trans ?_
      rw [hlg]
      have e1 : C₁ * O.Y.N ≤ max C₁ 0 * O.Y.N := mul_le_mul_of_nonneg_right (le_max_left _ _) hN
      have e2 : 0 ≤ max C₁ 0 * O.Y.N := mul_nonneg (le_max_right _ _) hN
      nlinarith
    have b2 : |O.Y.htDetT B c τ - GlobalTheory.ShFam.Pad.degFrame O.s O.Φ O.met.hm c τ| ≤ max C₂ 0 * O.Y.N * lg D B := by
      refine a2.trans ?_
      rw [hlg]
      have e1 : C₂ * O.Y.N ≤ max C₂ 0 * O.Y.N := mul_le_mul_of_nonneg_right (le_max_left _ _) hN
      have e2 : 0 ≤ max C₂ 0 * O.Y.N := mul_nonneg (le_max_right _ _) hN
      nlinarith
    have htri := abs_sub_abs_le_abs_sub (O.Y.htDetT B c τ) (GlobalTheory.ShFam.Pad.degFrame O.s O.Φ O.met.hm c τ)
    have : (max C₁ 0 + max C₂ 0) * O.Y.N * lg D B = max C₁ 0 * O.Y.N * lg D B + max C₂ 0 * O.Y.N * lg D B := by ring
    rw [this]
    linarith
  · intro B hB τ Q hQ
    have h1 := (hL B hB (GlobalTheory.FlagPoly.pSum τ 1 * Q)).sub_const
      (∑ c, O.Y.htDetT B c τ * (A.w c * Formalism.DegreeFormula.degFl D.what₂.Tau O.Y.N Q))
    have h2 := tendsto_nhds_unique h1 (hl D O hO hf A T H h B hB τ Q hQ)
    rw [sub_eq_zero] at h2
    rw [h2, Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by ring

example : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → ∃ Cf : ℝ, OnObj fun _ O A _ _ _ =>
    FewBad O.Y → FlatBd O.Y Cf ∧ ∀ Φ : ℝ → Fn O.Y, LimFam Φ → FlatVal A Φ := flat_line_onObj

end GlobalTheory.FlatObj
