import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SumSingleEmbeddingExtendLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.TorusFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TransvectionPeriodicity
import Formalism.LocalRingCardinality.ConjSqrtMinusD

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

lemma xiR_facts (D : D7) : xiR D = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) ∧
    1 ≤ (Ideal.absNorm D.host.ccK : ℝ) ∧ 1 ≤ Real.sqrt D.host.d := by
  have e1 : D.host.φ₀ D.host.xi0 =
      -1 / ((Ideal.absNorm D.host.ccK : ℂ) * D.host.φ₀ D.host.sqrtMinusD) := by
    unfold Host.xi0; simp [map_div₀, map_mul, map_neg, map_natCast]
  have e2 : ‖D.host.φ₀ D.host.sqrtMinusD‖ = Real.sqrt D.host.d := by
    have h0 : (D.host.φ₀ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ) := by
      rw [← map_pow, Formalism.BasicNotions.Host.sqrtMinusD_sq D.host, map_neg, map_natCast]
    rw [← Real.sqrt_sq (norm_nonneg (D.host.φ₀ D.host.sqrtMinusD)), ← norm_pow, h0, norm_neg,
      Complex.norm_natCast]
  refine ⟨?_, ?_, ?_⟩
  · unfold xiR; rw [e1, norm_div, norm_neg, norm_one, norm_mul, Complex.norm_natCast, e2]
  · have h : Ideal.absNorm D.host.ccK ≠ 0 := fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 h
  · have hd : 1 ≤ D.host.d := by have := D.host.qd_big.2; omega
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hd)

lemma xiR_le_half (D : D7) : xiR D ≤ 1 / 2 := by
  obtain ⟨hxi, hN1, hd1⟩ := xiR_facts D
  have ht : 1 ≤ D.R.t := D.R.t_odd.pos
  have hr : 1 ≤ D.R.r := (PfTies1.dimPos_fr D).2
  have h4 : 4 ≤ 4 * D.R.t * D.R.r := by nlinarith
  have hd : 4 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hsd : 2 ≤ Real.sqrt D.host.d := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
  rw [hxi]
  have hpos : 0 < (Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d := by positivity
  rw [div_le_div_iff₀ hpos (by norm_num)]
  nlinarith

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX
