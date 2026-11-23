import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegGeomDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountMonoLattice
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PackingStatement

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem selfIntersection_le_volNm_of_moriwakiBig : MoriwakiBigStatement → BirationalPullbackPushforwardFormula := by
  intro h K _ ι _ Ω _ y D A P0 II hD hII hV hB hP hS hF hC
  have hN : NefOnGeneric (mCoordIdeal y) A :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.NefOnGenericOfSemipos.proof K ι (mCoordIdeal y) P0 A hP hS
  have hb := h K ι Ω y D A P0 II hII hV hB hP hS hC hF hN
  obtain ⟨hfin, C, hC'⟩ := GlobalTheory.T.packing' K ι Ω y D A (chartLatNm y A.a) hV hB hS.1 (fun _ => le_rfl)
  refine hb.trans ?_
  unfold arVolP
  have h0 : ∀ (La : ℕ → AddSubgroup Ω) (τ : ℕ), 0 ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y A) La τ := by
    intro La τ
    unfold smallSectionCount
    exact Real.log_natCast_nonneg _
  have hden : ∀ k : ℕ, (0 : ℝ) ≤ ((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := fun k => by positivity
  refine Filter.limsup_le_limsup ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun k => div_le_div_of_nonneg_right
      (GroundTheory.Heights₂.Heights.HilbertSamuel.smallSectionCount_mono_lattice _ _
        (GroundTheory.Heights₂.Heights.HilbertSamuel.chartLat_le_chartLatNm y A.a _) (hfin _)) (hden k)
  · exact Filter.isCoboundedUnder_le_of_le Filter.atTop (fun k => div_nonneg (h0 _ _) (hden k))
  · refine Filter.isBoundedUnder_of_eventually_le (a := max C 0 * 2 ^ (D + 1) * ((D + 1).factorial : ℝ)) ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hkpos : (0 : ℝ) < ((1 * k : ℕ) : ℝ) := by
      rw [one_mul]
      exact_mod_cast hk
    have hF : (0 : ℝ) < ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hpos : (0 : ℝ) < ((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
    rw [div_le_iff₀ hpos]
    have h1 := hC' (1 * k)
    have h2 : ((1 * k : ℕ) : ℝ) + 1 ≤ 2 * ((1 * k : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((1 * k : ℕ) : ℝ) := by
        rw [one_mul]
        exact_mod_cast hk
      linarith
    have h3 : (((1 * k : ℕ) : ℝ) + 1) ^ (D + 1) ≤ (2 * ((1 * k : ℕ) : ℝ)) ^ (D + 1) :=
      pow_le_pow_left₀ (by positivity) h2 _
    have h4 : C * (((1 * k : ℕ) : ℝ) + 1) ^ (D + 1) ≤ max C 0 * (((1 * k : ℕ) : ℝ) + 1) ^ (D + 1) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have hF' := hF.ne'
    calc _ ≤ max C 0 * (2 * ((1 * k : ℕ) : ℝ)) ^ (D + 1) :=
          h1.trans (h4.trans (mul_le_mul_of_nonneg_left h3 (le_max_right _ _)))
      _ = max C 0 * 2 ^ (D + 1) * ((D + 1).factorial : ℝ) *
          (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
        field_simp
        ring

end GlobalTheory.CompanionTheory.Ar.Small
