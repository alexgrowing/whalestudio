import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsSumToVolumeProportionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestClassSelfIntersection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeVandermondeSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeChernCurveClassStatement

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR

namespace GlobalTheory.BcFib

theorem sieg_sub_vdmVal {D : D7} (Y : DV.ShimX D.what₂.Tau) (R : ℝ) :
    sieg Y ∅ R - vdmVal Y R = Y.arMix ∅ R 1 (X (Sum.inr (false, 2)) * DV.tagDR D.what₂.Tau Y.N
        (lamA D.what₂.Tau Y.N Y.j ^ (dimGr D.what₂.Tau Y.N Y.j - 1) *
          (fibPt D.what₂.Tau Y.N Y.j - vdmCl D.what₂.Tau Y.N Y.j))) := by
  rw [sieg, vdmVal, curveCl, curveV, mul_sub, map_sub, mul_sub, map_sub]

theorem chern_invForm {D : D7} (Y : DV.ShimX D.what₂.Tau) (hP : Propor Y) :
    Y.chern (invForm Y.j (fun _ => -(((Y.j : ℝ) - 1) / Y.j))
          (fun _ => -(((Y.N : ℝ) - Y.j - 1) / ((Y.N : ℝ) - Y.j))) *
        curveCl D.what₂.Tau Y.N Y.j) = Y.vol * bcFl Y := by
  have hH : ∀ τ, Y.chern (pHigh Y.j τ 1 * curveCl D.what₂.Tau Y.N Y.j) =
      -Y.chern (pLow Y.j τ 1 * curveCl D.what₂.Tau Y.N Y.j) := by
    intro τ
    have h1 := hP (-pHigh Y.j τ 1 * curveCl D.what₂.Tau Y.N Y.j)
    rw [GlobalTheory.RestTest.degFl_neg_pHigh, ← hP, neg_mul, map_neg] at h1
    linarith
  have e : ∀ τ, Y.chern ((C (-(((Y.j : ℝ) - 1) / Y.j)) * pLow Y.j τ 1 +
      C (-(((Y.N : ℝ) - Y.j - 1) / ((Y.N : ℝ) - Y.j))) * pHigh Y.j τ 1) * curveCl D.what₂.Tau Y.N Y.j) =
      (-(((Y.j : ℝ) - 1) / Y.j) - -(((Y.N : ℝ) - Y.j - 1) / ((Y.N : ℝ) - Y.j))) *
        (Y.vol * degFl D.what₂.Tau Y.N (pLow Y.j τ 1 * curveCl D.what₂.Tau Y.N Y.j)) := by
    intro τ
    rw [add_mul, map_add, mul_assoc, mul_assoc, ← smul_eq_C_mul, ← smul_eq_C_mul, LinearMap.map_smul,
      LinearMap.map_smul, hH, hP, smul_eq_mul, smul_eq_mul]
    ring
  rw [bcFl_eq, invForm, Finset.sum_mul, map_sum, Finset.sum_congr rfl (fun τ _ => e τ), ← Finset.mul_sum,
    ← Finset.mul_sum, testI]
  ring

theorem tendsto_sieg_sub_vdmVal : Hypotheses2 → HypothesesH → RegularAlteration → GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.Ch2HodgeVanishes →
    OnObj fun _ O _ _ _ _ => Tendsto (fun R : ℝ => sieg O.Y ∅ R - vdmVal O.Y R) atTop (𝓝 (O.Y.vol * bcFl O.Y)) := by
  intro h2 hH hR _ D O hc hf A T H hr
  have hP := (GlobalTheory.T.weights_sum_to_volume_proportional h2 hH D O hc hf A T H hr).2.2
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR2
  rw [sieg_sub_vdmVal, GlobalTheory.T.arithmetic_degree_vandermonde_sum h2 hH hR D O hc hf A T H hr R hR2, GlobalTheory.T.vandermonde_chern_curve_class h2 hH hR D O hc hf A T H hr R hR2,
    chern_invForm _ hP]

end GlobalTheory.BcFib

end
