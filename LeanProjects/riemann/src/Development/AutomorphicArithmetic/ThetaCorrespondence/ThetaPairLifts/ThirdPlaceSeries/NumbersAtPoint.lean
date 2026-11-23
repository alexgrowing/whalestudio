import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetNumberQuotientBounds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuoShapeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizesStatement

set_option synthInstance.maxHeartbeats 200000

section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.RefSum.NumPt
section Cols
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
end Cols
theorem _root_.GlobalTheory.RefSum.NumPtAlt.numbers_at_point : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → JetNum (Fm.D x ι) (DF (dat p i) (aOf p i u1)) (1 / 2500) ∧ 2 * (Fm.D x ι).R.r ≤ nCol (dat p i) ∧ (lenT p i PP : ℝ) * (Real.log ((Fm.D x ι).host.g 0) + Real.log ((Fm.D x ι).host.g 1)) ≤ C * unitE p := by
  intro hS
  refine Closed.imp (Closed.and (_root_.GlobalTheory.T.quotient_weight_gap_bounds' hS) (_root_.GlobalTheory.T.lenT_zBase_unitE_nCol_bounds hS)) ?_
  rintro eps Fm CH - ⟨⟨_, _, hA⟩, ⟨_, _, hB⟩⟩
  obtain ⟨x0, h⟩ := _root_.GlobalTheory.CovTop.EventuallyAtAllPoints.and hA hB
  refine ⟨max 0 (2 + 2 * Fm.CYL), le_max_left _ _, x0, fun x hx hle ι p hp i hi u1 hu => ?_⟩
  obtain ⟨hA, hB⟩ := h x hx hle ι p hp
  obtain ⟨a1, -, a3, a4, a5, a6, -⟩ := hA i hi u1 hu
  obtain ⟨b1, b2, -, -, b5, b6⟩ := hB i
  refine ⟨jetNum_of_sizes (Fm.sizes x hx ι) ?_, a3 ▸ two_mul_rank_le_nCol _, ?_⟩
  · have hev : Even (nCol (dat p i)) := even_iff_two_dvd.2 (Dvd.dvd.trans (by norm_num) eight_dvd_nCol)
    have := (GlobalTheory.T.thetaExponents_dominant_lastEntry_one_degree _ _ (dat p i) u1 (nCol (dat p i)) _ a1 hev a4 a5 a6).2.2.2.2
    rw [finrank_host, a3, Nat.mul_div_cancel_left _ two_pos] at this
    exact this
  · have hg := log_g_le (Fm.params x hx ι) b2 b5 b6
    rw [Fm.params_CYL x hx ι] at hg
    have hZ : 0 ≤ zBase (Fm.L x ι) ^ 12 := by positivity
    have hT : (0 : ℝ) ≤ lenT p i (Fm.parT x hx ι).PP := Nat.cast_nonneg _
    have hg' := hg.trans (mul_le_mul_of_nonneg_right (le_max_right 0 _) hZ)
    have h1 := mul_le_mul_of_nonneg_left hg' hT
    have h2 := mul_le_mul_of_nonneg_left b1 (le_max_left 0 (2 + 2 * Fm.CYL))
    linarith [mul_left_comm (lenT p i (Fm.parT x hx ι).PP : ℝ) (max 0 (2 + 2 * Fm.CYL)) (zBase (Fm.L x ι) ^ 12)]
end GlobalTheory.RefSum.NumPt
end
