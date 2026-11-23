import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionIndexCovering
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_index_covering : ∀ (K'' : Type) [Field K''] (P : Out.PolAV (Sp K'')) (N : ℕ), ∃ i₀ : (lbPow P.L N).ι, ⊤ ≤ (eSec P.A) ⁻¹ᵁ (lbPow P.L N).U i₀ := by
  first | exact @GlobalTheory.OriginChart.exists_chart_lbPow_eSec | exact GlobalTheory.OriginChart.exists_chart_lbPow_eSec | (intros; apply GlobalTheory.OriginChart.exists_chart_lbPow_eSec <;> assumption)
