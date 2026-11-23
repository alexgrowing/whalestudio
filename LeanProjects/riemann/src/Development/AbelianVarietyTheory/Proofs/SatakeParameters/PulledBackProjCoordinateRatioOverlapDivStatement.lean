import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledBackProjCoordinateRatioOverlapDiv
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XMemOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledBackProjCoordinateRatio_overlap_div : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (φ : Z ⟶ PSpace ℂ d) (a i j : Fin (d + 1)), genericPoint Z ∈ φ ⁻¹ᵁ chart d a → genericPoint Z ∈ φ ⁻¹ᵁ chart d i → rat φ a i ≠ 0 ∧ rat φ i j = rat φ a j / rat φ a i := by
  first | (exact @GlobalTheory.PD.XCover.rat_overlap) | (exact GlobalTheory.PD.XCover.rat_overlap) | (intros; apply GlobalTheory.PD.XCover.rat_overlap  <;> assumption)
