import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairwiseDisjointTriangularCells
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XMemOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_chart_affine_cover : ∀ (d : ℕ) (Z : Scheme.{0}) (φ : Z ⟶ PSpace ℂ d) [IsAffineHom φ], (⨆ i, φ ⁻¹ᵁ chart d i) = ⊤ ∧ ∀ I : Finset (Fin (d + 1)), I.Nonempty → IsAffineOpen (I.inf fun i => φ ⁻¹ᵁ chart d i) := by
  first | (exact @GlobalTheory.PD.XCover.preimage_chart_cover) | (exact GlobalTheory.PD.XCover.preimage_chart_cover) | (intros; apply GlobalTheory.PD.XCover.preimage_chart_cover  <;> assumption)
