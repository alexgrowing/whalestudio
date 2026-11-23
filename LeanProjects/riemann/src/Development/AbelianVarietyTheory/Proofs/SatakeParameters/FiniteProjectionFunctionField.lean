import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilIntegralParahoricEquivariance
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XMemOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_projection_function_field : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → FiniteDimensional (fld φ) Z.functionField := by
  first | (exact @GlobalTheory.PD.XCover.finiteDimensional_fld) | (exact GlobalTheory.PD.XCover.finiteDimensional_fld) | (intros; apply GlobalTheory.PD.XCover.finiteDimensional_fld  <;> assumption)
