import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicIndependentPulledBackProjCoordinateRati
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XMemOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicIndependent_pulledBackProjCoordinateRatios : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → AlgebraicIndependent ℂ (fun j : Fin d => rat φ 0 j.succ) := by
  first | (exact @GlobalTheory.PD.XCover.algebraicIndependent_rat) | (exact GlobalTheory.PD.XCover.algebraicIndependent_rat) | (intros; apply GlobalTheory.PD.XCover.algebraicIndependent_rat  <;> assumption)
