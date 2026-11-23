import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogResolutionProjectiveOfPrincipalisation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logResolution_projective_of_principalisation : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∀ T : Closeds X, genericPoint X ∉ T → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X), SmoothOfRelativeDimension D (π ≫ p) ∧ IsProjOver (π ≫ p) ∧ topologicalKrullDim Y = D ∧ π (genericPoint Y) = genericPoint X ∧ π.residueDegree (genericPoint Y) = 1 ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (⟨π ⁻¹' (T : Set X), T.isClosed.preimage π.continuous⟩ : Closeds Y)) := by
  first | exact @GlobalTheory.LogResProj.exists_logResolution | exact GlobalTheory.LogResProj.exists_logResolution | (intros; apply GlobalTheory.LogResProj.exists_logResolution <;> assumption)
