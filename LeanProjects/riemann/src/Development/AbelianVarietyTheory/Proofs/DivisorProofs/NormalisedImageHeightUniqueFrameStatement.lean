import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedImageHeightUniqueFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedImageHeight_unique_frame : Quoted → ∀ (F : Type) [Field F] [NumberField F] (V Ω : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] [Field Ω] [Algebra F Ω] (Nm : (F →+* ℂ) → V → ℝ) (W : Submodule (𝓞 F) V) (ev : V →ₗ[F] Ω) (D : ℕ) (h h' : ℝ), IsTotallyComplex F → CompHt.IsImageHeight Nm W ev D h → CompHt.IsImageHeight Nm W ev D h' → h = h' := by
  first | exact @GlobalTheory.ImageHeightFrame.isImageHeight_unique | exact GlobalTheory.ImageHeightFrame.isImageHeight_unique | (intros; apply GlobalTheory.ImageHeightFrame.isImageHeight_unique <;> assumption)
