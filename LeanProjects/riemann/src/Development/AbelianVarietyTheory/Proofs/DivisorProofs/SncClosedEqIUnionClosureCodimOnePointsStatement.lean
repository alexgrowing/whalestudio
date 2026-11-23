import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncClosedEqIUnionClosureCodimOnePoints
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
theorem _root_.GlobalTheory.T.snc_closed_eq_iUnion_closure_codim_one_points : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ T : Closeds X, FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal T) → ∃ (r : ℕ) (z : Fin r → X), Function.Injective z ∧ (∀ a, Order.coheight (z a) = 1) ∧ (T : Set X) = ⋃ a, closure {z a} ∧ (∀ w : X, w ∈ T → Order.coheight w = 1 → ∃ a, w = z a) ∧ ∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x := by
  first | exact @GlobalTheory.SncGenericPoints.exists_genericPoints | exact GlobalTheory.SncGenericPoints.exists_genericPoints | (intros; apply GlobalTheory.SncGenericPoints.exists_genericPoints <;> assumption)
