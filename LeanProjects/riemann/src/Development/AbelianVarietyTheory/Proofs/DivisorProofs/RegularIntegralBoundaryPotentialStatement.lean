import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularIntegralBoundaryPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointDimensionLtProjectiveLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LogResolutionProjectiveLine
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_integral_boundary_potential : GlobalTheory.Published.AnalyticLogResolution → GlobalTheory.Published.AnalyticSetDimension → ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas d X), IsProjective A → ∀ (m : ℕ) (α : LocPot X) (Λ : Fin m → LocPot X) (sg : Fin m → X → X → ℂ) (t : ℝ), IsBoundarySetting A α Λ sg t → ∀ (Z : Set X) (n : ℕ), IsIrreducibleAnalytic A Z → (regularLocus A Z n).Nonempty → ¬ Z ⊆ boundary sg → regIntegral A Z n (poincarePot α Λ sg t) (regularLocus A Z n \ boundary sg) (fun y => ENNReal.ofReal (1 + ∑ i, Real.log (rFun (Λ i) (sg i) y))) < ⊤ := by
  first | exact @GlobalTheory.LogRInt.logR_integrable | exact GlobalTheory.LogRInt.logR_integrable | (intros; apply GlobalTheory.LogRInt.logR_integrable <;> assumption)
