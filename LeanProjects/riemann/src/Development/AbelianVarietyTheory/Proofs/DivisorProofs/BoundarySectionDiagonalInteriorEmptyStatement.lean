import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySectionDiagonalInteriorEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareFormStatementStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
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
theorem _root_.GlobalTheory.T.boundary_section_diagonal_interior_empty : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (At : FinHolAtlas e X) (m : ℕ) (L : Fin m → LocPot X) (sg : Fin m → X → X → ℂ) (Dd : Fin m → Set X), GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.IsBoundary At L sg Dd → ∀ i, interior {y | sg i y y = 0} = ∅ := by
  first | exact @GlobalTheory.SncZero.interior_zero_boundary | exact GlobalTheory.SncZero.interior_zero_boundary | (intros; apply GlobalTheory.SncZero.interior_zero_boundary <;> assumption)
