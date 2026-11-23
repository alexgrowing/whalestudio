import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialsBoundedByPositive
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
theorem _root_.GlobalTheory.T.potentials_bounded_by_positive : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (At : FinHolAtlas e X) (α : LocPot X) (m : ℕ) (Λ : Fin m → LocPot X), IsPotential At α → ReciprocityTheory.AnForm.M.IsPosPot At α → (∀ i, IsPotential At (Λ i)) → ∃ K : Fin m → ℝ, ∀ i, 0 ≤ K i ∧ GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions.FormBoundedBy At α (Λ i) (K i) := by
  first | exact @GlobalTheory.PosDom.exists_formBoundedBy | exact GlobalTheory.PosDom.exists_formBoundedBy | (intros; apply GlobalTheory.PosDom.exists_formBoundedBy <;> assumption)
