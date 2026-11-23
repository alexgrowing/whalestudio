import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAnalyticInFiniteUnion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapCompSpMap
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
open GlobalTheory.HorComp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_analytic_in_finite_union : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] (At : FinHolAtlas d X) (C : Set X) (r : ℕ) (Zs : Fin r → Set X), IsIrreducibleAnalytic At C → (∀ i, At.IsAnalyticSubset (Zs i)) → C ⊆ ⋃ i, Zs i → ∃ i, C ⊆ Zs i := by
  first | exact @GlobalTheory.AnUnion.exists_subset_of_subset_iUnion | exact GlobalTheory.AnUnion.exists_subset_of_subset_iUnion | (intros; apply GlobalTheory.AnUnion.exists_subset_of_subset_iUnion <;> assumption)
