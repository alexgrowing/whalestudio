import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabiliserFiniteGenerationVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnOfHoloOn
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
open GlobalTheory.IrrAn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preconnected_in_union_analytic : ∀ (d : ℕ) (Y : Type) [TopologicalSpace Y] (A : FinHolAtlas d Y) (S Z₁ Z₂ : Set Y), IsPreconnected S → S.Nonempty → GlobalTheory.IrrAn.LocIdent A S → A.IsAnalyticSubset Z₁ → A.IsAnalyticSubset Z₂ → S ⊆ Z₁ ∪ Z₂ → S ⊆ Z₁ ∨ S ⊆ Z₂ := by
  first | exact @GlobalTheory.IrrAn.subset_or_subset_of_locIdent | exact GlobalTheory.IrrAn.subset_or_subset_of_locIdent | (intros; apply GlobalTheory.IrrAn.subset_or_subset_of_locIdent <;> assumption)
