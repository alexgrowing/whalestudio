import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsEqOfLocal
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
theorem _root_.GlobalTheory.T.closed_subset_analytic : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [LocallyOfFiniteType p] (σ : k →+* ℂ) (d : ℕ) (R : AnRead p σ d) [CompactSpace (CxPts p σ)] (T : Set (Limits.pullback p (spMap σ) : Scheme.{0})), IsClosed T → R.finAtlas.IsAnalyticSubset (GlobalTheory.IrrAn.ptsOf p σ T) := by
  first | exact @GlobalTheory.IrrAn.isAnalyticSubset_ptsOf | exact GlobalTheory.IrrAn.isAnalyticSubset_ptsOf | (intros; apply GlobalTheory.IrrAn.isAnalyticSubset_ptsOf <;> assumption)
