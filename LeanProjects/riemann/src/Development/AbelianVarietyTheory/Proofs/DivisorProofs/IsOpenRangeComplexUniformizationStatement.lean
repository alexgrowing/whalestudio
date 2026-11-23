import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenRangeComplexUniformization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSecOfNot
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
theorem _root_.GlobalTheory.T.isOpen_range_complex_uniformization : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (M : DRBase O c) (σ : O.κ.c.F →+* ℂ), IsOpen (Set.range (up M.b rfl σ)) := by
  first | exact @GlobalTheory.CompClopen.isOpen_range_up | exact GlobalTheory.CompClopen.isOpen_range_up | (intros; apply GlobalTheory.CompClopen.isOpen_range_up <;> assumption)
