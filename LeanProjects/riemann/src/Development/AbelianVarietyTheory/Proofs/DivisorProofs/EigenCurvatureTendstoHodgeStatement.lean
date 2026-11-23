import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenCurvatureTendstoHodge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
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
theorem _root_.GlobalTheory.T.eigen_curvature_tendsto_hodge : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (n : ℕ) (U : Set (V n)) (a : V n → CxFr s.T.Z σ), IsOpen U → HolFam U a → ContinuousOn (fun u => (a u).1) U → ∀ u ∈ U, Inner (a u).1 → ∀ (τ : D.host.E →+* ℂ) (ξ η : V n), Tendsto (fun R : ℝ => curv (eigGram (x.eigMetAt σ (some R)) a τ) u ξ η) atTop (𝓝 (curv (eigGram (x.hodge σ) a τ) u ξ η)) := by
  first | exact @GlobalTheory.ArchLim.tendsto_curv_eigMetAt | exact GlobalTheory.ArchLim.tendsto_curv_eigMetAt | (intros; apply GlobalTheory.ArchLim.tendsto_curv_eigMetAt <;> assumption)
