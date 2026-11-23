import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenGramSmooth
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
theorem _root_.GlobalTheory.T.eigen_gram_smooth : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ)
    (G : EigMet s.T.Z σ) (T : Set (CxPts (genStr s.T.Z) σ)), IsOpen T → G.SmoothOn (manifold s.T.Z σ) T →
    ∀ (n : ℕ) (U : Set (V n)) (a : V n → CxFr s.T.Z σ), IsOpen U → HolFam U a → ContinuousOn (fun u => (a u).1) U →
    ∀ u ∈ U, (a u).1 ∈ T → ∀ (τ : D.host.E →+* ℂ) i k, ContDiffAt ℝ (∞ : WithTop ℕ∞) (fun v => eigGram G a τ v i k) u := by
  first | exact @GlobalTheory.GramSmooth.contDiffAt_eigGram | exact GlobalTheory.GramSmooth.contDiffAt_eigGram | (intros; apply GlobalTheory.GramSmooth.contDiffAt_eigGram <;> assumption)
