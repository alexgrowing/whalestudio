import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositivePotentialCompact
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
theorem _root_.GlobalTheory.T.exists_positive_potential_compact : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) [CompactSpace (CxPts (genStr s.T.Z) σ)], ∃ α : LocPot (CxPts (genStr s.T.Z) σ), IsPotential (manifold s.T.Z σ).finAtlas α ∧ ReciprocityTheory.AnForm.M.IsPosPot (manifold s.T.Z σ).finAtlas α := by
  first | exact @GlobalTheory.KaehlerPot.exists_posPot_finAtlas | exact GlobalTheory.KaehlerPot.exists_posPot_finAtlas | (intros; apply GlobalTheory.KaehlerPot.exists_posPot_finAtlas <;> assumption)
