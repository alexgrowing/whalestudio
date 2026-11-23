import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensityChartFormula
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
theorem _root_.GlobalTheory.T.second_chern_density_chart_formula : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (E : X.Modules) (r : ℕ) (h : Met p σ E r) (L : LB X) (φ : Weight p σ L) (e : ℕ), h.IsCInf → φ.IsCInf → IsDens (secondChernDensityOfMetric h φ e) ∧ ∀ (c : AlgChart p σ (e + 2)) (cE : Chart E r), ∀ y ∈ c.e.source, y ∈ ptsIn p σ cE.U → secondChernDensityOfMetric h φ e c y = secondChernDensity e (chTwo (fun u => h.G cE (c.e.symm u)) (c.e y)) (chernMat φ c y) := by
  first | exact @GlobalTheory.ArchLim.ChTwoDens.isDens_ch2Dens | exact GlobalTheory.ArchLim.ChTwoDens.isDens_ch2Dens | (intros; apply GlobalTheory.ArchLim.ChTwoDens.isDens_ch2Dens <;> assumption)
