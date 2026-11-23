import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricChernCurvaturePullback
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
theorem _root_.GlobalTheory.T.det_metric_chern_curvature_pullback : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (σ : k →+* ℂ) (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (D : ℕ) (ch : AlgChart q σ D) (cE : Chart ((Scheme.Modules.pullback π).obj E) r), ∀ y ∈ ch.e.source, y ∈ ptsIn q σ cE.U → chernMat (((VMetric.det H).pull π hπ).φ σ) ch y = Matrix.of fun a b => (curv (fun u => ((h.pull π hπ).met σ).G cE (ch.e.symm u)) (ch.e y) (bas D a) (bas D b)).trace := by
  first | exact @GlobalTheory.MixDens.chernMat_det_pull_eq_trace_curv | exact GlobalTheory.MixDens.chernMat_det_pull_eq_trace_curv | (intros; apply GlobalTheory.MixDens.chernMat_det_pull_eq_trace_curv <;> assumption)
