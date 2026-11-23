import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernOneEqNegDdcLogDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixDens

theorem chernMat_det_pull_eq_trace_curv : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (σ : k →+* ℂ) (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (D : ℕ) (ch : AlgChart q σ D) (cE : Chart ((Scheme.Modules.pullback π).obj E) r), ∀ y ∈ ch.e.source, y ∈ ptsIn q σ cE.U → chernMat (((VMetric.det H).pull π hπ).φ σ) ch y = Matrix.of fun a b => (curv (fun u => ((h.pull π hπ).met σ).G cE (ch.e.symm u)) (ch.e y) (bas D a) (bas D b)).trace := by
  intro k _ X Y p q π hπ σ E r h H D ch cE y hy hU
  rw [← chernMat_congr (VMetric.isometric_det_pull H π hπ) ch hy]
  have hi : y ∈ ptsIn q σ ((VMetric.det (H.pull π hπ)).B.U cE) := hU
  have ho := ChartGlue.isOpen_over ch.e (isOpen_ptsIn (p := q) (σ := σ) cE.U)
  have hm := ChartGlue.mem_over ch.e hy hU
  have hM : MContDiffAt 2 (fun u => ((h.pull π hπ).met σ).G cE (ch.e.symm u)) (ch.e y) :=
    ((((H.pull π hπ) σ) cE y hU).mContDiffAt ch hy).of_le (WithTop.coe_le_coe.2 le_top)
  have hH : ∀ᶠ w in 𝓝 (ch.e y), (((h.pull π hπ).met σ).G cE (ch.e.symm w)).IsHermitian := by
    filter_upwards [ho.mem_nhds hm] with v hv
    exact (((h.pull π hπ).met σ).posDef cE _ hv.2).1
  have hu : IsUnit (((h.pull π hπ).met σ).G cE (ch.e.symm (ch.e y))).det := by
    rw [ch.e.left_inv hy]
    exact (((h.pull π hπ).met σ).posDef cE y hU).det_pos.ne'.isUnit
  have hd : ContDiffAt ℝ 2 (fun v => ((VMetric.det (H.pull π hπ)).φ σ).φ cE (ch.e.symm v)) (ch.e y) :=
    ((VMetric.det (H.pull π hπ)).cInf σ).contDiffAt ch hy hi
  have hc : ContDiffAt ℝ 2 (fun v => ((((VMetric.det (H.pull π hπ)).φ σ).φ cE (ch.e.symm v) : ℝ) : ℂ)) (ch.e y) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ hd
  ext a b
  rw [chernMat, ch.hess_eq ((VMetric.det (H.pull π hπ)).cInf σ) hy hi (mem_pick _ y)]
  show ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((((VMetric.det (H.pull π hπ)).φ σ).φ cE (ch.e.symm v) : ℝ) : ℂ)) (ch.e y) a b = _
  rw [GlobalTheory.CurveDens.cHess_apply_eq_ddbar hc, Matrix.of_apply, trace_curv hM hH hu]
  show leviForm (fun v => -Real.log (((h.pull π hπ).met σ).G cE (ch.e.symm v)).det.re) (ch.e y) _ _ = _
  rw [leviForm_neg]
  rfl

end GlobalTheory.MixDens
