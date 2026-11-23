import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChartLiftBis
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
theorem _root_.GlobalTheory.T.flag_bundle_chart_lift_bis : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (n r D : ℕ) (ε : Fin D ≃ Fin n ⊕ Low r) (σ : k →+* ℂ) (E : B.Modules) (h : VMetric q E r) (H : h.IsCInf) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) r), IsFlagBundle π (fun _ : Unit => E) (fun _ => r) (fun _ => fl) → ∀ (c₀ : AlgChart q σ n), ∀ y ∈ c₀.e.source, ∃ (c : AlgChart q σ n) (cE : Chart E r) (c' : AlgChart p σ D), y ∈ c.e.source ∧ c.e.source ⊆ ptsIn q σ cE.U ∧ IsCell ε π w c c' ∧ ∀ y' ∈ c'.e.source, ∀ i : Fin r, chernMat ((VMetric.grLB fl i (H.pull π w)).φ σ) c' y' = cHess D (fun v => (rootWt ε (fun u => (h.met σ).G cE (c.e.symm u)) i v : ℂ)) (c'.e y') := by
  first | exact @GlobalTheory.FlagCellDim.exists_cell_chart | exact GlobalTheory.FlagCellDim.exists_cell_chart | (intros; apply GlobalTheory.FlagCellDim.exists_cell_chart <;> assumption)
