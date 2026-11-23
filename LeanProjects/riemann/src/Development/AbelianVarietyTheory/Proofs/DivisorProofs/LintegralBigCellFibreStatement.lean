import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBigCellFibre
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDensityPushforwardIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetPartitionNull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartOffClosedSubsetStatement
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
theorem _root_.GlobalTheory.T.lintegral_big_cell_fibre : ∀ (n r D : ℕ) (ε : Fin D ≃ Fin n ⊕ Low r) (K : Set (V n)) (H : V D → ℝ≥0∞), MeasurableSet K → AEMeasurable H (volume.restrict (base ε ⁻¹' K)) → (∫⁻ v in base ε ⁻¹' K, H v = ∫⁻ u in K, ∫⁻ x : Low r → ℂ, H (pt ε u x)) ∧ AEMeasurable (fun u => ∫⁻ x : Low r → ℂ, H (pt ε u x)) (volume.restrict K) := by
  first | exact @GlobalTheory.ArchLim.setLIntegral_base_eq | exact GlobalTheory.ArchLim.setLIntegral_base_eq | (intros; apply GlobalTheory.ArchLim.setLIntegral_base_eq <;> assumption)
