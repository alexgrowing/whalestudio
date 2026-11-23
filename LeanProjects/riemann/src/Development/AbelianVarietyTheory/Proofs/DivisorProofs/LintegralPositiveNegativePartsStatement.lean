import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralPositiveNegativeParts
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
theorem _root_.GlobalTheory.T.lintegral_positive_negative_parts : ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) (a G : ℝ) (φ : α → ℝ), AEMeasurable φ μ → ∫ x, φ x ∂μ = G → (ENNReal.ofReal |a| * ENNReal.ofReal |G| ≤ ∫⁻ x, ENNReal.ofReal |a| * ENNReal.ofReal |φ x| ∂μ) ∧ ((∫⁻ x, ENNReal.ofReal |a| * ENNReal.ofReal |φ x| ∂μ) ≠ ⊤ → (∫⁻ x, (ENNReal.ofReal a * ENNReal.ofReal (φ x) + ENNReal.ofReal (-a) * ENNReal.ofReal (-φ x)) ∂μ) + (ENNReal.ofReal a * ENNReal.ofReal (-G) + ENNReal.ofReal (-a) * ENNReal.ofReal G) = (∫⁻ x, (ENNReal.ofReal a * ENNReal.ofReal (-φ x) + ENNReal.ofReal (-a) * ENNReal.ofReal (φ x)) ∂μ) + (ENNReal.ofReal a * ENNReal.ofReal G + ENNReal.ofReal (-a) * ENNReal.ofReal (-G))) := by
  first | exact @GlobalTheory.FibreParts.fibre_parts | exact GlobalTheory.FibreParts.fibre_parts | (intros; apply GlobalTheory.FibreParts.fibre_parts <;> assumption)
