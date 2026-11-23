import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellChartBaseProjection
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
theorem _root_.GlobalTheory.T.cell_chart_base_projection : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (n r D : ℕ) (ε : Fin D ≃ Fin n ⊕ Low r) (σ : k →+* ℂ) (c : AlgChart q σ n) (c' : AlgChart p σ D), IsCell ε π w c c' → (∀ v ∈ c'.e.target, PtsOver.map π w (spMap σ) (c'.e.symm v) = c.e.symm (base ε v)) ∧ ∀ A : Set (CxPts q σ), A ⊆ c.e.source → c'.e '' (PtsOver.map π w (spMap σ) ⁻¹' A ∩ c'.e.source) = base ε ⁻¹' (c.e '' A) := by
  first | exact @GlobalTheory.ArchLim.cell_proj_and_image_eq | exact GlobalTheory.ArchLim.cell_proj_and_image_eq | (intros; apply GlobalTheory.ArchLim.cell_proj_and_image_eq <;> assumption)
