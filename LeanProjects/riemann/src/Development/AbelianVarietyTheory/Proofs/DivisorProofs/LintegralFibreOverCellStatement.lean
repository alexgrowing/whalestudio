import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFibreOverCell
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
theorem _root_.GlobalTheory.T.lintegral_fibre_over_cell : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (n r D : ℕ) (ε : Fin D ≃ Fin n ⊕ Low r) (σ : k →+* ℂ) [IsIntegral Y] (c : AlgChart q σ n) (c' : AlgChart p σ D), IsArithVar p D → IsCell ε π w c c' → ∀ ρ : AlgChart p σ D → CxPts p σ → ℝ, IsDens ρ → ∀ A : Set (CxPts q σ), MeasurableSet A → A ⊆ c.e.source → ∀ h : CxPts q σ → ℝ≥0∞, Measurable h → (∫⁻ y in PtsOver.map π w (spMap σ) ⁻¹' A, h (PtsOver.map π w (spMap σ) y) ∂part ρ = ∫⁻ u in c.e '' A, ∫⁻ x : Low r → ℂ, h (c.e.symm u) * ENNReal.ofReal (ρ c' (c'.e.symm (pt ε u x)))) ∧ AEMeasurable (fun u => ∫⁻ x : Low r → ℂ, h (c.e.symm u) * ENNReal.ofReal (ρ c' (c'.e.symm (pt ε u x)))) (volume.restrict (c.e '' A)) := by
  first | exact @GlobalTheory.FubCell.lintegral_cell | exact GlobalTheory.FubCell.lintegral_cell | (intros; apply GlobalTheory.FubCell.lintegral_cell <;> assumption)
