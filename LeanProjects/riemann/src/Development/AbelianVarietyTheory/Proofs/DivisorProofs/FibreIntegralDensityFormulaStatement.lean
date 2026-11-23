import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIntegralDensityFormula
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
theorem _root_.GlobalTheory.T.fibre_integral_density_formula : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (n r D : ℕ) (ε : Fin D ≃ Fin n ⊕ Low r) (σ : k →+* ℂ) [IsIntegral Y] (c : AlgChart q σ n) (c' : AlgChart p σ D), IsArithVar q n → IsArithVar p D → IsCell ε π w c c' → ∀ (ρ : AlgChart p σ D → CxPts p σ → ℝ) (g : AlgChart q σ n → CxPts q σ → ℝ) (f : CxPts q σ → ℝ), IsDens ρ → IsDens g → Measurable f → (∀ u ∈ c.e.target, ∫ x : Low r → ℂ, ρ c' (c'.e.symm (pt ε u x)) = g c (c.e.symm u)) → ∀ A : Set (CxPts q σ), MeasurableSet A → A ⊆ c.e.source → (∫⁻ y in PtsOver.map π w (spMap σ) ⁻¹' A, ENNReal.ofReal |f (PtsOver.map π w (spMap σ) y)| ∂part ρ) ≠ ⊤ → (∫⁻ y in PtsOver.map π w (spMap σ) ⁻¹' A, ENNReal.ofReal |f (PtsOver.map π w (spMap σ) y)| ∂part fun c y => -ρ c y) ≠ ⊤ → ((∫⁻ y in PtsOver.map π w (spMap σ) ⁻¹' A, ENNReal.ofReal (f (PtsOver.map π w (spMap σ) y)) ∂part ρ) + (∫⁻ y in PtsOver.map π w (spMap σ) ⁻¹' A, ENNReal.ofReal (-f (PtsOver.map π w (spMap σ) y)) ∂part fun c y => -ρ c y) + ((∫⁻ u in A, ENNReal.ofReal (f u) ∂part fun c y => -g c y) + ∫⁻ u in A, ENNReal.ofReal (-f u) ∂part g) = (∫⁻ y in PtsOver.map π w (spMap σ) ⁻¹' A, ENNReal.ofReal (f (PtsOver.map π w (spMap σ) y)) ∂part fun c y => -ρ c y) + (∫⁻ y in PtsOver.map π w (spMap σ) ⁻¹' A, ENNReal.ofReal (-f (PtsOver.map π w (spMap σ) y)) ∂part ρ) + ((∫⁻ u in A, ENNReal.ofReal (f u) ∂part g) + ∫⁻ u in A, ENNReal.ofReal (-f u) ∂part fun c y => -g c y)) ∧ (∫⁻ u in A, ENNReal.ofReal |f u| ∂part g) + (∫⁻ u in A, ENNReal.ofReal |f u| ∂part fun c y => -g c y) ≤ (∫⁻ y in PtsOver.map π w (spMap σ) ⁻¹' A, ENNReal.ofReal |f (PtsOver.map π w (spMap σ) y)| ∂part ρ) + ∫⁻ y in PtsOver.map π w (spMap σ) ⁻¹' A, ENNReal.ofReal |f (PtsOver.map π w (spMap σ) y)| ∂part fun c y => -ρ c y := by
  first | exact @GlobalTheory.FubIdent.cell_balance | exact GlobalTheory.FubIdent.cell_balance | (intros; apply GlobalTheory.FubIdent.cell_balance <;> assumption)
