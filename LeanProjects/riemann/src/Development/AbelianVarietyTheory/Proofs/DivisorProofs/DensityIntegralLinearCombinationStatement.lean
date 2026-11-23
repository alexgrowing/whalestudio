import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityIntegralLinearCombination
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
theorem _root_.GlobalTheory.T.density_integral_linear_combination : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) [SecondCountableTopology (CxPts p σ)] (I : Type) [Fintype I] (c : I → ℝ) (ρ : I → AlgChart p σ D → CxPts p σ → ℝ) (f : CxPts p σ → ℝ), (∀ j, IsDens (ρ j)) → (∀ j, IntegrableDens (ρ j) f) → IntegrableDens (fun ch y => ∑ j, c j * ρ j ch y) f ∧ densInt (fun ch y => ∑ j, c j * ρ j ch y) f = ∑ j, c j * densInt (ρ j) f := by
  first | exact @GlobalTheory.DensLinear.densInt_sum | exact GlobalTheory.DensLinear.densInt_sum | (intros; apply GlobalTheory.DensLinear.densInt_sum <;> assumption)
