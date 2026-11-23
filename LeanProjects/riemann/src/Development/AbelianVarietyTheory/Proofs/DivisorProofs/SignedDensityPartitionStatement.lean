import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignedDensityPartition
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
theorem _root_.GlobalTheory.T.densInt_tendsto_zero_of_dominated : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) [SecondCountableTopology (CxPts p σ)] (ρ : ℝ → AlgChart p σ D → CxPts p σ → ℝ) (f : ℝ → CxPts p σ → ℝ) (w : AlgChart p σ D → CxPts p σ → ℝ) (F : CxPts p σ → ℝ) (S : Set (CxPts p σ)), (∀ R, IsDens (ρ R)) → (∀ R, Measurable (f R)) → IsMDens w → Integrable F (part w) → MeasurableSet S → (∀ R, part (ρ R) Sᶜ = 0 ∧ part (fun c y => -ρ R c y) Sᶜ = 0) → (∀ y, 0 ≤ F y) → (∀ᶠ R in atTop, ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, y ∈ S → |f R y * ρ R c y| ≤ F y * w c y) → (∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, y ∈ S → Tendsto (fun R => f R y * ρ R c y) atTop (𝓝 0)) → Tendsto (fun R => densInt (ρ R) (f R)) atTop (𝓝 0) := by
  first | exact @GlobalTheory.ArchLim.tendsto_densInt_of_dominated | exact GlobalTheory.ArchLim.tendsto_densInt_of_dominated | (intros; apply GlobalTheory.ArchLim.tendsto_densInt_of_dominated <;> assumption)
