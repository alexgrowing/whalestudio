import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityPushforwardIntegral
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
theorem _root_.GlobalTheory.T.density_pushforward_integral : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (n r D : ℕ) (ε : Fin D ≃ Fin n ⊕ Low r) (σ : k →+* ℂ) [IsIntegral B] [IsIntegral Y], IsArithVar q n → IsArithVar p D → π (genericPoint Y) = genericPoint B → ∀ (ρ : AlgChart p σ D → CxPts p σ → ℝ) (g : AlgChart q σ n → CxPts q σ → ℝ) (f : CxPts q σ → ℝ), IsDens ρ → IsDens g → Measurable f → IntegrableDens ρ (fun y => f (PtsOver.map π w (spMap σ) y)) → (∀ (c₀ : AlgChart q σ n), ∀ y ∈ c₀.e.source, ∃ (c : AlgChart q σ n) (c' : AlgChart p σ D), y ∈ c.e.source ∧ IsCell ε π w c c' ∧ ∀ u ∈ c.e.target, ∫ x : Low r → ℂ, ρ c' (c'.e.symm (pt ε u x)) = g c (c.e.symm u)) → densInt ρ (fun y => f (PtsOver.map π w (spMap σ) y)) = densInt g f := by
  first | exact @GlobalTheory.ArchLim.densInt_pull_eq_of_cells | exact GlobalTheory.ArchLim.densInt_pull_eq_of_cells | (intros; apply GlobalTheory.ArchLim.densInt_pull_eq_of_cells <;> assumption)
