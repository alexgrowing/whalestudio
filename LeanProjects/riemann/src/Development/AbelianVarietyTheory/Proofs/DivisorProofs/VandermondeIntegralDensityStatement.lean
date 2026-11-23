import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeIntegralDensity
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
theorem _root_.GlobalTheory.T.vandermonde_integral_density : ∀ r e : ℕ, ∃ t : ℝ, ∀ (D : ℕ) (ε : Fin D ≃ Fin (e + 2) ⊕ Low r) (G : V (e + 2) → Matrix (Fin r) (Fin r) ℂ) (ψ : V (e + 2) → ℝ) (u : V (e + 2)), MContDiffAt ∞ G u → (∀ᶠ v in 𝓝 u, (G v).PosDef) → ContDiffAt ℝ 2 ψ u → ∀ (I : Type) [Fintype I] (c : I → ℝ) (m : I → Option (Fin r) → ℤ), ∑ j, c j • lin (fun o => (m j o : ℝ)) ^ D = vdmPol r e → ∫ x : Low r → ℂ, ∑ j, c j * (D.factorial / Real.pi ^ D * (∑ o : Option (Fin r), (m j o : ℂ) • cHess D (fun v => ((o.elim (ψ (base ε v)) (fun i => rootWt ε G i v) : ℝ) : ℂ)) (pt ε u x)).det.re) = t * secondChernDensity e (chTwo G u) (cHess (e + 2) (fun v => (ψ v : ℂ)) u) := by
  first | exact @GlobalTheory.FlagMoment.fibre_integral | exact GlobalTheory.FlagMoment.fibre_integral | (intros; apply GlobalTheory.FlagMoment.fibre_integral <;> assumption)
