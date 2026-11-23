import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMixCurvatureLimit
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
theorem _root_.GlobalTheory.T.graded_mix_curvature_limit : ∀ {n m : ℕ} (H₀ H : V n → Matrix (Fin m) (Fin m) ℂ) (ρ : V n → ℝ) (u : V n),
    (∀ i k, ContDiffAt ℝ 2 (fun v => H₀ v i k) u) → (∀ i k, ContDiffAt ℝ 2 (fun v => H v i k) u) →
    ContDiffAt ℝ 2 ρ u → IsUnit (H₀ u).det → IsUnit (H u).det → ∀ ξ η : V n,
    Tendsto (fun c : ℝ => curv (fun v => GlobalTheory.GradedNorm.mix (1 / (1 + c * ρ v)) (H₀ v) (H v)) u ξ η) (𝓝 0)
        (𝓝 (curv H u ξ η)) ∧
      Tendsto (fun c : ℝ => curv (fun v => GlobalTheory.HermFrame.dualGram (GlobalTheory.GradedNorm.mix (1 / (1 + c * ρ v))
        (GlobalTheory.HermFrame.dualGram (H₀ v)) (GlobalTheory.HermFrame.dualGram (H v)))) u ξ η) (𝓝 0) (𝓝 (curv H u ξ η)) := by
  first | exact @GlobalTheory.CurvJet.tendsto_curv_mix | exact GlobalTheory.CurvJet.tendsto_curv_mix | (intros; apply GlobalTheory.CurvJet.tendsto_curv_mix <;> assumption)
