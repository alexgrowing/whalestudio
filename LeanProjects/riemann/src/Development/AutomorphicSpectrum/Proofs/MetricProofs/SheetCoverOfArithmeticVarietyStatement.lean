import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetCoverOfArithmeticVariety
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheet_cover_of_arithmetic_variety : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (n nc : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : Fin nc → GroundTheory.Heights₂.Heights.LowerBoundFree.SncChart P n Bd) (V B : ℕ → Set (Fin n → ℂ)) (γ : ℕ → (Fin n → ℂ) → (Σ k, J k) → ℂ) (A : HermLine J) (G : ((Σ k, J k) → ℂ) → ℝ), IsArithVar P (n + 1) → (∀ z ∈ mcPts P, ∃ a, ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ z ∈ torusSat {(χ a).γ t}) → IsSheetCover χ V B γ → (∀ m, ContDiffOn ℝ 2 (fun t => Real.log (A.h (γ m t))) (V m)) → (∀ w ∈ mcPts P \ Bd, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, IntegrableOn (fun t => G (γ m t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ m t'))) t) (B m)) → Summable (fun m => ∫ t in B m, |G (γ m t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ m t'))) t|) → ptsIntegral (e := n) P (fun _ z => Real.log (A.h z)) G = ∑' m, ∫ t in B m, G (γ m t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ m t'))) t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_sheets | exact GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_sheets | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_sheets <;> assumption)
