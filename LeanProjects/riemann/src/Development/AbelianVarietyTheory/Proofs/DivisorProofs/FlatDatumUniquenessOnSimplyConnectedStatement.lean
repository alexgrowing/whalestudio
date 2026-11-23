import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDatumUniquenessOnSimplyConnected
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFormCongrOfEventuallyEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelActionPreservesFlatForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapSymplecticTransform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapRigidity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricTranslationPullbackFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatCoordsSymplecticPullbackForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcCompHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteQuotientOfIsLatLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPeriodMapSimplyConnectedStatement
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_datum_uniqueness_on_simply_connected : IsometryInv → TranslationInv → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (g n : ℕ) (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ), SimplyConnectedSpace B → ∀ (M : Submodule ℤ (Fl g)), (∀ l ∈ M, ∀ l' ∈ M, ∃ k : ℤ, riem l l' = k) → ∀ (j₁ j₂ : Fl g → Pt E g → ℂ) (h₁ h₂ : Pt E g → ℝ), IsDatum B τ M j₁ h₁ → ChernIsFlat B τ h₁ → IsDatum B τ M j₂ h₂ → ChernIsFlat B τ h₂ → ∀ (β : Fin n → E), ∀ b ∈ B, ∀ T : Ext (n + n), IsTorsionForm τ M j₁ h₁ β b T → IsTorsionForm τ M j₂ h₂ β b T := by
  first | exact @GlobalTheory.TorsionForm.FlatSame.main | exact GlobalTheory.TorsionForm.FlatSame.main | (intros; apply GlobalTheory.TorsionForm.FlatSame.main <;> assumption)
