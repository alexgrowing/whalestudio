import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleIsomorphismLocalToGlobal
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bundle_isomorphism_local_to_global : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (j₁ j₂ : Fl g → Pt E g → ℂ), (∀ l ∈ stdLat g, ∀ P ∈ cov B g, j₁ l P ≠ 0) → (∀ b ∈ B, ∃ U : Set E, IsOpen U ∧ b ∈ U ∧ U ⊆ B ∧ ∃ φ, IsBundleIso U τ (stdLat g) j₁ j₂ φ) → ∃ φ, IsBundleIso B τ (stdLat g) j₁ j₂ φ ∧ ∀ b ∈ B, φ (zeroSec g b) = 1 := by
  first | exact @GlobalTheory.BundleIsoGlue.glue | exact GlobalTheory.BundleIsoGlue.glue | (intros; apply GlobalTheory.BundleIsoGlue.glue <;> assumption)
