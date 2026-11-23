import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothFunctionalOrbitSmoothVector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarCompactLtTop
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_functional_orbit_smoothVector : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (σ : Mat k r → (H →L[ℂ] H)) (Λ : H →L[ℂ] B), IsURepOn (GG k r) σ → ∀ v : H, IsSmoothVec (k := k) (r := r) σ v → SmoothOnH (Hpk k r) (fun g : Mat k r => Λ (σ g v)) ∧ ∀ ws : List (Mat k r), (∀ X ∈ ws, InLieHpk k r X) → ∀ x ∈ GG k r, rdWord ws (fun g : Mat k r => Λ (σ g v)) x = Λ (σ x (dsigW σ ws v)) := by
  first | exact @GlobalTheory.SgInfOrb.smooth_rdWord_functional | exact GlobalTheory.SgInfOrb.smooth_rdWord_functional | (intros; apply GlobalTheory.SgInfOrb.smooth_rdWord_functional <;> assumption)
