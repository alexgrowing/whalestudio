import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorTrivializationExists
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_factor_trivialization_exists : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (j : Fl g → Pt E g → ℂ), IsFactor B τ (stdLat g) j → (∃ ι, IsBundleIso B τ (stdLat g) (mulPullFactor (-1) j) j ι) → InducesPolarisation B τ (stdLat g) j → ∀ b₀ ∈ B, ∃ U : Set E, IsOpen U ∧ b₀ ∈ U ∧ U ⊆ B ∧ ∃ (x : Fl g) (φ : Pt E g → ℂ), IsBundleIso U τ (stdLat g) (translPullFactor τ x (fun l P => Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2))) j φ := by
  first | exact @GlobalTheory.ThetaTranslateLocal.exists_local_theta_translate_iso | exact GlobalTheory.ThetaTranslateLocal.exists_local_theta_translate_iso | (intros; apply GlobalTheory.ThetaTranslateLocal.exists_local_theta_translate_iso <;> assumption)
