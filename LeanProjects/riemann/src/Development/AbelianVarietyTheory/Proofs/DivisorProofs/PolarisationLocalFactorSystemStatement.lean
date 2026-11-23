import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationLocalFactorSystem
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisation_local_factor_system : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ j : Fl g → Pt E g → ℂ, IsFactor B τ (stdLat g) j → InducesPolarisation B τ (stdLat g) j → ∀ b ∈ B, ∃ U : Set E, IsOpen U ∧ b ∈ U ∧ U ⊆ B ∧ ∃ χ : Fl g → E → ℂ, (∀ l ∈ stdLat g, DifferentiableOn ℂ (χ l) U ∧ ∀ b' ∈ U, χ l b' ≠ 0) ∧ (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ b' ∈ U, χ (l + l') b' = χ l b' * χ l' b') ∧ ∃ φ, IsBundleIso U τ (stdLat g) j (fun l P => Complex.exp (2 * π * Complex.I * thetaExp (τ P.1) l P.2) * χ l P.1) φ := by
  first | exact @GlobalTheory.FactorThetaChar.exists_iso_theta_mul_char | exact GlobalTheory.FactorThetaChar.exists_iso_theta_mul_char | (intros; apply GlobalTheory.FactorThetaChar.exists_iso_theta_mul_char <;> assumption)
