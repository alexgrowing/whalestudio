import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSubringIntegralClosureMax
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_subring_integral_closure_max : ∀ {K : Type} [Field K] (R D B : Subring K) [IsLocalRing R] [IsLocalRing D], R ≤ D → (∀ r ∈ R, r ≠ 0 → r⁻¹ ∈ D → r⁻¹ ∈ R) → (integralClosure R K).toSubring ≤ D → B ≤ (integralClosure R K).toSubring → (∀ a ∈ D, ∃ u ∈ B, ∃ v ∈ B, v ≠ 0 ∧ v⁻¹ ∈ D ∧ a = u / v) → ∃ (P : Ideal (integralClosure R K).toSubring) (_ : P.IsMaximal), D = (LocalSubring.ofPrime _ P).toSubring ∧ ∀ t : (integralClosure R K).toSubring, t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ D) := by
  first | exact @GlobalTheory.CompanionTheory.Domination.eq_localisation_integralClosure | exact GlobalTheory.CompanionTheory.Domination.eq_localisation_integralClosure | (intros; apply GlobalTheory.CompanionTheory.Domination.eq_localisation_integralClosure <;> assumption)
