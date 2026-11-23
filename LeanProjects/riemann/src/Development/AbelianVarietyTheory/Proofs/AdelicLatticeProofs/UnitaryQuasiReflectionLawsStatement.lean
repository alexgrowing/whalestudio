import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryQuasiReflectionLaws
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryQuasiReflection_laws : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ x : Fin n → E, hermE c G x x ≠ 0 → (∀ u v, refl c G x u *ᵥ v = v + ((u - 1) * hermE c G v x / hermE c G x x) • x) ∧ refl c G x 1 = 1 ∧ (∀ u u', refl c G x u * refl c G x u' = refl c G x (u * u')) ∧ ∀ u, u * c u = 1 → IsUnE c G (refl c G x u) := by
  first | exact @GlobalTheory.UnRep.ReflLaws.refl_laws | exact GlobalTheory.UnRep.ReflLaws.refl_laws | (intros; apply GlobalTheory.UnRep.ReflLaws.refl_laws <;> assumption)
