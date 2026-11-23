import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalAnisotropicPairPlaneMatricesFacts
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbUnitary
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalAnisotropicPair_planeMatrices_facts : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → σ (hE σ J e₁ e₁) = hE σ J e₁ e₁ ∧ σ (hE σ J e₂ e₂) = hE σ J e₂ e₂ ∧ planeB σ J e₁ e₂ * planeA e₁ e₂ = 1 ∧ Formalism.UG.cT (σ : E →+* E) (planeA e₁ e₂) * J = planeH σ J e₁ e₂ * planeB σ J e₁ e₂ ∧ J * planeA e₁ e₂ = Formalism.UG.cT (σ : E →+* E) (planeB σ J e₁ e₂) * planeH σ J e₁ e₂ ∧ ∀ v : Fin M → E, (planeB σ J e₁ e₂).mulVec v = 0 ↔ (hE σ J e₁ v = 0 ∧ hE σ J e₂ v = 0) := by
  first | exact @GlobalTheory.PlaneSU.planeB_facts | exact GlobalTheory.PlaneSU.planeB_facts | (intros; apply GlobalTheory.PlaneSU.planeB_facts <;> assumption)
