import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RayClassFieldInfModulusEqSup
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.RayPrincipalIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassField_inf_modulus_eq_sup : ∀ {K H H₁ H₂ : Type} [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] [IsAbelianGalois K H] [Field H₁] [NumberField H₁] [Algebra K H₁] [IsAbelianGalois K H₁] [Field H₂] [NumberField H₂] [Algebra K H₂] [IsAbelianGalois K H₂], (∀ u : (𝓞 K)ˣ, u = 1 ∨ u = -1) → ∀ {𝔞 𝔟 : Ideal (𝓞 K)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → ∀ {q : ℕ}, q.Prime → q ≠ 2 → 𝔞 ≤ Ideal.span {(q : 𝓞 K)} → 𝔟 ≤ Ideal.span {(q : 𝓞 K)} → GlobalTheory.FieldSize.IsRay H (𝔞 ⊓ 𝔟) → GlobalTheory.FieldSize.IsRay H₁ 𝔞 → GlobalTheory.FieldSize.IsRay H₂ 𝔟 → ∀ (f₁ : H₁ →ₐ[K] H) (f₂ : H₂ →ₐ[K] H), f₁.fieldRange ⊔ f₂.fieldRange = ⊤ := by
  first | exact @GlobalTheory.RayCompositum.fieldRange_sup_eq_top | exact GlobalTheory.RayCompositum.fieldRange_sup_eq_top | (intros; apply GlobalTheory.RayCompositum.fieldRange_sup_eq_top <;> assumption)
