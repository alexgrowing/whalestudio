import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertHomCompatible
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appell_humbert_hom_compatible : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M₁ M₂ : LB A.left) (u₁ : HolUnif A M₁ g) (u₂ : HolUnif A M₂ g) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ)
      (χ₁ : u₁.Λ → ℂ) (χ₂ : u₂.Λ → ℂ) (f : A ⟶ A) (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    M₁.IsLB → M₂.IsLB → u₂.ex = u₁.ex → IsFactorAH u₁ H₁ χ₁ → IsFactorAH u₂ H₂ χ₂ → IsMonHom f →
    (∀ z, u₁.ex (Fl z) = u₁.ex z ≫ f) →
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (Fl w))) →
    (∀ z w, Fl z ⬝ᵥ H₁.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (Fl w))) →
    LBIso (abelian₂ A M₂) ((abelian₂ A M₁).pull (lift (fst A A) (snd A A ≫ f)).left) := by
  first | exact @GlobalTheory.TorusRM.lbIso_lam_pull_of_selfAdjoint | exact GlobalTheory.TorusRM.lbIso_lam_pull_of_selfAdjoint | (intros; apply GlobalTheory.TorusRM.lbIso_lam_pull_of_selfAdjoint <;> assumption)
