import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormsAddOfFactorProduct
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
theorem _root_.GlobalTheory.T.hermitian_forms_add_of_factor_product : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M₁ M₂ M₃ : LB A.left) (u₁ : HolUnif A M₁ g) (u₂ : HolUnif A M₂ g) (u₃ : HolUnif A M₃ g)
      (H₁ H₂ H₃ : Matrix (Fin g) (Fin g) ℂ) (χ₁ : u₁.Λ → ℂ) (χ₂ : u₂.Λ → ℂ) (χ₃ : u₃.Λ → ℂ),
    M₁.IsLB → M₂.IsLB → M₃.IsLB → u₂.ex = u₁.ex → u₃.ex = u₁.ex →
    IsFactorAH u₁ H₁ χ₁ → IsFactorAH u₂ H₂ χ₂ → IsFactorAH u₃ H₃ χ₃ → H₃ = H₁ + H₂ →
    LBIso (abelian₂ A M₂) (LB.div (abelian₂ A M₃) (abelian₂ A M₁)) := by
  first | exact @GlobalTheory.TorusRM.lbIso_lam_of_add | exact GlobalTheory.TorusRM.lbIso_lam_of_add | (intros; apply GlobalTheory.TorusRM.lbIso_lam_of_add <;> assumption)
