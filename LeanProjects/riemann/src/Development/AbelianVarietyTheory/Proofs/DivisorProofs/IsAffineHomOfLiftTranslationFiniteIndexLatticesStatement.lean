import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfLiftTranslationFiniteIndexLattices
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
theorem _root_.GlobalTheory.T.isAffineHom_of_lift_translation_finiteIndex_lattices : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (B : Over (Sp ℂ)) [GrpObj B], IsAbelianScheme B →
    ∀ (L : LB A.left) (L' : LB B.left) (u : HolUnif A L g) (u' : HolUnif B L' g) (a : Fin g → ℂ) (N : ℕ),
    0 < N → u.Λ ≤ u'.Λ → (∀ x ∈ u'.Λ, N • x ∈ u.Λ) →
    ∀ ψ : A.left ⟶ B.left, ψ ≫ B.hom = A.hom → (∀ z, (u.ex z).left ≫ ψ = (u'.ex (z + a)).left) → IsAffineHom ψ := by
  first | exact @GlobalTheory.LiftAffine.isAffineHom_of_lift | exact GlobalTheory.LiftAffine.isAffineHom_of_lift | (intros; apply GlobalTheory.LiftAffine.isAffineHom_of_lift <;> assumption)
