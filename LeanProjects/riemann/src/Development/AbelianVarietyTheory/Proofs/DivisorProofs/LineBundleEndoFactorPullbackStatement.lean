import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleEndoFactorPullback
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
theorem _root_.GlobalTheory.T.line_bundle_endo_factor_pullback : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (f : A ⟶ A),
    M.IsLB → IsFactorAH u Hm χ →
    ∀ (M' : LB A.left) (u' : HolUnif A M' g) (Hm' : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ) (α : A ⟶ A),
    M'.IsLB → u'.IsAH Hm' χ' → IsMonHom α → LBIso (abelian₂ A M') ((abelian₂ A M).pull (lift (fst A A) (snd A A ≫ α)).left) →
    (∀ w, (∀ l ∈ u.Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n) → u.ex w ≫ f = 1) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → x ≫ f = 1 := by
  first | exact @GlobalTheory.TorusRM.comp_eq_one_of_lam_triv_of_pull_pos | exact GlobalTheory.TorusRM.comp_eq_one_of_lam_triv_of_pull_pos | (intros; apply GlobalTheory.TorusRM.comp_eq_one_of_lam_triv_of_pull_pos <;> assumption)
