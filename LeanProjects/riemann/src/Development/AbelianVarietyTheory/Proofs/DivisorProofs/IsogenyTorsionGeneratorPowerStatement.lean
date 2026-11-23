import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyTorsionGeneratorPower
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
theorem _root_.GlobalTheory.T.isogeny_torsion_generator_power : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB →
    ∀ (P : Out.PolAV (Sp ℂ)) (ψ : A ⟶ P.A) (ρ : P.A ⟶ A) (N : ℕ), IsMonHom ψ → IsMonHom ρ →
      ψ ≫ ρ = (𝟙 A) ^ N → ρ ≫ ψ = (𝟙 P.A) ^ N →
      LBIso (abelian₂ A M) ((abelian₂ P.A P.L).pull (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → x ^ (N * N) = 1 := by
  first | exact @GlobalTheory.KillSquare.pow_sq_eq_one_of_lam_trivial | exact GlobalTheory.KillSquare.pow_sq_eq_one_of_lam_trivial | (intros; apply GlobalTheory.KillSquare.pow_sq_eq_one_of_lam_trivial <;> assumption)
