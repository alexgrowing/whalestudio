import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianThetaFactor
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitian_theta_factor : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB →
    ∀ (g : ℕ) (u : HolUnif A L g), ∃ (u' : HolUnif A L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u'.Λ → ℂ),
      u'.ex = u.ex ∧ Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧
      ∀ (l : u'.Λ) i z, ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i →
        u'.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
          Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u'.fr i (z + l) := by
  first | exact @GlobalTheory.exists_appellHumbert_frame_of_isLB | exact GlobalTheory.exists_appellHumbert_frame_of_isLB | (intros; apply GlobalTheory.exists_appellHumbert_frame_of_isLB <;> assumption)
