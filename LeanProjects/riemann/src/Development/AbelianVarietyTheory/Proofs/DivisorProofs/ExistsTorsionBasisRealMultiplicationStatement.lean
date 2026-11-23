import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionBasisRealMultiplication
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_basis_real_multiplication : ∀ (F : Type) [Field F] [NumberField F] (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (rm : OAct (𝓞 F) A) (L : LB A.left) (u : HolUnif A L (Module.finrank ℚ F)) (Fa : 𝓞 F →+* Module.End ℂ (Fin (Module.finrank ℚ F) → ℂ)), (∀ (a : 𝓞 F) (z : Fin (Module.finrank ℚ F) → ℂ), u.ex (Fa a z) = u.ex z ≫ rm.act a) → ∀ N : ℕ, 1 ≤ N → ∃ pt : Fin 2 → (𝟙_ (Over (Sp ℂ)) ⟶ A), (∀ i, pt i ^ N = 1) ∧ (∀ a b : 𝓞 F, (pt 0 ≫ rm.act a) * (pt 1 ≫ rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧ ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ A, y ^ N = 1 → ∃ a b : 𝓞 F, y = (pt 0 ≫ rm.act a) * (pt 1 ≫ rm.act b) := by
  first | exact @GlobalTheory.TorsionPoints.exists_torsion_basis | exact GlobalTheory.TorsionPoints.exists_torsion_basis | (intros; apply GlobalTheory.TorsionPoints.exists_torsion_basis <;> assumption)
