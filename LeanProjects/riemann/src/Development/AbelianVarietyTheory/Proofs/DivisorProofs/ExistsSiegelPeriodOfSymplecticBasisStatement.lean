import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelPeriodOfSymplecticBasis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegel_period_of_symplectic_basis : ∀ (h : ℕ) (Hm : Matrix (Fin h) (Fin h) ℂ) (v : Fin h ⊕ Fin h → (Fin h → ℂ)), Hm.IsHermitian → (∀ z : Fin h → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ i j, (hermForm Hm (v i) (v j)).im = (omegaStd (Pi.single i 1 : Fin h ⊕ Fin h → ℤ) (Pi.single j 1) : ℝ)) → ∃ (τ : Matrix (Fin h) (Fin h) ℂ) (T : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ)), τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ ∀ a, T (per τ a) = ∑ i, a i • v i := by
  first | exact @GlobalTheory.RiemannRel.exists_siegel_of_symplectic | exact GlobalTheory.RiemannRel.exists_siegel_of_symplectic | (intros; apply GlobalTheory.RiemannRel.exists_siegel_of_symplectic <;> assumption)
