import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductTorusFactorAppellHumbert
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianUniformizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundleStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_torus_factor_appell_humbert : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L₀ : LB A.left) (g : ℕ) (u : HolUnif A L₀ g)
    (L : LB (A ⊗ A).left), L.IsLB → HasGen (L.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
    ∀ (U : HolUnif (A ⊗ A) L (g + g)) (H : Matrix (Fin (g + g)) (Fin (g + g)) ℂ) (χ' : U.Λ → ℂ),
    (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) → GlobalTheory.TorusRM.IsFactorAH U H χ' →
    (∀ z w : Fin g → ℂ, hermForm H (Fin.append z 0) (Fin.append w 0) = 0) →
    ∀ (m : U.Λ) (l : Fin g → ℂ), (m : Fin (g + g) → ℂ) = Fin.append l 0 → χ' m = 1 := by
  first | exact @GlobalTheory.TorusRM.char_axis_eq_one_of_herm_axis_zero | exact GlobalTheory.TorusRM.char_axis_eq_one_of_herm_axis_zero | (intros; apply GlobalTheory.TorusRM.char_axis_eq_one_of_herm_axis_zero <;> assumption)
