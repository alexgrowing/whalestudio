import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEqMulOfContinuousOnQuotient
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_eq_mul_of_valAt'_eq_continuous_mul : ∀ (P : Out.PolAV (Sp ℂ)) (L : LB P.A.left) (u : HolUnif P.A L P.g) (U : P.A.left.Opens) (a b : Γ(P.A.left, U)) (φ : (Fin P.g → ℂ) → ℂ), Out.Laws → IsAffineOpen U → b ≠ 0 → ContinuousOn φ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} → (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → valAt' (u.ex z).left U a = φ z * valAt' (u.ex z).left U b) → ∃ c : Γ(P.A.left, U), a = c * b := by
  first | exact @GlobalTheory.exists_eq_mul_of_continuousOn_quotient | exact GlobalTheory.exists_eq_mul_of_continuousOn_quotient | (intros; apply GlobalTheory.exists_eq_mul_of_continuousOn_quotient <;> assumption)
