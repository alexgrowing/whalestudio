import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAlgebraicSectionOfHolomorphicTheta
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraic_section_of_holomorphic_theta : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (N : LB P.A.left) (u : HolUnif P.A N P.g) (ϑ : (Fin P.g → ℂ) → ℂ), N.IsLB → Differentiable ℂ ϑ → (∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ N.U i → ϑ (z + l) * u.fr i (z + l) = ϑ z * u.fr i z) → ∃ s : N.Sec, u.IsFn s ϑ := by
  first | exact @GlobalTheory.exists_sec_isFn_of_differentiable | exact GlobalTheory.exists_sec_isFn_of_differentiable | (intros; apply GlobalTheory.exists_sec_isFn_of_differentiable <;> assumption)
