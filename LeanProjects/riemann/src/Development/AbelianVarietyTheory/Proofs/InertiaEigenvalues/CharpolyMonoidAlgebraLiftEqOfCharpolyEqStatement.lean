import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyMonoidAlgebraLiftEqOfCharpolyEq
import Mathlib
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_monoidAlgebraLift_eq_of_charpoly_eq : ∀ {k G : Type} [Field k] [Monoid G] (n : ℕ) (ρ σ : G →* Matrix (Fin n) (Fin n) k), (∀ g, (ρ g).charpoly = (σ g).charpoly) → ∀ a : MonoidAlgebra k G, (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G ρ a).charpoly = (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G σ a).charpoly := by
  first | exact @GlobalTheory.charpoly_lift_eq_of_charpoly_eq | exact GlobalTheory.charpoly_lift_eq_of_charpoly_eq | (intros; apply GlobalTheory.charpoly_lift_eq_of_charpoly_eq <;> assumption)
