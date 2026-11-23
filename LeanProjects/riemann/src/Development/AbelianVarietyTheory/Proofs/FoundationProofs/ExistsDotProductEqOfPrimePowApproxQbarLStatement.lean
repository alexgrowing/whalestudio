import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDotProductEqOfPrimePowApproxQbarL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfForallNormLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dotProduct_eq_of_primePow_approx_qbarL : ∀ (l : ℕ) [Fact l.Prime] (X : Type) (m : ℕ) (M : X → Fin m → Qbar l) (z : X → Qbar l), (∀ n : ℕ, ∃ y : Fin m → Qbar l, ∀ x, ‖z x - M x ⬝ᵥ y‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖) → ∃ y : Fin m → Qbar l, ∀ x, z x = M x ⬝ᵥ y := by
  first | exact @GlobalTheory.exists_dotProduct_eq_of_approx_prime_pow | exact GlobalTheory.exists_dotProduct_eq_of_approx_prime_pow | (intros; apply GlobalTheory.exists_dotProduct_eq_of_approx_prime_pow <;> assumption)
