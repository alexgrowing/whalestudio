import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalApproximationsDifferByCongruentToOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TwU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalApproximations_differ_by_congruent_to_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g₁ g₂ : GL (Fin N) E), 0 < n → NearAt P n x g₁ → NearAt P n x g₂ → ∀ a b : Fin N, IntAt P ((((qOf P : ℕ) : E) ^ n)⁻¹ * (((g₁⁻¹ * g₂ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) a b) := by
  first | exact @GlobalTheory.TwU.CongTwo.intAt_inv_mul_of_nearAt | exact GlobalTheory.TwU.CongTwo.intAt_inv_mul_of_nearAt | (intros; apply GlobalTheory.TwU.CongTwo.intAt_inv_mul_of_nearAt <;> assumption)
