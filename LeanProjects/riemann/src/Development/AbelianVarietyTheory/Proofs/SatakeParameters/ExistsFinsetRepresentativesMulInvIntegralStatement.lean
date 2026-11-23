import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinsetRepresentativesMulInvIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_representatives_mul_inv_integral : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧ ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K) →
  ∀ (n n' : ℕ) (a : GL (Fin n) L) (x : Matrix (Fin n') (Fin n) L),
  (∀ i j, (x * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  ∃ Y : Finset (Matrix (Fin n') (Fin n) L), x ∈ Y ∧ (∀ y ∈ Y, ∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
    (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n → y = y') ∧
    ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ∃ y ∈ Y, u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - y ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n := by
  first | exact @GlobalTheory.Hk3.HoweDuality.exists_finset_reps_mul_inv | exact GlobalTheory.Hk3.HoweDuality.exists_finset_reps_mul_inv | (intros; apply GlobalTheory.Hk3.HoweDuality.exists_finset_reps_mul_inv <;> assumption)
