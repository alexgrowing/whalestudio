import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHeightOnePrimeIntegralClosureIffDvdIrreducibl
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_heightOne_prime_integralClosure_iff_dvd_irreducible : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (Q : Ideal B), Q.IsPrime → Q.height = 1 → ∀ (t : A), Irreducible t → (∀ b : B, (b : K) = algebraMap F K t → b ∈ Q) → ∀ (a : A) (b : B), (b : K) = algebraMap F K a → (b ∈ Q ↔ t ∣ a) := by
  first | (exact @GlobalTheory.JacVal.mem_iff_dvd_of_height_one) | (exact GlobalTheory.JacVal.mem_iff_dvd_of_height_one) | (intros; apply GlobalTheory.JacVal.mem_iff_dvd_of_height_one  <;> assumption)
