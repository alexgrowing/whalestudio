import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivisorDescentModUnramifiedGaloisSubmodule
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_descent_mod_unramified_galois_submodule : ∀ (A₀ R K₀ L : Type) [CommRing A₀] [IsDedekindDomain A₀] [CommRing R] [IsDedekindDomain R] [Field K₀] [Field L]
  [Algebra A₀ K₀] [IsFractionRing A₀ K₀] [Algebra R L] [IsFractionRing R L] [Algebra A₀ R] [Algebra K₀ L] [Algebra A₀ L]
  [IsScalarTower A₀ R L] [IsScalarTower A₀ K₀ L] [IsIntegralClosure R A₀ L] [FiniteDimensional K₀ L] [IsGalois K₀ L]
  (N : ℕ), 0 < N →
  (∀ Q : Ideal R, Q.IsPrime → Q ≠ ⊥ → ¬ Ideal.map (algebraMap A₀ R) (Q.comap (algebraMap A₀ R)) ≤ Q ^ 2) →
  (∀ c : ClassGroup A₀, ∃ d, c = d ^ N) →
  ∀ w : L, w ≠ 0 → (∀ σ : L ≃ₐ[K₀] L, ∃ u : L, u ≠ 0 ∧ σ w = w * u ^ N) →
  ∃ (f : K₀) (J : Submodule R L), f ≠ 0 ∧ J ^ N = Submodule.span R {w / algebraMap K₀ L f} := by
  first | exact @GlobalTheory.DivisorDescent.descent_submodule | exact GlobalTheory.DivisorDescent.descent_submodule | (intros; apply GlobalTheory.DivisorDescent.descent_submodule <;> assumption)
