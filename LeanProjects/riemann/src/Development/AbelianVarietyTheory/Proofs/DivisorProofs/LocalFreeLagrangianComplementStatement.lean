import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFreeLagrangianComplement
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_free_lagrangian_complement : ∀ (R : Type) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] (g : ℕ) (P : Submodule R M),
    (∃ N : Submodule R M, IsCompl P N) → Module.Finite R M → Module.Projective R M →
    (∀ q : PrimeSpectrum R, Module.rankAtStalk M q = 2 * g) →
    Module.Finite R P → Module.Projective R P → (∀ q : PrimeSpectrum R, Module.rankAtStalk P q = g) →
    ∀ q : PrimeSpectrum R, ∃ r : R, r ∈ q.asIdeal.primeCompl ∧
      ∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsLocalization.Away r R']
        (M' : Type*) [AddCommGroup M'] [Module R' M'] [Module R M'] [IsScalarTower R R' M']
        (f : M →ₗ[R] M'), IsLocalizedModule (Submonoid.powers r) f →
        ∃ c : Module.Basis (Fin (2 * g)) R' M',
          Submodule.span R' (f '' P) = Submodule.span R' (c '' {j | (j : ℕ) < g}) := by
  first | exact @GlobalTheory.AdaptedBasis.exists_adapted_basis_away | exact GlobalTheory.AdaptedBasis.exists_adapted_basis_away | (intros; apply GlobalTheory.AdaptedBasis.exists_adapted_basis_away <;> assumption)
