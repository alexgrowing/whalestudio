import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectPairingDualSymplectic
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfect_pairing_dual_symplectic : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    (N : Type 1) [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (g : ℕ),
    Module.Finite R N → Module.Projective R N → (∀ P : PrimeSpectrum R, Module.rankAtStalk N P = 2 * g) →
    ∀ b : M →ₗ[R] M →ₗ[R] R, b.IsPerfPair →
    ∀ φ : Module.Dual R N →ₗ[R] Module.Dual R N →ₗ[R] R,
      (∀ (x y : Module.Dual R N) (u v : M), (∀ w, x (e w) = b w u) → (∀ w, y (e w) = b w v) →
        φ x y = b u v) →
    ∀ S : Submodule R N, (∃ S' : Submodule R N, IsCompl S S') →
      (∀ P : PrimeSpectrum R, Module.rankAtStalk S P = g) →
      (∀ x y : Module.Dual R N, (∀ c ∈ S, x c = 0) → (∀ c ∈ S, y c = 0) → φ x y = 0) →
      ∀ u v : M, e u ∈ S → e v ∈ S → b u v = 0 := by
  first | exact @GlobalTheory.AnnIso.pairing_vanishes_of_annihilator_isotropic | exact GlobalTheory.AnnIso.pairing_vanishes_of_annihilator_isotropic | (intros; apply GlobalTheory.AnnIso.pairing_vanishes_of_annihilator_isotropic <;> assumption)
