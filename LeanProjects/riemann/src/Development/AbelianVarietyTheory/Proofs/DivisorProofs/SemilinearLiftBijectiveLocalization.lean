import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
open GlobalTheory.DeRham TensorProduct

namespace GlobalTheory

theorem DeRham.localisation_of_liftSemi_bijective :
    ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (f : R) [IsLocalization.Away f R']
      {M M' : Type 1} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M']
      (ρ : M →ₛₗ[algebraMap R R'] M'), Function.Bijective (GlobalTheory.DeRham.liftSemi ρ) →
      (∀ m' : M', ∃ (n : ℕ) (x : M), algebraMap R R' f ^ n • m' = ρ x) ∧
        ∀ x : M, ρ x = 0 → ∃ n : ℕ, f ^ n • x = 0 := by
  intro R R' _ _ _ f _ M M' _ _ _ _ ρ hρ
  have hloc : IsLocalizedModule (Submonoid.powers f) (TensorProduct.mk R R' M 1) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) R' _).2
      (TensorProduct.isBaseChange R M R')
  refine ⟨fun m' ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := hρ.2 m'
    obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, h⟩ :=
      IsLocalizedModule.surj (Submonoid.powers f) (TensorProduct.mk R R' M 1) z
    refine ⟨n, x, ?_⟩
    have h' : (algebraMap R R' f ^ n) • z = (1 : R') ⊗ₜ[R] x := by
      rw [← map_pow, algebraMap_smul]
      exact h
    rw [← map_smul, h', liftSemi_tmul, one_smul]
  · have h0 : TensorProduct.mk R R' M 1 x = TensorProduct.mk R R' M 1 0 := by
      apply hρ.1
      simp [hx]
    obtain ⟨⟨_, n, rfl⟩, h⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) h0
    exact ⟨n, by simpa [Submonoid.smul_def] using h⟩

end GlobalTheory
