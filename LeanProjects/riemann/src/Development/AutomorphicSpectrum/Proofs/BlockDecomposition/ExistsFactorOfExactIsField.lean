import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialActionSecondFactor
open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx GlobalTheory.CompanionTheory.HopfLe

namespace GlobalTheory.CompanionTheory.HopfLe

theorem exists_factor_of_exact_field {K A B D : Type} [Field K] [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup D] [Module K D]
    (f : A →ₗ[K] B) (g : B →ₗ[K] D) (hfg : Function.Exact f g) (μ : B →ₗ[K] K)
    (hμ : ∀ a, μ (f a) = 0) : ∃ ρ : D →ₗ[K] K, μ = ρ ∘ₗ g := by
  have hle : LinearMap.ker g ≤ LinearMap.ker μ := by
    intro b hb
    obtain ⟨a, rfl⟩ := (hfg b).1 hb
    exact hμ a
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_extend
    ((LinearMap.ker g).liftQ μ hle ∘ₗ (g.quotKerEquivRange.symm : LinearMap.range g →ₗ[K] B ⧸ LinearMap.ker g))
  refine ⟨ρ, LinearMap.ext fun b => ?_⟩
  have hb := LinearMap.congr_fun hρ ⟨g b, LinearMap.mem_range_self g b⟩
  calc μ b = (LinearMap.ker g).liftQ μ hle ((LinearMap.ker g).mkQ b) := by
        rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
    _ = (LinearMap.ker g).liftQ μ hle
          (g.quotKerEquivRange.symm ⟨g b, LinearMap.mem_range_self g b⟩) := by
        rw [LinearMap.quotKerEquivRange_symm_apply_image]
    _ = ρ (g b) := hb.symm

theorem exists_factor_of_exact_isField {K A B D : Type} [CommRing K] (hK : IsField K)
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B] [AddCommGroup D] [Module K D]
    (f : A →ₗ[K] B) (g : B →ₗ[K] D) (hfg : Function.Exact f g) (μ : B →ₗ[K] K)
    (hμ : ∀ a, μ (f a) = 0) : ∃ ρ : D →ₗ[K] K, μ = ρ ∘ₗ g := by
  letI := hK.toField
  exact exists_factor_of_exact_field f g hfg μ hμ

theorem exists_rho_of_exact {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (hR : IsField R)
    (hex : Function.Exact (Algebra.linearMap R (Cn F 0)) (dn F 0))
    (ν ν₀ : Cn F 0 →ₗ[R] R) (h1 : ν₀ 1 = 1) :
    ∃ ρ : Cn F 1 →ₗ[R] R, ν = ν 1 • ν₀ + ρ ∘ₗ dn F 0 := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.CompanionTheory.HopfLe.exists_factor_of_exact_isField hR _ _ hex (ν - ν 1 • ν₀) (by
    intro r
    simp only [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, LinearMap.sub_apply,
      LinearMap.smul_apply, map_smul, h1, smul_eq_mul, mul_one]
    ring)
  refine ⟨ρ, ?_⟩
  rw [← hρ]
  abel

end GlobalTheory.CompanionTheory.HopfLe
