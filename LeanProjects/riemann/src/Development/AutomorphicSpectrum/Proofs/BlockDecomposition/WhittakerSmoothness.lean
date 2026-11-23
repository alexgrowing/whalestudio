import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothOfTranslationLaw

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WhittakerSmooth

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem whittaker_invariant_under_fixing_subgroup (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) (φ : (Fin 2 → F) → ℂ)
    (u : GL (Fin 2) F) (hφ : GodementSectionLocal.rightTranslate u φ = φ)
    (hμ : μ₂ (GeneralLinearGroup.det u) = 1)
    (hm : GodementSectionLocal.modPow ((GeneralLinearGroup.det u : Fˣ) : F) (1 / 2) = 1)
    (g : GL (Fin 2) F) : W2 ψ μ₁ μ₂ φ (g * u) = W2 ψ μ₁ μ₂ φ g := by
  have hv : ∀ v : Fin 2 → F, φ (v ᵥ* ((g * u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) =
      φ (v ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) := by
    intro v
    rw [Units.val_mul, ← Matrix.vecMul_vecMul]
    exact congrFun hφ _
  have hmp : mp (GeneralLinearGroup.det (g * u)) (1 / 2) = mp (GeneralLinearGroup.det g) (1 / 2) := by
    change GodementSectionLocal.modPow ((GeneralLinearGroup.det (g * u) : Fˣ) : F) (1 / 2) =
      GodementSectionLocal.modPow ((GeneralLinearGroup.det g : Fˣ) : F) (1 / 2)
    rw [map_mul, Units.val_mul, GodementSectionLocal.modPow_mul, hm, mul_one]
  unfold W2
  rw [hmp, map_mul (GeneralLinearGroup.det) g u, map_mul μ₂, hμ, mul_one]
  simp only [hv]

theorem sSmooth : Ad3.SchwartzSpaceL2.SSmooth := by
  intro F _ _ _ _ _ _ ψ _ μ₁ μ₂ _ hμ₂ φ hφ
  obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.GodementFix.exists_congruence_fix hμ₂.1 hφ
  refine ⟨⟨GLnLocal.congruenceSubgroup F 2 m, GLnLocal.isOpen_congruenceSubgroup F 2 m⟩,
    fun g u hu ↦ ?_⟩
  obtain ⟨h1, h2, h3⟩ := hm u hu
  exact whittaker_invariant_under_fixing_subgroup ψ μ₁ μ₂ φ u h1 h2 (h3 _) g

end GlobalTheory.CompanionTheory.WhittakerSmooth
