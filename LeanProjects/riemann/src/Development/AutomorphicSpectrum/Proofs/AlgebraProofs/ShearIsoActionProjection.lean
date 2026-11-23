import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreeHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

noncomputable section

namespace GlobalTheory.CompanionTheory.FreeQuotProof

theorem action_eq_fst_smul_snd {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] :
    (γ[G, X] : G ⊗ X ⟶ X) = (fst G X) • (snd G X) := by
  rw [CategoryTheory.Hom.smul_def, lift_fst_snd, Category.id_comp]

theorem exists_iso_swap_action_snd : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X], ∃ σ : G ⊗ X ⟶ G ⊗ X, IsIso σ ∧ σ ≫ snd G X = γ[G, X] ∧ σ ≫ γ[G, X] = snd G X := by
  intro S G X _ _
  have hγ : (γ[G, X] : G ⊗ X ⟶ X) = fst G X • snd G X := GlobalTheory.CompanionTheory.FreeQuotProof.action_eq_fst_smul_snd G X
  obtain ⟨σ, h₁, h₂⟩ : ∃ σ : G ⊗ X ⟶ G ⊗ X,
      σ ≫ snd G X = fst G X • snd G X ∧ σ ≫ fst G X = (fst G X)⁻¹ :=
    ⟨lift (fst G X)⁻¹ (fst G X • snd G X), lift_snd _ _, lift_fst _ _⟩
  have h₃ : σ ≫ (fst G X • snd G X) = snd G X := by
    rw [CategoryTheory.ModObj.comp_smul, h₂, h₁, inv_smul_smul]
  have h₄ : σ ≫ σ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, h₂, CategoryTheory.Hom.inv_def, ← Category.assoc, h₂,
        ← CategoryTheory.Hom.inv_def, inv_inv, Category.id_comp]
    · rw [Category.assoc, h₁, h₃, Category.id_comp]
  exact ⟨σ, ⟨σ, h₄, h₄⟩, by rw [hγ]; exact h₁, by rw [hγ]; exact h₃⟩

end GlobalTheory.CompanionTheory.FreeQuotProof
