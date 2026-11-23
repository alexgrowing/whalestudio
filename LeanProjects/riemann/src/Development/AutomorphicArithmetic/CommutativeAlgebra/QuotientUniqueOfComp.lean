import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorModuliObjectPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackAbelianMapUniqueStatement
open CategoryTheory UpperTheory.Gal.Int.Geo

theorem UpperTheory.quotient_unique_of_comp :
    QComp → QUniq := by
  intro hQ q _ D R R' _ _ _ b gb N N₀ c h3 hc X X₁ s s₁ o u f n n'
  obtain ⟨u', ⟨m⟩⟩ := GlobalTheory.T.exists_harrisTaylorModuliObject_pullback q D R b N₀ X₁ X s₁ (f ≫ s₁) f rfl u

  have down : ∀ k : QMap o u f c, ∃ k₁ : QMap o u' (𝟙 X) c, k.φ = k₁.φ ≫ m.φ := by
    intro k
    obtain ⟨k₀, hk⟩ : ∃ k₀ : QMap o u (𝟙 X ≫ f) c, k₀.φ = k.φ := by
      rw [Category.id_comp]
      exact ⟨k, rfl⟩
    obtain ⟨k₁, h₁⟩ := (hQ q D R R' b gb N N₀ c X X X₁ s (f ≫ s₁) s₁ o u' u (𝟙 X) f).2.1 k₀ m
    exact ⟨k₁, hk ▸ h₁⟩
  obtain ⟨n₁, h₁⟩ := down n
  obtain ⟨n₂, h₂⟩ := down n'

  have self : ∀ k : QMap o u' (𝟙 X) c, ∃ a : GlobalTheory.UPel.HT.ObjMap u' u' (𝟙 X), k.φ = n₁.φ ≫ a.φ := by
    intro k
    obtain ⟨k₀, hk⟩ : ∃ k₀ : QMap o u' (𝟙 X ≫ 𝟙 X) c, k₀.φ = k.φ := by
      rw [Category.id_comp]
      exact ⟨k, rfl⟩
    obtain ⟨a₀, ha₀⟩ : ∃ a : GlobalTheory.UPel.HT.ObjMap u' u' (𝟙 X), k₀.φ = n₁.φ ≫ a.φ :=
      (hQ q D R R' b gb N N₀ c X X X s (f ≫ s₁) (f ≫ s₁) o u' u' (𝟙 X) (𝟙 X)).2.2.1
        inferInstance n₁ k₀
    exact ⟨a₀, hk ▸ ha₀⟩
  obtain ⟨a, ha⟩ := self n₁
  obtain ⟨a', ha'⟩ := self n₂
  have hr : a.φ = a'.φ := GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique q D R b N₀ h3 hc X X (f ≫ s₁) (f ≫ s₁) u' u' (𝟙 X) a a'
  rw [h₁, h₂, ha', ← hr, ← ha]
