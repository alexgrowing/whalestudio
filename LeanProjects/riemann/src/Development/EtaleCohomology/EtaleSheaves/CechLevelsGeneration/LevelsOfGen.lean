import Development.EtaleCohomology.EtaleSheaves.CechLevels.CechLevelsOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LevelsPf
open LateralTheory.E.CechLevelsPf

theorem int_of_gen {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (hφ : φ.IsIntegral)
    (χ : A →+* B) {ι : Type} (l : ι → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ)
    (hc : Subring.closure (⋃ i, Set.range (l i)) = ⊤) : χ.IsIntegral := by
  let _ := χ.toAlgebra
  have hle : Subring.closure (⋃ i, Set.range (l i)) ≤ (integralClosure A B).toSubring := by
    rw [Subring.closure_le]
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨i, y, rfl⟩ := hx
    obtain ⟨p, hm, hp⟩ := hφ y
    refine ⟨p, hm, ?_⟩
    show Polynomial.eval₂ χ (l i y) p = 0
    rw [← hl i, ← Polynomial.hom_eval₂, hp, map_zero]
  intro b
  have : b ∈ (integralClosure A B).toSubring := hle (hc ▸ Subring.mem_top b)
  exact this

def LevelsGen : Prop := ∀ (A A' : Type) [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A) (p : SimplexCategoryᵒᵖ),
  ∃ (B : Type) (_ : CommRing B) (χ : A →+* B) (ι : Type) (l : ι → (A' →+* B)), (∀ i, (l i).comp φ = χ) ∧
    Subring.closure (⋃ i, Set.range (l i)) = ⊤ ∧ Nonempty (Arrow.mk ((psi φ I).app p) ≅
      Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map χ))))))

theorem Levels_of_gen (hG : LevelsGen) : LateralTheory.E.CechLevelsPf.Levels := by
  intro A A' _ _ φ I hφ p
  obtain ⟨B, _, χ, ι, l, hl, hc, he⟩ := hG A A' φ I p
  exact ⟨B, inferInstance, χ, int_of_gen φ hφ χ l hl hc, he⟩

end LateralTheory.E.LevelsPf
