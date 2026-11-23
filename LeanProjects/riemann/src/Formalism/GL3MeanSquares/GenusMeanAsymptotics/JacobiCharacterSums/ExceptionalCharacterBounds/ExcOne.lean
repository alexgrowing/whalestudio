import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower

open Formalism.ZeroFreeDirichlet

noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP

theorem excOne : ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 20 ∧
    ∀ (m : ℕ) [NeZero m], ∃ B : DirichletCharacter ℂ m → Finset ℝ,
      (∀ χ, ExcZeros c₁ χ (B χ)) ∧
      (∀ χ χ', (B χ).Nonempty → (B χ').Nonempty → χ = χ') ∧
      (∀ χ, ∀ β ∈ B χ, χ ^ 2 = 1 ∧ χ ≠ 1 ∧ 1 / 2 ≤ β ∧
        DirichletCharacter.LFunction χ (β : ℂ) = 0) := by
  obtain ⟨cZ, hcZ, hZ⟩ := zFRDirichlet
  refine ⟨min cZ (1 / 20), lt_min hcZ (by norm_num), min_le_right _ _, fun m _ => ?_⟩
  have hex := fun χ : DirichletCharacter ℂ m =>
    exists_exceptional_zero_set cZ (min cZ (1 / 20)) (min_le_left _ _) hZ m χ
  refine ⟨fun χ => Classical.choose (hex χ), fun χ => Classical.choose_spec (hex χ), ?_, ?_⟩
  · rintro χ χ' ⟨β, hβ⟩ ⟨β', hβ'⟩
    obtain ⟨h1, hreg, hz, _⟩ := (Classical.choose_spec (hex χ)).2.1 β hβ
    obtain ⟨h1', hreg', hz', _⟩ := (Classical.choose_spec (hex χ')).2.1 β' hβ'
    have := (hZ m χ β (zero_free_region_mono (min_le_left _ _) hreg) ⟨Or.inl h1, hz⟩).2.2.2.2 χ' β'
      (zero_free_region_mono (min_le_left _ _) hreg') ⟨Or.inl h1', hz'⟩
    exact this.1.symm
  · intro χ β hβ
    obtain ⟨h1, hreg, hz, _⟩ := (Classical.choose_spec (hex χ)).2.1 β hβ
    have hZ1 := hZ m χ β (zero_free_region_mono (min_le_left _ _) hreg) ⟨Or.inl h1, hz⟩
    exact ⟨hZ1.1, h1, half_le_of_real_in_region (min_le_right _ _) hreg, hz⟩

end Formalism.HermitianLattices.Ext.SupplyAP
