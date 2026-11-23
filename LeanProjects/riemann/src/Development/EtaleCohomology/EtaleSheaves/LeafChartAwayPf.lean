import Development.EtaleCohomology.EtaleSheaves.LeafChartPf

open CategoryTheory AlgebraicGeometry

namespace LateralTheory.E.LeafChartAwayPf

theorem LeafChartAway_of : LateralTheory.E.LeafChartPf.LeafChartAway := by
  intro X Y B _ j _ I g hj
  let f := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g)))
  have hf : ∀ y : Spec (CommRingCat.of (Localization.Away g)),
      f y = PrimeSpectrum.comap (algebraMap B (Localization.Away g)) y := fun _ => rfl
  refine ⟨f ≫ j, inferInstance, ?_, ?_, ?_⟩
  · rintro _ ⟨y', rfl⟩
    exact ⟨f y', rfl⟩
  · intro y hy
    have hmem : (show PrimeSpectrum B from y) ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away g))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact hy
    obtain ⟨y', hy'⟩ := hmem
    refine ⟨y', ?_⟩
    show j (f y') = j y
    exact congrArg j ((hf y').trans hy')
  · intro y'
    change j (f y') ∈ Y ↔ _
    rw [hj, hf, Ideal.map_le_iff_le_comap]
    rfl

end LateralTheory.E.LeafChartAwayPf
