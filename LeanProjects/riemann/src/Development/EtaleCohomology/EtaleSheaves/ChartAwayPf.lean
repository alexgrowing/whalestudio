import Development.EtaleCohomology.EtaleSheaves.LeafChartAffPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.ChartAwayPf

theorem ChartAway_of : LateralTheory.E.LeafChartAffPf.ChartAway := by
  intro X Y B _ j _ I g hj
  let f := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g)))
  have hf : ∀ y' : Spec (CommRingCat.of (Localization.Away g)),
      (show PrimeSpectrum B from f.base y') =
        PrimeSpectrum.comap (algebraMap B (Localization.Away g)) (show PrimeSpectrum _ from y') := fun _ => rfl
  refine ⟨f ≫ j, inferInstance, ?_, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨f.base y, rfl⟩
  · intro y hy
    have : (show PrimeSpectrum B from y) ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away g))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact hy
    obtain ⟨y', hy'⟩ := this
    refine ⟨y', ?_⟩
    show j.base (f.base y') = j.base y
    rw [show f.base y' = y from (hf y').trans hy']
  · intro y'
    show j.base (f.base y') ∈ Y ↔ _
    rw [hj (f.base y'), hf y', Ideal.map_le_iff_le_comap]
    rfl

end LateralTheory.E.ChartAwayPf
