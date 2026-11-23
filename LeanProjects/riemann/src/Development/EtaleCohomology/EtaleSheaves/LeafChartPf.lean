import Development.EtaleCohomology.EtaleSheaves.LeafChartRing

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafChartPf

def LeafChartAff : Prop := ∀ {X Z S : Scheme.{0}} (p : X ⟶ S) (ι : Z ⟶ X) [IsClosedImmersion ι] (d e : ℕ)
  [SmoothOfRelativeDimension (e + d) p] [SmoothOfRelativeDimension e (ι ≫ p)] (x : X), x ∈ Set.range ι →
  ∀ W : X.Opens, x ∈ W → ∃ (A B : Type) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B) (I : Ideal B),
    Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B ∧
    Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) ∧
    ∃ (j : Spec (CommRingCat.of B) ⟶ X) (_ : IsOpenImmersion j), x ∈ Set.range j ∧ Set.range j ⊆ (W : Set X) ∧
      ∀ y : Spec (CommRingCat.of B), j y ∈ Set.range ι ↔ I ≤ (show PrimeSpectrum B from y).asIdeal

def LeafChartAway : Prop := ∀ {X : Scheme.{0}} (Y : Set X) (B : Type) [CommRing B] (j : Spec (CommRingCat.of B) ⟶ X)
  [IsOpenImmersion j] (I : Ideal B) (g : B),
  (∀ y : Spec (CommRingCat.of B), j y ∈ Y ↔ I ≤ (show PrimeSpectrum B from y).asIdeal) →
  ∃ (j' : Spec (CommRingCat.of (Localization.Away g)) ⟶ X) (_ : IsOpenImmersion j'), Set.range j' ⊆ Set.range j ∧
    (∀ y : Spec (CommRingCat.of B), g ∉ (show PrimeSpectrum B from y).asIdeal → j y ∈ Set.range j') ∧
    ∀ y' : Spec (CommRingCat.of (Localization.Away g)), j' y' ∈ Y ↔
      I.map (algebraMap B (Localization.Away g)) ≤ (show PrimeSpectrum (Localization.Away g) from y').asIdeal

theorem LeafChart_of (hR : LateralTheory.E.t_E6Cut.LeafChartRing) (hA : LeafChartAff) (hW : LeafChartAway) :
    LateralTheory.E.t_E6Cut.LeafChart := by
  intro X Z S p ι _ d e _ _ x hx W hxW
  obtain ⟨A, B, _, _, _, I, h1, h2, j, _, ⟨y0, rfl⟩, hjW, hj⟩ := hA p ι d e x hx W hxW
  have hI : I ≤ (show PrimeSpectrum B from y0).asIdeal := (hj y0).1 hx
  obtain ⟨g, hg, C, _, φ, het, heq⟩ :=
    hR d e A B I h1 h2 (show PrimeSpectrum B from y0).asIdeal inferInstance hI
  obtain ⟨j', hj', hsub, hcov, hiff⟩ := hW (Set.range ι) B j I g hj
  refine ⟨Localization.Away g, C, inferInstance, inferInstance, j', hj', φ, het, hcov y0 hg,
    hsub.trans hjW, fun y' => ?_⟩
  rw [hiff y', heq]

end LateralTheory.E.LeafChartPf
