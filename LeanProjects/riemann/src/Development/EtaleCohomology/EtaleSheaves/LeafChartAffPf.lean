import Development.EtaleCohomology.EtaleSheaves.LeafChartPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafChartAffPf

def ChartGeo : Prop := ∀ {X Z S : Scheme.{0}} (p : X ⟶ S) (ι : Z ⟶ X) [IsClosedImmersion ι] (d e : ℕ)
  [SmoothOfRelativeDimension (e + d) p] [SmoothOfRelativeDimension e (ι ≫ p)] (x : X), x ∈ Set.range ι →
  ∀ W : X.Opens, x ∈ W → ∃ (A B : Type) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B) (I : Ideal B),
    Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B ∧
    (∀ P : Ideal B, P.IsPrime → I ≤ P → ∃ g ∉ P,
      Algebra.IsStandardSmoothOfRelativeDimension e A (Localization.Away g ⧸ I.map (algebraMap B (Localization.Away g)))) ∧
    ∃ (j : Spec (CommRingCat.of B) ⟶ X) (_ : IsOpenImmersion j), x ∈ Set.range j ∧ Set.range j ⊆ (W : Set X) ∧
      ∀ y : Spec (CommRingCat.of B), j y ∈ Set.range ι ↔ I ≤ (show PrimeSpectrum B from y).asIdeal

def StdAway : Prop := ∀ (n : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (g : B),
  Algebra.IsStandardSmoothOfRelativeDimension n A B →
    Algebra.IsStandardSmoothOfRelativeDimension n A (Localization.Away g)

def ChartAway : Prop := LateralTheory.E.LeafChartPf.LeafChartAway

theorem stdAway_pf : StdAway := by
  intro n A B _ _ _ g h
  have := h
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 B (Localization.Away g) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away (S := Localization.Away g) g
  have := Algebra.IsStandardSmoothOfRelativeDimension.trans (n := n) (m := 0) (R := A) (S := B) (T := Localization.Away g)
  simpa using this

theorem LeafChartAff_of (hG : ChartGeo) (hW : ChartAway) : LateralTheory.E.LeafChartPf.LeafChartAff := by
  intro X Z S p ι _ d e _ _ x hx W hxW
  obtain ⟨A, B, _, _, _, I, h1, hloc, j, _, ⟨y0, rfl⟩, hjW, hj⟩ := hG p ι d e x hx W hxW
  have hI : I ≤ (show PrimeSpectrum B from y0).asIdeal := (hj y0).1 hx
  obtain ⟨g, hg, h2⟩ := hloc _ (show PrimeSpectrum B from y0).isPrime hI
  obtain ⟨j', hj', hsub, hcov, hiff⟩ := hW (Set.range ι) B j I g hj
  exact ⟨A, Localization.Away g, inferInstance, inferInstance, inferInstance, I.map (algebraMap B _),
    stdAway_pf _ A B g h1, h2, j', hj', hcov y0 hg, hsub.trans hjW, hiff⟩

end LateralTheory.E.LeafChartAffPf
