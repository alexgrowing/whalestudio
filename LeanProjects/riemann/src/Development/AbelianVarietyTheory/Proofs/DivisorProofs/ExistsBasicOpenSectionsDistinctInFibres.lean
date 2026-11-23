import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqualizerSectionsClosedIdealStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SectionsSpread

theorem sep_elem (R : Type) [CommRing R] (X : Over (Sp R)) (hX : IsSeparated X.hom)
    (K : Type) [Field K] (e : R →+* K) (x y : Sp R ⟶ X.left)
    (hx : x ≫ X.hom = 𝟙 _) (hy : y ≫ X.hom = 𝟙 _) (hne : spMap e ≫ x ≠ spMap e ≫ y) :
    ∃ r : R, e r ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), ψ r ≠ 0 →
      spMap ψ ≫ x ≠ spMap ψ ≫ y := by
  obtain ⟨I, hI⟩ := GlobalTheory.T.equalizer_sections_closed_ideal R X hX x y hx hy
  have h1 : ¬ ∀ r ∈ I, e r = 0 := fun h => hne ((hI K e).2 h)
  push_neg at h1
  obtain ⟨r, hrI, hr⟩ := h1
  refine ⟨r, hr, fun F _ ψ hψ heq => hψ ((hI F ψ).1 heq r hrI)⟩

theorem pairs : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), IsSeparated X.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → ∀ t : Finset (Sp R ⟶ X.left), (∀ x ∈ t, x ≫ X.hom = 𝟙 _) → (∀ x ∈ t, ∀ y ∈ t, x ≠ y → spMap e ≫ x ≠ spMap e ≫ y) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → ∀ x ∈ t, ∀ y ∈ t, x ≠ y → spMap ψ ≫ x ≠ spMap ψ ≫ y := by
  intro R _ X hX K _ e _ t ht hsep
  classical
  let g : (Sp R ⟶ X.left) × (Sp R ⟶ X.left) → R := fun p =>
    if h : p.1 ∈ t ∧ p.2 ∈ t ∧ p.1 ≠ p.2 then
      Classical.choose (sep_elem R X hX K e p.1 p.2 (ht _ h.1) (ht _ h.2.1) (hsep _ h.1 _ h.2.1 h.2.2))
    else 1
  have hg : ∀ p : (Sp R ⟶ X.left) × (Sp R ⟶ X.left), e (g p) ≠ 0 ∧
      ∀ (F : Type) [Field F] (ψ : R →+* F), ψ (g p) ≠ 0 → p.1 ∈ t → p.2 ∈ t → p.1 ≠ p.2 →
        spMap ψ ≫ p.1 ≠ spMap ψ ≫ p.2 := by
    intro p
    by_cases h : p.1 ∈ t ∧ p.2 ∈ t ∧ p.1 ≠ p.2
    · have hs := Classical.choose_spec
        (sep_elem R X hX K e p.1 p.2 (ht _ h.1) (ht _ h.2.1) (hsep _ h.1 _ h.2.1 h.2.2))
      simp only [g, dif_pos h]
      exact ⟨hs.1, fun F _ ψ hψ _ _ _ => hs.2 F ψ hψ⟩
    · simp only [g, dif_neg h]
      exact ⟨by simp, fun F _ ψ _ h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  refine ⟨∏ p ∈ t ×ˢ t, g p, ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun p _ => (hg p).1
  · intro F _ ψ hu x hx y hy hxy
    have hmem : (x, y) ∈ t ×ˢ t := Finset.mem_product.2 ⟨hx, hy⟩
    have hdvd : g (x, y) ∣ ∏ p ∈ t ×ˢ t, g p := Finset.dvd_prod_of_mem g hmem
    have hu' : IsUnit (ψ (g (x, y))) := isUnit_of_dvd_unit (map_dvd ψ hdvd) hu
    exact (hg (x, y)).2 F ψ hu'.ne_zero hx hy hxy

end GlobalTheory.SectionsSpread
