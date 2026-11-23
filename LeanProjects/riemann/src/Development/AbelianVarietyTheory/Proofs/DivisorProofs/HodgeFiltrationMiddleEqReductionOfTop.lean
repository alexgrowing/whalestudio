import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FilRed

theorem filtration_reduction : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (M : GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _)) (F : Submodule R (HdR A)) (F₁ : Submodule R₁ (HdR A₁)),
      (∀ y : HdR A₁, y ∈ F₁ ↔ ∃ x ∈ F, (redMor h₂).Corr x y) →
      (∀ d₁, crysToDR κ₁ h₁ d₁ ∈ F₁ ↔ ∃ d, crysToDR κ h d ∈ F ∧ M.Corr d d₁) ∧
      ((∀ y : HdR A₁, y ∈ Fil A₁ ↔ ∃ x ∈ Fil A, (redMor h₂).Corr x y)) := by
  intro P R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ hS g A₀ _ A₁ _ A _ i₁ i₂ i h₁ h₂ h e hA hg M F F₁ hF
  have hπ : Function.Surjective π := hS.comp ▸ hS.surj₁.comp hS.surj
  have H := canonical_of_abelianDeRham P hS.nil hπ hS.ker
  have hb := H.crysToDR_bijective h hA hg
  have hs := (H g A₀ A i h hA hg).1.2
  have e' : i₁ ≫ i₂ = 𝟙 _ ≫ i := by rw [e, Category.id_comp]
  have key : ∀ d d₁, (redMor h₂).Corr (crysToDR κ h d) (crysToDR κ₁ h₁ d₁) ↔ M.Corr d d₁ := by
    intro d d₁
    refine ⟨fun H' c' ↦ ?_, fun H' ↦ crysToDR_corr κ h h₁ M (redMor h₂) e' H'⟩
    obtain ⟨c, rfl⟩ := hs c'
    have k := (liftMor κ h).comp M
    rw [GrpMor.pull_pull (liftMor κ h) M k (fun _ ↦ rfl) rfl c,
      ← GrpMor.pull_pull (redMor h₂) (liftMor κ₁ h₁) k (fun _ ↦ rfl) e' c]
    exact H' c
  refine ⟨fun d₁ ↦ ?_, (canonical_of_abelianDeRham P (isDPNilpotent_squareZero hJ) hS.surj hS.kerJ g A₁ A i₂ h₂ hA hg).2.2⟩
  rw [hF]
  constructor
  · rintro ⟨x, hx, c⟩
    obtain ⟨d, rfl⟩ := hb.2 x
    exact ⟨d, hx, (key d d₁).1 c⟩
  · rintro ⟨d, hd, c⟩
    exact ⟨_, hd, (key d d₁).2 c⟩

end GlobalTheory.FilRed
