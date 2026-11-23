import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem crys_two_reductions : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ N : GrpMor (divided₂ hJ) (spMap ρ) A₁ κ (spMap π) A₀ (RingHom.id R) (spMap π₁) i₁,
      Function.Bijective (N.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀) ∧
      ∀ d : Crys κ (spMap π) A₀, crysToDR κ h d = crysToDR (divided₂ hJ) h₂ ((N.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀).dualMap d) := by
  intro P R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ st g A₀ _ A₁ _ A _ i₁ i₂ i h₁ h₂ h e hA hg
  obtain ⟨-, -, -, PR, -⟩ := P
  have hπ : Function.Surjective π := by
    rw [← st.comp]; exact st.surj₁.comp st.surj
  have hb : spMap π₁ ≫ spMap ρ = spMap π ≫ spMap (RingHom.id R) := by
    rw [Cris.spMap_id, Category.comp_id, ← st.comp, Cris.spMap_comp]
  let N : GrpMor (divided₂ hJ) (spMap ρ) A₁ κ (spMap π) A₀ (RingHom.id R) (spMap π₁) i₁ :=
    GrpMor.of_isGrpPullback st.dpJ hb h₁
  have key : ∀ c, N.pull ((liftMor (divided₂ hJ) h₂).pull c) = (liftMor κ h).pull c := fun c ↦
    GrpMor.pull_pull (liftMor (divided₂ hJ) h₂) N (liftMor κ h) (fun _ ↦ rfl) e c
  have b := PR R A g hA hg I κ st.nil R₀ π hπ st.ker A₀ i h
  have b₂ := PR R A g hA hg J (divided₂ hJ) (isDPNilpotent_squareZero hJ) R₁ ρ st.surj st.kerJ A₁ i₂ h₂
  refine ⟨N, ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩, fun d ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := b₂.2 x
    obtain ⟨y, rfl⟩ := b₂.2 y
    have : (liftMor κ h).pull x = (liftMor κ h).pull y := by
      rw [← key, ← key]; exact hxy
    rw [b.1 this]
  · obtain ⟨c, rfl⟩ := b.2 y
    exact ⟨_, key c⟩
  · ext c
    show d ((liftMor κ h).pull c) = d (N.pull ((liftMor (divided₂ hJ) h₂).pull c))
    rw [key]

end GlobalTheory.SqLift
