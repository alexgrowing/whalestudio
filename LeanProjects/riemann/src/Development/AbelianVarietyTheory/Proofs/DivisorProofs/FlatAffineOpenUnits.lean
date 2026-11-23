import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem flat_and_isUnit_sections_of_flat_over_away :
    ∀ (N : ℕ) (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (N : ℤ))), Flat s →
    ∀ (W : M.Opens), IsAffineOpen W → Module.Flat ℤ Γ(M, W) ∧ IsUnit ((N : ℤ) : Γ(M, W)) := by
  intro N M s hs W hW
  have htop : IsAffineOpen (⊤ : (Sp (Localization.Away (N : ℤ))).Opens) := isAffineOpen_top _
  have hfl : RingHom.Flat (s.appLE ⊤ W le_top).hom :=
    HasRingHomProperty.appLE (P := @Flat) (Q := RingHom.Flat) s hs ⟨⊤, htop⟩ ⟨W, hW⟩ le_top
  let φ : Localization.Away (N : ℤ) →+* Γ(M, W) :=
    (s.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (N : ℤ)))).inv.hom
  have hφ : RingHom.Flat φ := by
    refine RingHom.Flat.comp ?_ hfl
    exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have hloc : RingHom.Flat (algebraMap ℤ (Localization.Away (N : ℤ))) := by
    rw [RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat _ (Submonoid.powers (N : ℤ))
  have hcomp : RingHom.Flat (φ.comp (algebraMap ℤ (Localization.Away (N : ℤ)))) := hloc.comp hφ
  have heq : φ.comp (algebraMap ℤ (Localization.Away (N : ℤ))) = algebraMap ℤ Γ(M, W) :=
    Subsingleton.elim _ _
  rw [heq, RingHom.flat_algebraMap_iff] at hcomp
  refine ⟨hcomp, ?_⟩
  have hu : IsUnit (algebraMap ℤ (Localization.Away (N : ℤ)) (N : ℤ)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have := hu.map φ
  simpa [map_intCast] using this

end GlobalTheory
