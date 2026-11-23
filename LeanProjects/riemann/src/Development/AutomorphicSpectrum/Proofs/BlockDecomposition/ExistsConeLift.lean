import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickJIsNilpotent
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeLiftEx

theorem exists_unit_lift {B : Type} [CommRing B] (J : Ideal B) (hJ : ∀ x ∈ J, IsNilpotent x) (u : (B ⧸ J)ˣ) :
    ∃ w : Bˣ, Ideal.Quotient.mk J (w : B) = (u : B ⧸ J) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : B ⧸ J)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (B ⧸ J)ˣ) : B ⧸ J)
  have hmem : a * b - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ha, hb, Units.mul_inv, map_one, sub_self]
  have hu : IsUnit (a * b) := by
    have := (hJ _ hmem).isUnit_one_add
    simpa using this
  exact ⟨(isUnit_of_mul_isUnit_left hu).unit, by simpa using ha⟩

theorem nonempty_cLiftK : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) (s : ℕ), Nonempty (CLiftK (KS q s (𝒱D D)).ι D) := by
  intro K _ X q D s
  have hp : ∀ c : (KS q s (𝒱D D)).FullSubcategory,
      ∃ p : Spec (CommRingCat.of (c.obj.B ⧸ c.obj.J)) ⟶ D.Y, p ≫ D.f = pt c.obj := by
    intro c
    obtain ⟨V, ⟨σ, hσ⟩, hV⟩ := c.property.2
    have hr : Set.range (pt c.obj) ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hV (show x ∈ (⊤ : Scheme.Opens _) from trivial)
    refine ⟨IsOpenImmersion.lift V.ι (pt c.obj) hr ≫ σ, ?_⟩
    rw [Category.assoc, hσ, IsOpenImmersion.lift_fac]
  choose p hp using hp
  have hw : ∀ {c c' : (KS q s (𝒱D D)).FullSubcategory} (φ : c ⟶ c'),
      ∃ w : (((KS q s (𝒱D D)).ι).obj c').Bˣ, ∀ (h : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (((KS q s (𝒱D D)).ι).obj c').J (((KS q s (𝒱D D)).ι).map φ).φ (((KS q s (𝒱D D)).ι).map φ).hle)) ≫ p c) ≫ D.f = p c' ≫ D.f),
        Ideal.Quotient.mk (((KS q s (𝒱D D)).ι).obj c').J w = (Scheme.ΓSpecIso (CommRingCat.of ((((KS q s (𝒱D D)).ι).obj c').B ⧸ (((KS q s (𝒱D D)).ι).obj c').J))).hom.hom
          (D.u (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (((KS q s (𝒱D D)).ι).obj c').J (((KS q s (𝒱D D)).ι).map φ).φ (((KS q s (𝒱D D)).ι).map φ).hle)) ≫ p c) (p c') h) := by
    intro c c' φ
    by_cases h : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (((KS q s (𝒱D D)).ι).obj c').J (((KS q s (𝒱D D)).ι).map φ).φ (((KS q s (𝒱D D)).ι).map φ).hle)) ≫ p c) ≫ D.f = p c' ≫ D.f
    · obtain ⟨w, hw⟩ := exists_unit_lift (((KS q s (𝒱D D)).ι).obj c').J
        (fun x hx => GlobalTheory.CompanionTheory.SiteNil.thick_J_isNilpotent _ x hx)
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of ((((KS q s (𝒱D D)).ι).obj c').B ⧸ (((KS q s (𝒱D D)).ι).obj c').J))).hom.hom.toMonoidHom
          (D.u _ _ h))
      exact ⟨w, fun _ => hw⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose w hw using @hw
  exact ⟨{ p := p, hp := hp, w := fun φ => w φ, hw := fun φ h => hw φ h }⟩

end GlobalTheory.CompanionTheory.ConeLiftEx
