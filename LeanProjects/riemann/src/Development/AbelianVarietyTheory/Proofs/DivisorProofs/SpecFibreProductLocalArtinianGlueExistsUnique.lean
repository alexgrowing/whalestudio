import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqOfMulEq
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.SmallGlue
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem spec_localArtinian_point_eq (P : CommRingCat.{0}) [IsLocalRing P] [IsArtinianRing P]
    (x y : Spec P) : x = y := by
  apply PrimeSpectrum.ext
  haveI := x.isPrime
  haveI := y.isPrime
  rw [IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime x.asIdeal),
    IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime y.asIdeal)]

theorem spec_map_injective_of_surjective {R S : CommRingCat.{0}} (f : R ⟶ S) (hf : Function.Surjective f) :
    Function.Injective (Spec.map f) := fun x y h =>
  PrimeSpectrum.comap_injective_of_surjective f.hom hf h

theorem spec_pullback_localArtinian_glue_existsUnique : ∀ (P B₁ B₂ B₀ : CommRingCat.{0}) (f₁ : P ⟶ B₁) (f₂ : P ⟶ B₂) (g₁ : B₁ ⟶ B₀) (g₂ : B₂ ⟶ B₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective f₁ → Function.Surjective f₂ → Nontrivial B₀ → ∀ (Z : Scheme.{0}) (a : Spec B₁ ⟶ Z) (b : Spec B₂ ⟶ Z), Spec.map g₁ ≫ a = Spec.map g₂ ≫ b → ∃! w : Spec P ⟶ Z, Spec.map f₁ ≫ w = a ∧ Spec.map f₂ ≫ w = b := by
  intro P B₁ B₂ B₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ hnt Z a b hab
  have hnt₁ : Nontrivial B₁ := RingHom.domain_nontrivial g₁.hom
  have hnt₂ : Nontrivial B₂ := RingHom.domain_nontrivial g₂.hom
  obtain ⟨y₀⟩ : Nonempty (Spec B₀) := inferInstanceAs (Nonempty (PrimeSpectrum B₀))
  have hone₁ : ∀ y y' : Spec B₁, y = y' := fun y y' =>
    spec_map_injective_of_surjective f₁ hs₁ (spec_localArtinian_point_eq P _ _)
  have hone₂ : ∀ y y' : Spec B₂, y = y' := fun y y' =>
    spec_map_injective_of_surjective f₂ hs₂ (spec_localArtinian_point_eq P _ _)
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := a (Spec.map g₁ y₀)) trivial
  have hza : Set.range a ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨y, rfl⟩; rw [hV.range_fromSpec, hone₁ y (Spec.map g₁ y₀)]; exact hzV
  have hzb : Set.range b ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨y, rfl⟩
    rw [hV.range_fromSpec, hone₂ y (Spec.map g₂ y₀)]
    have : b (Spec.map g₂ y₀) = a (Spec.map g₁ y₀) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hab]
    rw [this]; exact hzV
  haveI := hV.isOpenImmersion_fromSpec
  set φ₁ := Spec.preimage (IsOpenImmersion.lift hV.fromSpec a hza) with hφ₁
  set φ₂ := Spec.preimage (IsOpenImmersion.lift hV.fromSpec b hzb) with hφ₂
  have ha : Spec.map φ₁ ≫ hV.fromSpec = a := by
    rw [hφ₁, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hb : Spec.map φ₂ ≫ hV.fromSpec = b := by
    rw [hφ₂, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hφ : φ₁ ≫ g₁ = φ₂ ≫ g₂ := by
    apply Spec.map_injective
    rw [← cancel_mono hV.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      ha, hb, hab]
  have key : ∀ w : Spec P ⟶ Z, Spec.map f₁ ≫ w = a → Spec.map f₂ ≫ w = b →
      w = Spec.map (hP.lift φ₁ φ₂ hφ) ≫ hV.fromSpec := by
    intro w hw₁ hw₂
    have hr : Set.range w ⊆ Set.range hV.fromSpec := by
      rintro _ ⟨x, rfl⟩
      rw [spec_localArtinian_point_eq P x (Spec.map f₁ (Spec.map g₁ y₀)), ← Scheme.Hom.comp_apply, hw₁]
      exact hza ⟨_, rfl⟩
    rw [← IsOpenImmersion.lift_fac hV.fromSpec w hr, ← Spec.map_preimage (IsOpenImmersion.lift hV.fromSpec w hr)]
    congr 2
    apply hP.hom_ext
    · rw [IsPullback.lift_fst]
      apply Spec.map_injective
      rw [← cancel_mono hV.fromSpec, Spec.map_comp, Category.assoc, Spec.map_preimage,
        IsOpenImmersion.lift_fac, hw₁, ha]
    · rw [IsPullback.lift_snd]
      apply Spec.map_injective
      rw [← cancel_mono hV.fromSpec, Spec.map_comp, Category.assoc, Spec.map_preimage,
        IsOpenImmersion.lift_fac, hw₂, hb]
  refine ⟨Spec.map (hP.lift φ₁ φ₂ hφ) ≫ hV.fromSpec, ⟨?_, ?_⟩, fun w hw => key w hw.1 hw.2⟩
  · rw [← Category.assoc, ← Spec.map_comp, IsPullback.lift_fst, ha]
  · rw [← Category.assoc, ← Spec.map_comp, IsPullback.lift_snd, hb]

end GlobalTheory
