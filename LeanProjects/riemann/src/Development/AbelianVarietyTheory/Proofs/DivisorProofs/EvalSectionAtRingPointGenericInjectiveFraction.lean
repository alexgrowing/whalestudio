import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem injective_ringHom_genericStalk_integralScheme (C : Scheme.{0}) [IsIntegral C] (q : C) (hq : q = genericPoint C)
    {A : Type} [CommRing A] [Nontrivial A] (φ : C.presheaf.stalk q →+* A) : Function.Injective φ := by
  subst hq
  exact RingHom.injective (φ : C.functionField →+* A)

theorem exists_fraction_genericStalk_germ_affineOpen (C : Scheme.{0}) [IsIntegral C] (V : C.Opens) (hV : IsAffineOpen V)
    (q : C) (hq : q = genericPoint C) (hqV : q ∈ V) (s : C.presheaf.stalk q) :
    ∃ a b : Γ(C, V), b ≠ 0 ∧ s * C.presheaf.germ V q hqV b = C.presheaf.germ V q hqV a := by
  subst hq
  haveI : Nonempty V := ⟨⟨_, hqV⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen (X := C) V hV
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (S := C.functionField) (nonZeroDivisors Γ(C, V)) s
  refine ⟨a, b, nonZeroDivisors.ne_zero b.2, ?_⟩
  have := IsLocalization.mk'_spec (S := C.functionField) a b
  rw [← hab]
  exact this

theorem germ_appLE_eq_stalkMap_germ_specField {K : Type} [Field K] (C : Scheme.{0}) (x : Sp K ⟶ C) (V : C.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V)
    (p : Sp K) (hp : x p ∈ V) (c : Γ(C, V)) :
    (Sp K).presheaf.germ ⊤ p (by simp) (x.appLE V ⊤ h c) = x.stalkMap p (C.presheaf.germ V (x p) hp c) := by
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE]
  simp

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem isGen_evAt_frac : ∀ (K : Type) [Field K] (C : Scheme.{0}) [IsIntegral C] (x : Sp K ⟶ C), IsGen x →
    ∀ V : C.Opens, (V : Set C).Nonempty → ∃ h : ⊤ ≤ x ⁻¹ᵁ V, Function.Injective (evAt x h) ∧
      (IsAffineOpen V → ∀ z : K, ∃ a b : Γ(C, V), b ≠ 0 ∧ z * evAt x h b = evAt x h a) := by
  intro K _ C _ x hx V hV
  haveI : IsDominant x := hx.1
  haveI : IsPreimmersion x := hx.2
  have hsub : ∀ p q : Sp K, p = q := fun p q => Subsingleton.elim (α := PrimeSpectrum K) p q
  have hgen : ∀ p : Sp K, x p = genericPoint C := by
    intro p
    apply ((genericPoint_spec C).eq _).symm
    rw [isGenericPoint_def]
    have hr : Set.range x = {x p} := by
      ext y
      constructor
      · rintro ⟨q, rfl⟩
        rw [hsub q p]
        rfl
      · rintro rfl
        exact ⟨p, rfl⟩
    rw [← hr]
    exact x.denseRange.closure_range
  have hmem : genericPoint C ∈ V :=
    ((genericPoint_spec C).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have h : ⊤ ≤ x ⁻¹ᵁ V := by
    intro p _
    show x p ∈ V
    rw [hgen p]
    exact hmem
  obtain ⟨p⟩ : Nonempty (Sp K) := ⟨(⊥ : PrimeSpectrum K)⟩
  have hp : x p ∈ V := by rw [hgen p]; exact hmem
  refine ⟨h, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    have h1 : x.appLE V ⊤ h c = 0 := by
      have := congrArg (Scheme.ΓSpecIso (.of K)).inv.hom hc
      simpa [evAt] using this
    have h2 := germ_appLE_eq_stalkMap_germ_specField C x V h p hp c
    rw [h1, map_zero] at h2
    have h3 : C.presheaf.germ V (x p) hp c = 0 :=
      injective_ringHom_genericStalk_integralScheme C (x p) (hgen p) (x.stalkMap p).hom (by rw [← h2, map_zero])
    exact germ_injective_of_isIntegral (X := C) (x p) hp (by rw [h3, map_zero])
  · intro hA z
    obtain ⟨s, hs⟩ := x.stalkMap_surjective p
      ((Sp K).presheaf.germ ⊤ p (by simp) ((Scheme.ΓSpecIso (.of K)).inv.hom z))
    obtain ⟨a, b, hb, hab⟩ := exists_fraction_genericStalk_germ_affineOpen C V hA (x p) (hgen p) hp s
    refine ⟨a, b, hb, ?_⟩
    have e := congrArg (x.stalkMap p).hom hab
    rw [map_mul, hs, ← germ_appLE_eq_stalkMap_germ_specField C x V h p hp, ← germ_appLE_eq_stalkMap_germ_specField C x V h p hp, ← map_mul] at e
    have e2 := germ_injective_of_isIntegral (X := Sp K) p (by simp) e
    have e3 := congrArg (Scheme.ΓSpecIso (.of K)).hom.hom e2
    simpa [evAt] using e3

end GlobalTheory.Nef
