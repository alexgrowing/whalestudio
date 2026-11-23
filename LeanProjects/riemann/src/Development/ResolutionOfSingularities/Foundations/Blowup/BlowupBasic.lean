import Mathlib
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace FunctorialResolution.Blowup

theorem map_mem_nonZeroDivisors_of_iso {A B : CommRingCat.{u}} (e : A ≅ B) {x : A}
    (hx : x ∈ nonZeroDivisors A) : e.hom.hom x ∈ nonZeroDivisors B := by
  obtain ⟨hx1, hx2⟩ := mem_nonZeroDivisors_iff.mp hx
  have h2 : ∀ z : A, e.inv.hom (e.hom.hom z) = z := by
    intro z
    simp
  have h3 : ∀ y : B, e.hom.hom (e.inv.hom y) = y := by
    intro y
    simp
  have key : ∀ y : B, e.hom.hom x * y = 0 → y = 0 := by
    intro y hy
    have h1 : e.inv.hom (e.hom.hom x * y) = 0 := by rw [hy, map_zero]
    rw [map_mul, h2 x] at h1
    have h4 := hx1 _ h1
    rw [← h3 y, h4, map_zero]
  rw [mem_nonZeroDivisors_iff]
  refine ⟨key, fun y hy => key y ?_⟩
  rw [mul_comm]
  exact hy

private theorem exists_affineOpen_le (X : Scheme.{u}) (x : X) (W : X.Opens) (hx : x ∈ W) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ (U : X.Opens) ≤ W := by
  obtain ⟨V, hV, hxV, hVW⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  exact ⟨⟨V, hV⟩, hxV, hVW⟩

private theorem appLE_eq_id_of_eq_id {Z : Scheme.{u}} (g : Z ⟶ Z) (hg : g = 𝟙 Z) (U : Z.Opens)
    (h : U ≤ g ⁻¹ᵁ U) : g.appLE U U h = 𝟙 _ := by
  subst hg
  simp [Scheme.Hom.appLE]
  exact (Category.id_comp _).trans (Z.presheaf.map_id _)

private theorem le_preimage_inv_preimage_hom {A B : Scheme.{u}} (e : A ≅ B) (U : B.Opens) :
    U ≤ e.inv ⁻¹ᵁ (e.hom ⁻¹ᵁ U) := by
  intro y hy
  show e.hom.base (e.inv.base y) ∈ U
  have hb : e.hom.base (e.inv.base y) = y := by simp
  rw [hb]
  exact hy

private noncomputable def sectionsIsoPreimage {A B : Scheme.{u}} (e : A ≅ B) (U : B.Opens) :
    Γ(B, U) ≅ Γ(A, e.hom ⁻¹ᵁ U) where
  hom := e.hom.appLE U (e.hom ⁻¹ᵁ U) le_rfl
  inv := e.inv.appLE (e.hom ⁻¹ᵁ U) U (le_preimage_inv_preimage_hom e U)
  hom_inv_id := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_id_of_eq_id _ e.inv_hom_id U _
  inv_hom_id := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_id_of_eq_id _ e.hom_inv_id _ _

private theorem isLocallyGeneratedByNonZeroDivisor_comap_id {X : Scheme.{u}} {I : X.IdealSheafData}
    (hI : IsLocallyGeneratedByNonZeroDivisor I) : IsLocallyGeneratedByNonZeroDivisor (I.comap (𝟙 X)) := by
  intro x
  obtain ⟨U, f, hxU, hf, hIspan⟩ := hI x
  refine ⟨U, f, hxU, hf, ?_⟩
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I (𝟙 X) U U le_rfl,
    appLE_eq_id_of_eq_id (𝟙 X) rfl (U : X.Opens) le_rfl, hIspan]
  simp

theorem isLocallyGeneratedByNonZeroDivisor_top (X : Scheme.{u}) :
    IsLocallyGeneratedByNonZeroDivisor (⊤ : X.IdealSheafData) := by
  intro x
  obtain ⟨U, hxU, -⟩ := exists_affineOpen_le X x ⊤ trivial
  refine ⟨U, 1, hxU, one_mem _, ?_⟩
  simp

theorem isLocallyGeneratedByNonZeroDivisor_comap_top {X X' : Scheme.{u}} (f : X' ⟶ X) :
    IsLocallyGeneratedByNonZeroDivisor ((⊤ : X.IdealSheafData).comap f) := by
  intro x
  obtain ⟨U, hU, -⟩ := exists_affineOpen_le X (f.base x) ⊤ trivial
  obtain ⟨V, hV, hVU⟩ := exists_affineOpen_le X' x (f ⁻¹ᵁ (U : X.Opens)) hU
  refine ⟨V, 1, hV, one_mem _, ?_⟩
  have h1 : ((⊤ : X.IdealSheafData).ideal U) = ⊤ := by simp
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (⊤ : X.IdealSheafData) f U V hVU, h1,
    Ideal.map_top, Ideal.span_singleton_one]

theorem IsLocallyGeneratedByNonZeroDivisor.comap_iso {X' X'' : Scheme.{u}} {J : X'.IdealSheafData}
    (hJ : IsLocallyGeneratedByNonZeroDivisor J) (e : X'' ≅ X') :
    IsLocallyGeneratedByNonZeroDivisor (J.comap e.hom) := by
  intro x
  obtain ⟨U, f, hxU, hf, hJU⟩ := hJ (e.hom.base x)
  refine ⟨⟨e.hom ⁻¹ᵁ (U : X'.Opens), IsAffineOpen.preimage_of_isIso U.2 e.hom⟩,
    (e.hom.appLE (U : X'.Opens) (e.hom ⁻¹ᵁ (U : X'.Opens)) le_rfl).hom f, hxU, ?_, ?_⟩
  · exact FunctorialResolution.Blowup.map_mem_nonZeroDivisors_of_iso (sectionsIsoPreimage e (U : X'.Opens)) hf
  · rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE J e.hom U
      ⟨e.hom ⁻¹ᵁ (U : X'.Opens), IsAffineOpen.preimage_of_isIso U.2 e.hom⟩ le_rfl, hJU,
      Ideal.map_span, Set.image_singleton]

theorem IsBlowupAlongIdealSheaf.isLocallyGeneratedByNonZeroDivisor_comap {X X' : Scheme.{u}} {π : X' ⟶ X}
    {I : X.IdealSheafData} (h : IsBlowupAlongIdealSheaf π I) : IsLocallyGeneratedByNonZeroDivisor (I.comap π) :=
  h.1

theorem IsBlowupAlongIdealSheaf.existsUnique_lift {X X' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) (W : Scheme.{u}) (g : W ⟶ X) (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) :
    ∃! k : W ⟶ X', k ≫ π = g :=
  h.2 W g hg

theorem IsBlowupAlongIdealSheaf.hom_ext_of_comp_eq {X X' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) {W : Scheme.{u}} {g : W ⟶ X} (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g))
    {a b : W ⟶ X'} (ha : a ≫ π = g) (hb : b ≫ π = g) : a = b :=
  (h.2 W g hg).unique ha hb

theorem IsBlowupAlongIdealSheaf.isIso_of_isLocallyGeneratedByNonZeroDivisor {X X' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) (hI : IsLocallyGeneratedByNonZeroDivisor I) : IsIso π := by
  obtain ⟨s, hs, -⟩ := h.2 X (𝟙 X) (isLocallyGeneratedByNonZeroDivisor_comap_id hI)
  refine ⟨⟨s, ?_, hs⟩⟩
  exact h.hom_ext_of_comp_eq h.1 (by rw [Category.assoc, hs, Category.comp_id]) (Category.id_comp π)

theorem IsBlowupAlongIdealSheaf.isIso_of_top {X X' : Scheme.{u}} {π : X' ⟶ X}
    (h : IsBlowupAlongIdealSheaf π (⊤ : X.IdealSheafData)) : IsIso π :=
  h.isIso_of_isLocallyGeneratedByNonZeroDivisor (isLocallyGeneratedByNonZeroDivisor_top X)

theorem isBlowupAlongIdealSheaf_id_of_isLocallyGeneratedByNonZeroDivisor {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : IsLocallyGeneratedByNonZeroDivisor I) : IsBlowupAlongIdealSheaf (𝟙 X) I := by
  constructor
  · rwa [Scheme.IdealSheafData.comap_id]
  · intro W g _
    refine ⟨g, Category.comp_id g, ?_⟩
    intro y hy
    rw [← hy, Category.comp_id]

theorem IsBlowupAlongIdealSheaf.hom_ext_of_isBlowupAlongIdealSheaf {X X₁ X₂ : Scheme.{u}} {π₁ : X₁ ⟶ X} {π₂ : X₂ ⟶ X}
    {I : X.IdealSheafData} (h₁ : IsBlowupAlongIdealSheaf π₁ I) (h₂ : IsBlowupAlongIdealSheaf π₂ I)
    {a b : X₁ ⟶ X₂} (ha : a ≫ π₂ = π₁) (hb : b ≫ π₂ = π₁) : a = b :=
  h₂.hom_ext_of_comp_eq h₁.1 ha hb

theorem IsBlowupAlongIdealSheaf.exists_iso {X X₁ X₂ : Scheme.{u}} {π₁ : X₁ ⟶ X} {π₂ : X₂ ⟶ X}
    {I : X.IdealSheafData} (h₁ : IsBlowupAlongIdealSheaf π₁ I) (h₂ : IsBlowupAlongIdealSheaf π₂ I) :
    ∃ e : X₁ ≅ X₂, e.hom ≫ π₂ = π₁ := by
  obtain ⟨a, ha, -⟩ := h₂.2 X₁ π₁ h₁.1
  obtain ⟨b, hb, -⟩ := h₁.2 X₂ π₂ h₂.1
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · exact h₁.hom_ext_of_comp_eq h₁.1 (by rw [Category.assoc, hb, ha]) (Category.id_comp π₁)
  · exact h₂.hom_ext_of_comp_eq h₂.1 (by rw [Category.assoc, ha, hb]) (Category.id_comp π₂)

theorem IsBlowupAlongIdealSheaf.iso_hom_comp {X X' X'' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) (e : X'' ≅ X') : IsBlowupAlongIdealSheaf (e.hom ≫ π) I := by
  have hcomp : I.comap (e.hom ≫ π) = (I.comap π).comap e.hom := by
    simp [Scheme.IdealSheafData.comap_comp]
  refine ⟨?_, ?_⟩
  · rw [hcomp]
    exact h.1.comap_iso e
  · intro W g hg
    obtain ⟨k, hk, hk'⟩ := h.2 W g hg
    refine ⟨k ≫ e.inv, ?_, ?_⟩
    · show (k ≫ e.inv) ≫ e.hom ≫ π = g
      rw [Category.assoc, ← Category.assoc e.inv e.hom π, e.inv_hom_id, Category.id_comp, hk]
    · intro m hm
      have hm' : m ≫ e.hom ≫ π = g := hm
      have hme : m ≫ e.hom = k := hk' _ ((Category.assoc m e.hom π).trans hm')
      rw [← hme, Category.assoc, e.hom_inv_id, Category.comp_id]

end FunctorialResolution.Blowup
