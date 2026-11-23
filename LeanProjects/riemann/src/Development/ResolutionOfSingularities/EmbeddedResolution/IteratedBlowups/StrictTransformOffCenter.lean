import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def complComapSupport {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData) : X₁.Opens :=
  (Z.comap π).support.compl

theorem complComapSupport_eq {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData) :
    complComapSupport π Z = (Z.comap π).support.compl := rfl

theorem coe_complComapSupport {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData) :
    ((complComapSupport π Z : X₁.Opens) : Set X₁) = ((Z.comap π).support : Set X₁)ᶜ := rfl

theorem strictTransform_comap_complComapSupport_ι {X X₁ : Scheme.{u}} [IsNoetherian X₁]
    (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    (Blowup.strictTransform π Z D).comap (Scheme.Opens.ι (complComapSupport π Z)) =
      (D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z)) := by
  have hqι : QuasiCompact (Scheme.Opens.ι (complComapSupport π Z)) := inferInstance
  have hq1 : QuasiCompact
      (((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι) := inferInstance
  have hq2 : QuasiCompact
      ((((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι) ≫
        Scheme.Opens.ι (complComapSupport π Z)) := inferInstance
  have h1 : Blowup.strictTransform π Z D =
      ((((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι) ≫
        Scheme.Opens.ι (complComapSupport π Z)).ker :=
    ker_ι_preimage_comp_subschemeι_eq_ker_comap (D.comap π) (complComapSupport π Z)
  rw [h1]
  exact comap_ker_subschemeι_comp
    ((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z)))
    (Scheme.Opens.ι (complComapSupport π Z))

theorem strictTransform_comap_of_comap_center_eq_top {X X₁ B : Scheme.{u}} [IsNoetherian X₁]
    (π : X₁ ⟶ X) (Z D : X.IdealSheafData) (g : B ⟶ X₁)
    (hg : (Z.comap π).comap g = ⊤) :
    (Blowup.strictTransform π Z D).comap g = (D.comap π).comap g := by
  have hsupp : ((((Z.comap π).comap g).support : Closeds B) : Set B)
      = ⇑g.base ⁻¹' (((Z.comap π).support : Closeds X₁) : Set X₁) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hempty : ⇑g.base ⁻¹' (((Z.comap π).support : Closeds X₁) : Set X₁) = ∅ := by
    rw [← hsupp, hg]
    simp
  have hbase : ∀ b : B, ⇑g.base b ∈ ((complComapSupport π Z : X₁.Opens) : Set X₁) := by
    intro b
    rw [coe_complComapSupport]
    simp only [Set.mem_compl_iff]
    intro hmem
    have hb : b ∈ ⇑g.base ⁻¹' (((Z.comap π).support : Closeds X₁) : Set X₁) := hmem
    rw [hempty] at hb
    simp at hb
  have hrange : Set.range ⇑g.base ⊆
      Set.range ⇑(Scheme.Opens.ι (complComapSupport π Z)).base := by
    rintro x ⟨b, rfl⟩
    have h0 : ⇑g.base b ∈ ((complComapSupport π Z : X₁.Opens) : Set X₁) := hbase b
    simpa [Scheme.Opens.range_ι] using h0
  have hfac := IsOpenImmersion.lift_fac (Scheme.Opens.ι (complComapSupport π Z)) g hrange
  rw [← hfac, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
    strictTransform_comap_complComapSupport_ι]

end FunctorialResolution.EmbeddedResolution
