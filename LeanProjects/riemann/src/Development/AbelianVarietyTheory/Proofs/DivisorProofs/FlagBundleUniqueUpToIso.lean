import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

namespace GlobalTheory.CovTest

variable {S T Y B : Scheme.{0}}

theorem pullbackComp_congr_assoc_app (π : Y ⟶ B) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g) (h : S ⟶ T)
    (k : S ⟶ B) (w₂ : h ≫ g = k) (w₃ : (h ≫ g') ≫ π = k) (E : B.Modules) :
    (Scheme.Modules.pullbackComp h g').inv.app ((Scheme.Modules.pullback π).obj E) ≫
      (Scheme.Modules.pullback h).map ((Scheme.Modules.pullbackComp g' π).hom.app E ≫
        (Scheme.Modules.pullbackCongr w).hom.app E) ≫
      (Scheme.Modules.pullbackComp h g).hom.app E ≫ (Scheme.Modules.pullbackCongr w₂).hom.app E =
    (Scheme.Modules.pullbackComp (h ≫ g') π).hom.app E ≫ (Scheme.Modules.pullbackCongr w₃).hom.app E := by
  subst w w₂
  have := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity h g' π) E
  simp [Scheme.Modules.pullbackCongr] at this ⊢
  rw [← cancel_epi ((Scheme.Modules.pullbackComp h (g' ≫ π)).inv.app E ≫
      (Scheme.Modules.pullback h).map ((Scheme.Modules.pullbackComp g' π).inv.app E) ≫
        (Scheme.Modules.pullbackComp h g').hom.app ((Scheme.Modules.pullback π).obj E))]
  simp only [Category.assoc, reassoc_of% this, eqToHom_trans, eqToHom_refl]
  simp [← Functor.map_comp_assoc]

theorem pullbackComp_congr_id_app (π : Y ⟶ B) (w : 𝟙 Y ≫ π = π) (E : B.Modules) :
    (Scheme.Modules.pullbackComp (𝟙 Y) π).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E =
      (Scheme.Modules.pullbackId Y).hom.app ((Scheme.Modules.pullback π).obj E) := by
  have := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality π) E
  simp [Scheme.Modules.pullbackCongr] at this ⊢
  rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom] at this
  rw [this]

theorem flagCompat_comp {ι : Type} {E : ι → B.Modules} {n : ι → ℕ} (π : Y ⟶ B)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) (g : T ⟶ B)
    (fl'' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a)) (g' : T ⟶ Y) (w : g' ≫ π = g)
    (h₁ : ∀ a i, ∃ e : (Scheme.Modules.pullback g').obj ((fl a).F i) ≅ (fl'' a).F i,
      e.hom ≫ (fl'' a).ι i = (Scheme.Modules.pullback g').map ((fl a).ι i) ≫
        (Scheme.Modules.pullbackComp g' π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a))
    (k : S ⟶ B) (fl''' : ∀ a, Vert.Flag ((Scheme.Modules.pullback k).obj (E a)) (n a)) (h : S ⟶ T)
    (w₂ : h ≫ g = k)
    (h₂ : ∀ a i, ∃ e : (Scheme.Modules.pullback h).obj ((fl'' a).F i) ≅ (fl''' a).F i,
      e.hom ≫ (fl''' a).ι i = (Scheme.Modules.pullback h).map ((fl'' a).ι i) ≫
        (Scheme.Modules.pullbackComp h g).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w₂).hom.app (E a))
    (w₃ : (h ≫ g') ≫ π = k) :
    ∀ a i, ∃ e : (Scheme.Modules.pullback (h ≫ g')).obj ((fl a).F i) ≅ (fl''' a).F i,
      e.hom ≫ (fl''' a).ι i = (Scheme.Modules.pullback (h ≫ g')).map ((fl a).ι i) ≫
        (Scheme.Modules.pullbackComp (h ≫ g') π).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr w₃).hom.app (E a) := by
  intro a i
  obtain ⟨e₁, he₁⟩ := h₁ a i
  obtain ⟨e₂, he₂⟩ := h₂ a i
  refine ⟨(Scheme.Modules.pullbackComp h g').symm.app _ ≪≫ (Scheme.Modules.pullback h).mapIso e₁ ≪≫ e₂, ?_⟩
  rw [← pullbackComp_congr_assoc_app π g' g w h k w₂ w₃ (E a)]
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc, he₂]
  rw [← Functor.map_comp_assoc, he₁]
  simp

theorem flagCompat_id {ι : Type} {E : ι → B.Modules} {n : ι → ℕ} (π : Y ⟶ B)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) (w : 𝟙 Y ≫ π = π) :
    ∀ a i, ∃ e : (Scheme.Modules.pullback (𝟙 Y)).obj ((fl a).F i) ≅ (fl a).F i,
      e.hom ≫ (fl a).ι i = (Scheme.Modules.pullback (𝟙 Y)).map ((fl a).ι i) ≫
        (Scheme.Modules.pullbackComp (𝟙 Y) π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a) := by
  intro a i
  refine ⟨(Scheme.Modules.pullbackId Y).app _, ?_⟩
  rw [pullbackComp_congr_id_app π w (E a)]
  simp

theorem exists_iso_of_isFlagBundle : ∀ (B Y Y' : Scheme.{0}) (π : Y ⟶ B) (π' : Y' ⟶ B) (ι : Type) (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (fl' : ∀ a, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π').obj (E a)) (r a)), GlobalTheory.CovTest.IsFlagBundle π E r fl → GlobalTheory.CovTest.IsFlagBundle π' E r fl' → ∃ e : Y ≅ Y', e.hom ≫ π' = π := by
  intro B Y Y' π π' ι E r fl fl' hπ hπ'
  obtain ⟨u, ⟨wu, cu⟩, -⟩ := hπ' Y π fl
  obtain ⟨v, ⟨wv, cv⟩, -⟩ := hπ Y' π' fl'
  have huv : u ≫ v = 𝟙 Y := by
    obtain ⟨z, -, hz⟩ := hπ Y π fl
    have w₃ : (u ≫ v) ≫ π = π := by rw [Category.assoc, wv, wu]
    exact (hz _ ⟨w₃, flagCompat_comp π fl π' fl' v wv cv π fl u wu cu w₃⟩).trans
      (hz _ ⟨Category.id_comp π, flagCompat_id π fl _⟩).symm
  have hvu : v ≫ u = 𝟙 Y' := by
    obtain ⟨z, -, hz⟩ := hπ' Y' π' fl'
    have w₃ : (v ≫ u) ≫ π' = π' := by rw [Category.assoc, wu, wv]
    exact (hz _ ⟨w₃, flagCompat_comp π' fl' π fl u wu cu π' fl' v wv cv w₃⟩).trans
      (hz _ ⟨Category.id_comp π', flagCompat_id π' fl' _⟩).symm
  exact ⟨⟨u, v, huv, hvu⟩, wu⟩

end GlobalTheory.CovTest
