import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTest.FlagUniq

variable {B Y : Scheme.{0}} {ι : Type} {E : ι → B.Modules} {n : ι → ℕ}

def Carries {T : Scheme.{0}} (π : Y ⟶ B) (g : T ⟶ B) (h : T ⟶ Y) (w : h ≫ π = g)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a))
    (flT : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a)) : Prop :=
  ∀ a i, ∃ e : (Scheme.Modules.pullback h).obj ((fl a).F i) ≅ (flT a).F i,
    e.hom ≫ (flT a).ι i = (Scheme.Modules.pullback h).map ((fl a).ι i) ≫
      (Scheme.Modules.pullbackComp h π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a)

theorem carries_id (π : Y ⟶ B) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) :
    Carries π π (𝟙 Y) (Category.id_comp π) fl fl := by
  intro a i
  refine ⟨(Scheme.Modules.pullbackId Y).app ((fl a).F i), ?_⟩
  have h1 : (Scheme.Modules.pullback (𝟙 Y)).map ((fl a).ι i) ≫
      (Scheme.Modules.pullbackId Y).hom.app ((Scheme.Modules.pullback π).obj (E a)) =
      (Scheme.Modules.pullbackId Y).hom.app ((fl a).F i) ≫ (fl a).ι i :=
    (Scheme.Modules.pullbackId Y).hom.naturality ((fl a).ι i)
  have h2 := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality π) (E a)
  simp at h2
  simp only [Iso.app_hom, Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app]
  rw [← h1, ← h2, Iso.hom_inv_id_app_assoc]

theorem carries_comp {T Y' : Scheme.{0}} (π : Y ⟶ B) (π' : Y' ⟶ B) (g : T ⟶ B) (h₁ : T ⟶ Y') (h₂ : Y' ⟶ Y)
    (w₁ : h₁ ≫ π' = g) (w₂ : h₂ ≫ π = π')
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a))
    (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback π').obj (E a)) (n a))
    (flT : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a))
    (c₁ : Carries π' g h₁ w₁ fl' flT) (c₂ : Carries π π' h₂ w₂ fl fl') :
    Carries π g (h₁ ≫ h₂) (by rw [Category.assoc, w₂, w₁]) fl flT := by
  subst w₁ w₂
  intro a i
  obtain ⟨e₁, he₁⟩ := c₁ a i
  obtain ⟨e₂, he₂⟩ := c₂ a i
  refine ⟨(Scheme.Modules.pullbackComp h₁ h₂).symm.app _ ≪≫ (Scheme.Modules.pullback h₁).mapIso e₂ ≪≫ e₁, ?_⟩
  have h3 := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity h₁ h₂ π) (E a)
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc, he₁] at h3 ⊢
  rw [← Functor.map_comp_assoc, he₂]
  simp [Scheme.Modules.pullbackCongr] at h3 ⊢
  have hn : (Scheme.Modules.pullbackComp h₁ h₂).inv.app ((fl a).F i) ≫
      (Scheme.Modules.pullback h₁).map ((Scheme.Modules.pullback h₂).map ((fl a).ι i)) =
      (Scheme.Modules.pullback (h₁ ≫ h₂)).map ((fl a).ι i) ≫
        (Scheme.Modules.pullbackComp h₁ h₂).inv.app ((Scheme.Modules.pullback π).obj (E a)) :=
    ((Scheme.Modules.pullbackComp h₁ h₂).inv.naturality ((fl a).ι i)).symm
  rw [reassoc_of% hn]
  congr 1
  have h4 := congrArg (fun f => (Scheme.Modules.pullbackComp h₁ h₂).inv.app ((Scheme.Modules.pullback π).obj (E a)) ≫
    (Scheme.Modules.pullback h₁).map ((Scheme.Modules.pullbackComp h₂ π).hom.app (E a)) ≫
    (Scheme.Modules.pullbackComp h₁ (h₂ ≫ π)).hom.app (E a) ≫ f ≫ eqToHom (by rw [Category.assoc])) h3
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id_app_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at h4
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc] at h4
  exact h4.symm

end GlobalTheory.CovTest.FlagUniq

open GlobalTheory.CovTest.FlagUniq in

theorem GlobalTheory.CovTest.flagBundle_iso_over : ∀ (B Y Y' : Scheme.{0}) (π : Y ⟶ B) (π' : Y' ⟶ B) (ι : Type) (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback π').obj (E a)) (r a)), IsFlagBundle π E r fl → IsFlagBundle π' E r fl' → ∃ e : Y ≅ Y', e.hom ≫ π' = π := by
  intro B Y Y' π π' ι E r fl fl' h h'
  obtain ⟨g₁, ⟨w₁, c₁⟩, -⟩ := h' Y π fl
  obtain ⟨g₂, ⟨w₂, c₂⟩, -⟩ := h Y' π' fl'
  obtain ⟨u, -, hu⟩ := h Y π fl
  obtain ⟨u', -, hu'⟩ := h' Y' π' fl'
  have e₁ : g₁ ≫ g₂ = 𝟙 Y :=
    (hu _ ⟨_, carries_comp π π' π g₁ g₂ w₁ w₂ fl fl' fl c₁ c₂⟩).trans (hu _ ⟨_, carries_id π fl⟩).symm
  have e₂ : g₂ ≫ g₁ = 𝟙 Y' :=
    (hu' _ ⟨_, carries_comp π' π π' g₂ g₁ w₂ w₁ fl' fl fl' c₂ c₁⟩).trans (hu' _ ⟨_, carries_id π' fl'⟩).symm
  exact ⟨⟨g₁, g₂, e₁, e₂⟩, w₁⟩
