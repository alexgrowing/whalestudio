import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

namespace GlobalTheory.FlagLiftComp

theorem liftComp : ∀ {B T Y₁ Y₂ : Scheme.{0}} (g : T ⟶ B) (π₁ : Y₁ ⟶ B) (π₂ : Y₂ ⟶ B) (E : B.Modules)
    (F' : T.Modules) (F₁ : Y₁.Modules) (F₂ : Y₂.Modules) (ι' : F' ⟶ (Scheme.Modules.pullback g).obj E)
    (ι₁ : F₁ ⟶ (Scheme.Modules.pullback π₁).obj E) (ι₂ : F₂ ⟶ (Scheme.Modules.pullback π₂).obj E)
    (g₁ : T ⟶ Y₁) (g₂ : Y₁ ⟶ Y₂) (w₁ : g₁ ≫ π₁ = g) (w₂ : g₂ ≫ π₂ = π₁) (w : (g₁ ≫ g₂) ≫ π₂ = g)
    (e₁ : (Scheme.Modules.pullback g₁).obj F₁ ≅ F'),
    e₁.hom ≫ ι' = (Scheme.Modules.pullback g₁).map ι₁ ≫
      (Scheme.Modules.pullbackComp g₁ π₁).hom.app E ≫ (Scheme.Modules.pullbackCongr w₁).hom.app E →
    ∀ (e₂ : (Scheme.Modules.pullback g₂).obj F₂ ≅ F₁),
    e₂.hom ≫ ι₁ = (Scheme.Modules.pullback g₂).map ι₂ ≫
      (Scheme.Modules.pullbackComp g₂ π₂).hom.app E ≫ (Scheme.Modules.pullbackCongr w₂).hom.app E →
    ∃ e : (Scheme.Modules.pullback (g₁ ≫ g₂)).obj F₂ ≅ F', e.hom ≫ ι' =
      (Scheme.Modules.pullback (g₁ ≫ g₂)).map ι₂ ≫
        (Scheme.Modules.pullbackComp (g₁ ≫ g₂) π₂).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E := by
  intro B T Y₁ Y₂ g π₁ π₂ E F' F₁ F₂ ι' ι₁ ι₂ g₁ g₂ w₁ w₂ w e₁ h₁ e₂ h₂
  subst w₂
  subst w₁
  have hc : ∀ {X Y : Scheme.{0}} {f : X ⟶ Y} (h : f = f) (M : Y.Modules),
      (Scheme.Modules.pullbackCongr h).hom.app M = 𝟙 _ := fun _ _ => rfl
  rw [hc, Category.comp_id] at h₁ h₂
  refine ⟨(Scheme.Modules.pullbackComp g₁ g₂).symm.app F₂ ≪≫ (Scheme.Modules.pullback g₁).mapIso e₂ ≪≫ e₁, ?_⟩
  have hA := congrArg (fun α => NatTrans.app α E)
    (Scheme.Modules.pseudofunctor_associativity g₁ g₂ π₂)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at hA
  have hB : (Scheme.Modules.pullbackComp g₁ g₂).hom.app ((Scheme.Modules.pullback π₂).obj E) ≫
      (Scheme.Modules.pullbackComp (g₁ ≫ g₂) π₂).hom.app E =
      (Scheme.Modules.pullback g₁).map ((Scheme.Modules.pullbackComp g₂ π₂).hom.app E) ≫
        (Scheme.Modules.pullbackComp g₁ (g₂ ≫ π₂)).hom.app E ≫ eqToHom (by simp) := by
    rw [← hA]
    rw [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hN := (Scheme.Modules.pullbackComp g₁ g₂).inv.naturality ι₂
  simp only [Functor.comp_map] at hN
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc, h₁]
  rw [← Functor.map_comp_assoc, h₂, Functor.map_comp_assoc]
  rw [← reassoc_of% hN]
  congr 1
  rw [← cancel_epi ((Scheme.Modules.pullbackComp g₁ g₂).hom.app ((Scheme.Modules.pullback π₂).obj E)),
    Iso.hom_inv_id_app_assoc, reassoc_of% hB]
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app, eqToHom_trans, eqToHom_refl, Category.comp_id]

end GlobalTheory.FlagLiftComp
