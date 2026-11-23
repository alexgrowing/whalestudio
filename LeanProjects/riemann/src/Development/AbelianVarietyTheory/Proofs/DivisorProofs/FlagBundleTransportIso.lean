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

namespace GlobalTheory.CovTest

open CategoryTheory AlgebraicGeometry

theorem isFlagBundle_cond_iso {B Y T : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E E' : ι → B.Modules) (r : ι → ℕ)
    (e : ∀ a, E a ≅ E' a) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a))
    (g : T ⟶ B) (fl'' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E' a)) (r a))
    (y : T ⟶ Y) (w : y ≫ π = g) :
    (∀ a i, ∃ e0 : (Scheme.Modules.pullback y).obj ((fl a).F i) ≅
        ((fl'' a).ofIso ((Scheme.Modules.pullback g).mapIso (e a)).symm).F i,
      e0.hom ≫ ((fl'' a).ofIso ((Scheme.Modules.pullback g).mapIso (e a)).symm).ι i =
        (Scheme.Modules.pullback y).map ((fl a).ι i) ≫
          (Scheme.Modules.pullbackComp y π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a)) ↔
    (∀ a i, ∃ e0 : (Scheme.Modules.pullback y).obj (((fl a).ofIso ((Scheme.Modules.pullback π).mapIso (e a))).F i) ≅
        (fl'' a).F i,
      e0.hom ≫ (fl'' a).ι i =
        (Scheme.Modules.pullback y).map (((fl a).ofIso ((Scheme.Modules.pullback π).mapIso (e a))).ι i) ≫
          (Scheme.Modules.pullbackComp y π).hom.app (E' a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E' a)) := by
  have nat : ∀ a, (Scheme.Modules.pullback y).map ((Scheme.Modules.pullback π).map (e a).hom) ≫
      (Scheme.Modules.pullbackComp y π).hom.app (E' a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E' a) =
      (Scheme.Modules.pullbackComp y π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a) ≫
        (Scheme.Modules.pullback g).map (e a).hom := by
    intro a
    rw [← Category.assoc, ← Functor.comp_map, (Scheme.Modules.pullbackComp y π).hom.naturality (e a).hom,
      Category.assoc, (Scheme.Modules.pullbackCongr w).hom.naturality (e a).hom]
  constructor
  · intro h a i
    obtain ⟨e0, he⟩ := h a i
    refine ⟨e0, ?_⟩
    have he' := congrArg (· ≫ (Scheme.Modules.pullback g).map (e a).hom) he
    simp only [Vert.Flag.ofIso, Iso.symm_hom, Functor.mapIso_inv, Category.assoc] at he'
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id] at he'
    simp only [Vert.Flag.ofIso, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    rw [nat a]
    exact he'
  · intro h a i
    obtain ⟨e0, he⟩ := h a i
    refine ⟨e0, ?_⟩
    simp only [Vert.Flag.ofIso, Functor.mapIso_hom, Functor.map_comp, Category.assoc] at he
    rw [nat a] at he
    simp only [Vert.Flag.ofIso, Iso.symm_hom, Functor.mapIso_inv]
    rw [← Category.assoc, he]
    simp only [Category.assoc]
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

theorem isFlagBundle_of_iso : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (E E' : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → (∀ a, Nonempty (E a ≅ E' a)) → ∃ fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E' a)) (r a), IsFlagBundle π E' r fl' := by
  intro B Y π ι E E' r fl hfl he
  have e : ∀ a, E a ≅ E' a := fun a => (he a).some
  refine ⟨fun a => (fl a).ofIso ((Scheme.Modules.pullback π).mapIso (e a)), fun T g fl'' => ?_⟩
  obtain ⟨g', ⟨w, hg⟩, hu⟩ := hfl T g (fun a => (fl'' a).ofIso ((Scheme.Modules.pullback g).mapIso (e a)).symm)
  refine ⟨g', ⟨w, (isFlagBundle_cond_iso π E E' r e fl g fl'' g' w).1 hg⟩, fun y ⟨wy, hy⟩ => ?_⟩
  exact hu y ⟨wy, (isFlagBundle_cond_iso π E E' r e fl g fl'' y wy).2 hy⟩

end GlobalTheory.CovTest
