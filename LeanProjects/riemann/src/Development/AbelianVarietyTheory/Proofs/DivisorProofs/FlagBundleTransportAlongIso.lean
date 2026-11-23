import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFlag
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagIsoBundle

theorem pull_natural {B Y T : Scheme.{0}} (π : Y ⟶ B) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g)
    {M N : B.Modules} (f : M ⟶ N) :
    (Scheme.Modules.pullback g').map ((Scheme.Modules.pullback π).map f) ≫
        (Scheme.Modules.pullbackComp g' π).hom.app N ≫ (Scheme.Modules.pullbackCongr w).hom.app N =
      (Scheme.Modules.pullbackComp g' π).hom.app M ≫ (Scheme.Modules.pullbackCongr w).hom.app M ≫
        (Scheme.Modules.pullback g).map f := by
  have h1 := (Scheme.Modules.pullbackComp g' π).hom.naturality f
  have h2 := (Scheme.Modules.pullbackCongr w).hom.naturality f
  simp only [Functor.comp_map] at h1
  rw [← Category.assoc, h1, Category.assoc, h2]

theorem isFlagBundle_of_iso : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (E E' : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (e : ∀ a, E a ≅ E' a), IsFlagBundle π E r fl → IsFlagBundle π E' r (fun a => (fl a).ofIso ((Scheme.Modules.pullback π).mapIso (e a))) := by
  intro B Y π ι E E' r fl e h T g fl''
  obtain ⟨g', ⟨w, H⟩, uniq⟩ := h T g fun a =>
    (fl'' a).ofIso ((Scheme.Modules.pullback g).mapIso (e a)).symm
  refine ⟨g', ⟨w, fun a i => ?_⟩, fun y ⟨w', H'⟩ => uniq y ⟨w', fun a i => ?_⟩⟩
  · obtain ⟨e0, he0⟩ := H a i
    refine ⟨e0, ?_⟩
    have k := pull_natural π g' g w (e a).hom
    simp only [Vert.Flag.ofIso, Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom, Functor.map_comp,
      Category.assoc] at he0 ⊢
    rw [k, ← reassoc_of% he0, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
  · obtain ⟨e1, he1⟩ := H' a i
    refine ⟨e1, ?_⟩
    have k := pull_natural π y g w' (e a).hom
    simp only [Vert.Flag.ofIso, Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom, Functor.map_comp,
      Category.assoc] at he1 ⊢
    rw [reassoc_of% he1, reassoc_of% k, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

end GlobalTheory.FlagIsoBundle
