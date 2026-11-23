import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.liftFF_of :
    AlgOf → LiftPt → LiftFF := by
  intro hAlg hPt S K h hfin hflat V _ _ _ _ z g hg
  obtain ⟨B, _, _, k, hfinB, hfreeB, hp⟩ := hAlg S K h hfin hflat V z
  haveI : Module.Finite V B := hfinB
  haveI : Module.Free V B := hfreeB
  let u : Sp (IsLocalRing.ResidueField V) ⟶ Sp B := hp.lift g (resPt V) hg
  have huk : u ≫ k = g := hp.lift_fst _ _ _
  have hua : u ≫ spMap (algebraMap V B) = resPt V := hp.lift_snd _ _ _
  let χ : B →+* IsLocalRing.ResidueField V := (Spec.preimage u).hom
  have hχ : spMap χ = u := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage u).hom) = u
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hχa : χ.comp (algebraMap V B) = IsLocalRing.residue V := by
    have h1 : Spec.map (CommRingCat.ofHom (χ.comp (algebraMap V B))) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
      exact (congrArg (· ≫ spMap (algebraMap V B)) hχ).trans hua
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  obtain ⟨z₀, hz₀⟩ := hPt V B χ hχa
  refine ⟨spMap z₀.toRingHom ≫ k, ?_, ?_⟩
  · have hc : z₀.toRingHom.comp (algebraMap V B) = RingHom.id V := by
      ext x
      exact z₀.commutes x
    have h3 : spMap z₀.toRingHom ≫ spMap (algebraMap V B) = 𝟙 _ := by
      show Spec.map (CommRingCat.ofHom z₀.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap V B)) = 𝟙 _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
      exact Spec.map_id _
    rw [Category.assoc, hp.w, ← Category.assoc, h3, Category.id_comp]
  · have h4 : resPt V ≫ spMap z₀.toRingHom = u := by
      rw [← hχ, ← hz₀]
      show Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) ≫ Spec.map (CommRingCat.ofHom z₀.toRingHom) =
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue V).comp z₀.toRingHom))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← Category.assoc, h4, huk]
