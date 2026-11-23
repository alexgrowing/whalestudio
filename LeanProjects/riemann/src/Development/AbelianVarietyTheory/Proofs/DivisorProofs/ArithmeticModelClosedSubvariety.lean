import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalModelOverProjective
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

theorem exists_isPre_closure : ∀ (F F' : Type) [Field F] [NumberField F] [Field F'] (e : F ≃+* F') (T : Scheme.{0}) (sT : T ⟶ Sp (𝓞 F')), IsProjOver sT → ∀ (V : Scheme.{0}) [IsIntegral V] (j : V ⟶ Limits.pullback sT (spMap (algebraMap (𝓞 F') F'))), IsClosedImmersion j → ∀ d : ℕ, topologicalKrullDim V = d → ∃ (X W : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (jB : W ⟶ X) (πB : W ⟶ Limits.pullback sT (spMap (algebraMap (𝓞 F') F'))) (ρ : X ⟶ T), IsPre (Limits.pullback.snd sT (spMap (algebraMap (𝓞 F') F')) ≫ spMap e.toRingHom) (Set.range j) d (Limits.pullback.fst sT (spMap (algebraMap (𝓞 F') F'))) q jB πB ρ := by
  intro F F' _ _ _ e T sT hT V _ j hj d hd
  have : CharZero F' := e.symm.toRingHom.charZero
  have : NumberField F' := NumberField.of_ringEquiv F F' e
  let ε : 𝓞 F ≃+* 𝓞 F' := RingOfIntegers.mapRingEquiv e
  have hb := IsPullback.of_hasPullback sT (spMap (algebraMap (𝓞 F') F'))
  let h : V ⟶ T := j ≫ Limits.pullback.fst _ _
  have hh : j ≫ Limits.pullback.fst _ _ = h := rfl
  have w : h ≫ sT = (j ≫ Limits.pullback.snd _ _) ≫ spMap (algebraMap (𝓞 F') F') := by
    rw [← hh, Category.assoc, Category.assoc, Limits.pullback.condition]
  have : IsAffineHom (Limits.pullback.fst sT (spMap (algebraMap (𝓞 F') F'))) :=
    MorphismProperty.of_isPullback hb.flip (isAffineHom_of_isAffine _)
  have : QuasiCompact h := by rw [← hh]; infer_instance
  have : Flat (spMap (algebraMap (𝓞 F') F')) := flat_specMap_localization (nonZeroDivisors (𝓞 F')) F'
  have : Mono (spMap (algebraMap (𝓞 F') F')) := mono_specMap_localization (nonZeroDivisors (𝓞 F')) F'
  have hpb := isPullback_toImage_of_isClosedImmersion h j _ hh
  have H' := hpb.flip.paste_vert hb
  have i1 : IsIso (spMap ε.toRingHom) := by
    have : IsIso (CommRingCat.ofHom ε.toRingHom) := (ε.toCommRingCatIso).isIso_hom
    exact inferInstance
  have i2 : IsIso (spMap e.toRingHom) := by
    have : IsIso (CommRingCat.ofHom e.toRingHom) := (e.toCommRingCatIso).isIso_hom
    exact inferInstance
  have sq : IsPullback (spMap (algebraMap (𝓞 F') F')) (spMap e.toRingHom) (spMap ε.toRingHom)
      (spMap (algebraMap (𝓞 F) F)) := by
    refine IsPullback.of_vert_isIso ⟨?_⟩
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have H := H'.paste_vert sq
  have hP' : IsProjOver (h.imageι ≫ sT) := ProjSpace.isProjOver_comp_of_isClosedImmersion _ hT
  have hP := GlobalTheory.ModelOver.isProjOver_comp_spMap ε hP'
  have hfl' : Flat (h.imageι ≫ sT) := flat_image_of_over_fractionField h sT _ w.symm
  have hfl : Flat ((h.imageι ≫ sT) ≫ spMap ε.toRingHom) := inferInstance
  have hpr := CommonModel.isProper_of_isProjOver hP
  have hdim := GlobalTheory.IntModel.topologicalKrullDim_eq_succ (RingOfIntegers.not_isField F) H hd
  refine ⟨h.image, V, (h.imageι ≫ sT) ≫ spMap ε.toRingHom, h.toImage, j, h.imageι,
    ⟨inferInstance, inferInstance, inferInstance, hP, ?_, hdim⟩, ?_, inferInstance, rfl, h.toImage_imageι⟩
  · have : Flat (spMap (Int.castRingHom (𝓞 F))) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ (𝓞 F))
    infer_instance
  · simpa only [Category.assoc] using H

end GlobalTheory.ArLieBase

end
