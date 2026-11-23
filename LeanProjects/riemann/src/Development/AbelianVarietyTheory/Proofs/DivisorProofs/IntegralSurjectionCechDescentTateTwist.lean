import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfStalkwiseBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAugEqvOfIsIntegralHomOfStrictlyHenselianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCechNerveAugmentationIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem eqv_cechAug_of_comp_iso (R : Type) [CommRing R] (F : Shv R) {V W T : Scheme.{0}} (g : V ⟶ W) (t : W ⟶ T) [IsIso t]
    (h : Eqv R (cechAug (g ≫ t)) F) : Eqv R (cechAug g) F := by
  have E := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  let e : Arrow.mk (yoneda.map g) ≅ Arrow.mk (yoneda.map (g ≫ t)) :=
    Arrow.isoMk (Iso.refl _) (yoneda.mapIso (asIso t)) (by simp)
  let φ := SimplicialObject.augmentedCechNerve.mapIso e
  have hw : φ.hom.left ≫ cechAug (g ≫ t) = cechAug g ≫ (SimplicialObject.const _).map φ.hom.right := φ.hom.w
  have hl : IsIso φ.hom.left := (SimplicialObject.Augmented.drop.mapIso φ).isIso_hom
  have hr : IsIso ((SimplicialObject.const _).map φ.hom.right) := by
    have : IsIso φ.hom.right := (SimplicialObject.Augmented.point.mapIso φ).isIso_hom
    infer_instance
  have h1 : Eqv R (φ.hom.left ≫ cechAug (g ≫ t)) F := ((E.2.1 _ _ _ _ _).1 (E.1 _ _ _ hl)) h
  rw [hw] at h1
  exact (E.2.1 _ _ _ _ _).2.2 (E.1 _ _ _ hr) h1

theorem b4 : B4 := by
  intro q Y X f _ _ hq i
  have E := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  refine GlobalTheory.T.equiv_of_stalkwise_base_change (ZMod q) (tw q i) X (cech f) (sch.obj X) (cechAug f) (sch.map (𝟙 X))
    (GlobalTheory.T.tateTwist_finitary q i) ?_ ?_ ?_
  · intro k
    obtain ⟨Z, π, e, hπ, he⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsIntegralHom Y X f ‹_› k
    haveI := hπ
    refine ⟨Z, π ≫ f, e, inferInstance, inferInstance, ?_⟩
    rw [CategoryTheory.Functor.map_id, Category.comp_id, he]
  · intro k
    refine ⟨X, 𝟙 X, Iso.refl _, inferInstance, inferInstance, ?_⟩
    simp [sch]
  · intro O _ s hs
    obtain ⟨e₁, e₂, h⟩ := GlobalTheory.T.baseChange_cechNerveAugmentation_iso X X Y (𝟙 X) f (Over.mk s)
    have hqO : IsUnit ((q : ℕ) : O) := by
      have := hq.map (s.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of O)).hom).hom
      simpa using this
    have hg : Eqv _ (cechAug (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom))) (tw q i) :=
      eqv_cechAug_of_comp_iso _ _ _ (pullback.snd (𝟙 X) s)
        (GlobalTheory.T.eqv_cechAug_of_isIntegralHom_of_surjective_of_sh q i O hs.1 hqO _ _ inferInstance inferInstance)
    have hm : (bcMap (cechAug f) (sch.map (𝟙 X))).app (Over.mk s) =
        e₁.inv ≫ cechAug (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom)) ≫ e₂.hom := by
      rw [← h, Iso.inv_hom_id_assoc]
    rw [hm]
    exact (E.2.1 _ _ _ _ _).1 (E.1 _ _ _ inferInstance) ((E.2.1 _ _ _ _ _).1 hg (E.1 _ _ _ inferInstance))

end GlobalTheory.EtC
