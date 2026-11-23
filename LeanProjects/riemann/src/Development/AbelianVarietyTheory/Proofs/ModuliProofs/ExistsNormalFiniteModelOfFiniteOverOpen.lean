import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_normal_finite_model_of_finite_over_open : ∀ (O F : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Field F] [Algebra O F] [IsFractionRing O F] (X U : Scheme.{0}) (s : X ⟶ Sp O) (c : U ⟶ Sp F) (f : U ⟶ X) (W : (pullback s (spMap (algebraMap O F))).Opens) (fW : U ⟶ W.toScheme), IsProjOver s → Geo.Tor.IsNormalScheme U → IsFinite fW → fW ≫ W.ι ≫ pullback.fst _ _ = f → fW ≫ W.ι ≫ pullback.snd _ _ = c → ∃ (Y : Scheme.{0}) (π : Y ⟶ X) (jQ : U ⟶ pullback (π ≫ s) (spMap (algebraMap O F))), IsFinite π ∧ Geo.Tor.IsNormalScheme Y ∧ IsProjOver (π ≫ s) ∧ Flat (π ≫ s) ∧ jQ ≫ pullback.snd _ _ = c ∧ jQ ≫ pullback.fst _ _ ≫ π = f ∧ IsOpenImmersion jQ ∧ Dense (Set.range jQ) ∧ ∀ y : ↥(pullback (π ≫ s) (spMap (algebraMap O F))), y ∈ Set.range jQ ↔ π (pullback.fst (π ≫ s) (spMap (algebraMap O F)) y) ∈ Set.range (W.ι ≫ pullback.fst s (spMap (algebraMap O F))) := by
  intro O F _ _ _ _ _ _ X U s c f W fW hs hU hfW hf hc
  have hprop : IsProper s := (isProjOver_iff_isProper_and_exists_isAmpleLB s).mp hs |>.1
  have hN : GlobalTheory.IsNormalScheme U := .of_pred hU
  have hb : IsPullback (pullback.fst s (spMap (algebraMap O F))) (pullback.snd _ _) s
      (spMap (algebraMap O F)) := .of_hasPullback _ _
  have : IsLocallyNoetherian (pullback s (spMap (algebraMap O F))) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (spMap (algebraMap O F)))
  have : QuasiCompact f := by rw [← hf]; infer_instance
  have : QuasiSeparated f := by rw [← hf]; infer_instance
  have : LocallyOfFiniteType c := by rw [← hc]; infer_instance
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian c
  have w : f ≫ s = c ≫ spMap (algebraMap O F) := by
    rw [← hf, ← hc]; simp only [Category.assoc, pullback.condition]
  have hfin : IsFinite f.fromNormalization :=
    isFinite_fromNormalization_of_over_fractionRing (o := .of O) f s F c w
  have h := isPullback_toNormalization_of_isLocalization (nonZeroDivisors O) hb fW W.ι f hf.symm
  have hb' : IsPullback (pullback.fst (f.fromNormalization ≫ s) (spMap (algebraMap O F)))
      (pullback.snd _ _) (f.fromNormalization ≫ s) (spMap (algebraMap O F)) := .of_hasPullback _ _
  have hpre := isPreimmersion_of_isPullback_localization (nonZeroDivisors O) hb
  have hpre' := isPreimmersion_of_isPullback_localization (nonZeroDivisors O) hb'
  let q : pullback (f.fromNormalization ≫ s) (spMap (algebraMap O F)) ⟶
      pullback s (spMap (algebraMap O F)) :=
    pullback.lift (pullback.fst _ _ ≫ f.fromNormalization) (pullback.snd _ _)
      (by simpa using pullback.condition)
  have hq₁ : q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f.fromNormalization := pullback.lift_fst ..
  have hq₂ : q ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd ..
  have hq : IsPullback (pullback.fst (f.fromNormalization ≫ s) (spMap (algebraMap O F))) q
      f.fromNormalization (pullback.fst s (spMap (algebraMap O F))) :=
    IsPullback.of_bot (by rw [hq₂]; exact hb') hq₁.symm hb
  let j : U ⟶ pullback (f.fromNormalization ≫ s) (spMap (algebraMap O F)) :=
    pullback.lift f.toNormalization c (by simpa using w)
  have hj₁ : j ≫ pullback.fst _ _ = f.toNormalization := pullback.lift_fst ..
  have hj₂ : j ≫ pullback.snd _ _ = c := pullback.lift_snd ..
  have hjq : j ≫ q = fW ≫ W.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hq₁, reassoc_of% hj₁, Category.assoc, hf]
      simp
    · rw [Category.assoc, hq₂, hj₂, Category.assoc, hc]
  have hj : IsPullback j fW q W.ι := IsPullback.of_right (by rw [hj₁]; exact h) hjq hq
  refine ⟨f.normalization, f.fromNormalization, j, hfin, IsNormalScheme.pred _,
    isProjOver_comp_of_isFinite _ hs, flat_fromNormalization_comp f F s c w, hj₂,
    by rw [reassoc_of% hj₁]; simp,
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hj.flip inferInstance, ?_, fun y ↦ ?_⟩
  · rw [hpre'.isEmbedding.isInducing.dense_iff]
    intro y
    have hd : DenseRange f.toNormalization := f.toNormalization.denseRange
    rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, hj₁]
    exact hd _
  · rw [← Scheme.Hom.comp_apply, ← hq₁, Scheme.Hom.comp_apply]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨fW u, by rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply fW, ← hjq]; simp⟩
    · rintro ⟨v, hv⟩
      rw [Scheme.Hom.comp_apply] at hv
      obtain ⟨u, hu, -⟩ := Scheme.exists_preimage_of_isPullback hj y v
        (hpre.isEmbedding.injective hv).symm
      exact ⟨u, hu⟩

end GlobalTheory
