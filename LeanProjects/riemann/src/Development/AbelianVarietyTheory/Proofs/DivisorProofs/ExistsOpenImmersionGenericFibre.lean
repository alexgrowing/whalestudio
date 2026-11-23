import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupCyclotomicAwayProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtOfSecCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyQuasiFiniteOfFiniteGeometricFibres
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecCoordOfSubsingletonPic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.SecCompact

theorem exists_openImmersion_genericFibre (F : Type) [Field F] (o : Type) [CommRing o] [Algebra o F]
    [IsFractionRing o F] [Algebra.FiniteType ℤ o] (m : ℕ) (X : Scheme.{0}) (sX : X ⟶ Sp F) [IsReduced X]
    [IsSeparated sX] [LocallyOfFiniteType sX] [QuasiCompact sX] (f : X ⟶ PSpace o m) [QuasiCompact f]
    [QuasiSeparated f] (hf : f ≫ PSpace.str o m = sX ≫ spMap (algebraMap o F))
    (hfib : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X),
      Set.Finite {y : Sp K ⟶ X | y ≫ sX = x ≫ sX ∧ y ≫ f = x ≫ f}) :
    IsFinite f.fromNormalization ∧
      ∃ iF : X ⟶ pullback (f.fromNormalization ≫ PSpace.str o m) (spMap (algebraMap o F)),
        IsOpenImmersion iF ∧ Dense (Set.range iF) ∧ iF ≫ pullback.snd _ _ = sX ∧
          iF ≫ pullback.fst _ _ = f.toNormalization := by
  haveI := isProper_str o m
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI := IsPreimmersion.of_isLocalization (R := o) (S := F) (nonZeroDivisors o)
  haveI : Algebra.FiniteType ℤ (CommRingCat.of o) := ‹Algebra.FiniteType ℤ o›
  refine ⟨GlobalTheory.NormBlowupInt.isFinite_fromNormalization_int_of_isReduced (o := CommRingCat.of o) f
    (PSpace.str o m) fun x _ => ?_, ?_⟩
  · have h1 : ((f ≫ PSpace.str o m).stalkMap x).hom.EssFiniteType := by
      rw [hf, Scheme.Hom.stalkMap_comp]
      exact .comp (RingHom.FiniteType.of_surjective _
        (Scheme.Hom.stalkMap_surjective _ _)).essFiniteType (LocallyOfFiniteType.stalkMap sX x)
    rw [Scheme.Hom.stalkMap_comp] at h1
    have h2 : (f.stalkMap x).hom.EssFiniteType := .of_comp _ h1
    exact h2.residueFieldMap
  have hb := IsPullback.of_hasPullback (PSpace.str o m) (spMap (algebraMap o F))
  let f' : X ⟶ pullback (PSpace.str o m) (spMap (algebraMap o F)) := pullback.lift f sX hf
  have e₁ : f' ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have e₂ : f' ≫ pullback.snd _ _ = sX := pullback.lift_snd _ _ _
  haveI : LocallyOfFiniteType (f' ≫ pullback.snd _ _) := by rw [e₂]; infer_instance
  haveI : LocallyOfFiniteType f' := locallyOfFiniteType_of_comp f' (pullback.snd _ _)
  haveI : QuasiCompact (f' ≫ pullback.snd _ _) := by rw [e₂]; infer_instance
  haveI : QuasiCompact f' := QuasiCompact.of_comp f' (pullback.snd _ _)
  haveI : IsSeparated (f' ≫ pullback.snd _ _) := by rw [e₂]; infer_instance
  haveI : IsSeparated f' := IsSeparated.of_comp f' (pullback.snd _ _)
  haveI : LocallyQuasiFinite f' := by
    refine GlobalTheory.GeomFibre.locallyQuasiFinite_of_finite_geometric_fibres X _ f' inferInstance fun K _ _ x => ?_
    refine (hfib K x).subset fun y (hy : y ≫ f' = x ≫ f') => ⟨?_, ?_⟩
    · rw [← e₂, ← Category.assoc, hy, Category.assoc]
    · rw [← e₁, ← Category.assoc, hy, Category.assoc]
  obtain ⟨hoi, -, hdom⟩ :=
    GlobalTheory.isOpenImmersion_lift_toNormalization_of_isLocalization (nonZeroDivisors o) hb f' f e₁.symm
  refine ⟨pullback.lift f.toNormalization f' (by simp [e₁]) ≫
    (pullbackRightPullbackFstIso (PSpace.str o m) (spMap (algebraMap o F)) f.fromNormalization).hom,
    inferInstance, (Scheme.Hom.denseRange _), ?_, ?_⟩
  · rw [Category.assoc, pullbackRightPullbackFstIso_hom_snd, pullback.lift_snd_assoc, e₂]
  · rw [Category.assoc, pullbackRightPullbackFstIso_hom_fst, pullback.lift_fst]

end GlobalTheory.SecCompact
