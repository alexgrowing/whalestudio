import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfIsSchemeTheoreticallyDominantOfFractionRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGrpObjOfFlatClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory

namespace IsogenyModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
private theorem over_pullback_map_left_fst {S S' : Scheme} (φ : S' ⟶ S) (Ga X : Over S) (io : Ga ⟶ X) :
    ((Over.pullback φ).map io).left ≫ pullback.fst X.hom φ = pullback.fst _ _ ≫ io.left :=
  pullback.lift_fst _ _ _

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
private theorem over_pullback_map_left_snd {S S' : Scheme} (φ : S' ⟶ S) (Ga X : Over S) (io : Ga ⟶ X) :
    ((Over.pullback φ).map io).left ≫ pullback.snd X.hom φ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in

theorem _root_.GlobalTheory.IsogenyModel.exists_flat_closure (T K : Type) [CommRing T] [IsDedekindDomain T] [Field K] [Algebra T K]
    [IsFractionRing T K] (X : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp T)) (Z : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K))
    (i : Z ⟶ (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))).obj X) (hi : IsClosedImmersion i.left) :
    ∃ (Ga : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp T)) (io : Ga ⟶ X)
      (e : (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))).obj Ga ≅ Z), IsClosedImmersion io.left ∧
      Flat Ga.hom ∧ e.hom ≫ i = (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))).map io := by
  haveI := hi
  haveI : Flat (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) := _root_.GlobalTheory.flat_specMap_localization (nonZeroDivisors T) K
  haveI : Mono (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) := _root_.GlobalTheory.mono_specMap_localization (nonZeroDivisors T) K
  set u := pullback.fst X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) with hu
  set j := i.left ≫ u with hj
  have hjs : Z.hom ≫ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) = j ≫ X.hom := by
    rw [hj, Category.assoc, hu, pullback.condition, ← Category.assoc]
    congr 1
    exact (Over.w i).symm
  haveI : QuasiCompact (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) := by dsimp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]; infer_instance
  haveI : QuasiCompact j := by rw [hj, hu]; infer_instance
  have hflat : Flat (j.imageι ≫ X.hom) :=
    _root_.GlobalTheory.flat_image_of_over_fractionField j X.hom Z.hom hjs
  have hA : IsPullback i.left j.toImage u j.imageι :=
    _root_.GlobalTheory.isPullback_toImage_of_isClosedImmersion j i.left u rfl
  have hB : IsPullback u (pullback.snd X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))) X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) := IsPullback.of_hasPullback X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))
  have hC : IsPullback j.toImage (i.left ≫ pullback.snd X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))) (j.imageι ≫ X.hom) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) :=
    IsPullback.paste_vert hA.flip hB
  have hZ : i.left ≫ pullback.snd X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) = Z.hom := Over.w i
  rw [hZ] at hC
  refine ⟨Over.mk (j.imageι ≫ X.hom), Over.homMk j.imageι rfl,
    Over.isoMk hC.isoPullback.symm (by simp), (show IsClosedImmersion j.imageι from inferInstance), hflat, ?_⟩
  ext1
  simp only [Over.comp_left, Over.isoMk_hom_left, Iso.symm_hom]
  rw [Iso.inv_comp_eq]
  apply pullback.hom_ext
  · rw [Category.assoc, over_pullback_map_left_fst]
    erw [hC.isoPullback_hom_fst_assoc]
    simp [hj, hu]
  · rw [Category.assoc, over_pullback_map_left_snd]
    erw [hC.isoPullback_hom_snd]
    exact hZ

variable {S : Scheme.{0}}

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
variable {S : Scheme.{0}} in

theorem _root_.GlobalTheory.IsogenyModel.exists_kernel {G B : Over S} [GrpObj G] [GrpObj B] [IsSeparated B.hom] (f : G ⟶ B)
    [IsMonHom f] [IsFinite f.left] :
    ∃ (Z : Over S) (_ : GrpObj Z) (i : Z ⟶ G), IsMonHom i ∧ IsClosedImmersion i.left ∧
      IsFinite Z.hom ∧ IsPullback i (toUnit Z) f η[B] := by
  have hP := IsPullback.of_hasPullback f η[B]
  have hL := IsPullback.map (Over.forget S) hP
  haveI : IsClosedImmersion η[B].left :=
    _root_.GlobalTheory.Retract.isClosedImmersion_section (f := 𝟙 S) (r := B.hom) (Over.w η[B])
      (Category.comp_id _)
  haveI : Mono η[B] := ⟨fun a b _ => toUnit_unique a b⟩
  set i := pullback.fst f η[B] with hi
  have key : ∀ {X : Over S} (a : X ⟶ pullback f η[B]), (a ≫ i) ≫ f = 1 := fun a => by
    rw [Category.assoc, hi, pullback.condition, ← Category.assoc,
      toUnit_unique (a ≫ pullback.snd f η[B]) (toUnit _), ← Hom.one_def]
  have key1 : i ≫ f = 1 := by simpa using key (𝟙 _)
  have hinv : ∀ {X : Over S} (a : X ⟶ G), a⁻¹ ≫ f = (a ≫ f)⁻¹ := by
    intro X a
    exact GrpObj.inv_comp a f
  obtain ⟨inst, hmon⟩ := _root_.GlobalTheory.exists_grpObj_of_mono i
    (pullback.lift η[G] (𝟙 _) (by simp))
    (pullback.lift ((fst _ _ ≫ i) * (snd _ _ ≫ i)) (toUnit _)
      (by rw [mul_comp, key, key, _root_.mul_one, Hom.one_def]))
    (pullback.lift i⁻¹ (toUnit _) (by rw [hinv, key1, _root_.inv_one, Hom.one_def]))
    (pullback.lift_fst _ _ _)
    (by rw [pullback.lift_fst, Hom.mul_def, lift_fst_comp_snd_comp])
    (by rw [pullback.lift_fst, Hom.inv_def])
  refine ⟨pullback f η[B], inst, i, hmon, ?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hL.flip (show IsClosedImmersion η[B].left from inferInstance)
  · have hw := Over.w (pullback.snd f η[B])
    have : IsFinite (pullback.snd f η[B]).left :=
      MorphismProperty.of_isPullback (P := @IsFinite) hL (show IsFinite f.left from inferInstance)
    rw [← hw]
    simpa using this
  · simpa [toUnit_unique (pullback.snd f η[B]) (toUnit _)] using hP

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
variable {S : Scheme.{0}} in

theorem _root_.GlobalTheory.IsogenyModel.exists_iso_of_same_kernel {G A B Z : Over S} [GrpObj G] [GrpObj A] [GrpObj B]
    (q : G ⟶ A) (f : G ⟶ B) (i : Z ⟶ G) [IsMonHom q] [IsMonHom f] [Flat q.left]
    [Surjective q.left] [QuasiCompact q.left] [Surjective f.left] [IsProper A.hom]
    [IsSeparated B.hom] [IsReduced B.left] (hq : IsPullback i (toUnit Z) q η[A])
    (hf : IsPullback i (toUnit Z) f η[B]) :
    ∃ e : A ≅ B, IsMonHom e.hom ∧ q ≫ e.hom = f := by
  obtain ⟨β, hβ, hqβ⟩ := _root_.GlobalTheory.FlatQuotient.exists_desc q i f hq hf.w
  have htriv : ∀ {X : Over S} (x : X ⟶ A), x ≫ β = 1 → x = 1 := by
    intro X x hx
    have hP := IsPullback.of_hasPullback x q
    have hL := IsPullback.map (Over.forget S) hP
    haveI : Flat (pullback.fst x q).left :=
      MorphismProperty.of_isPullback (P := @Flat) hL.flip (show Flat q.left from inferInstance)
    haveI : Surjective (pullback.fst x q).left :=
      MorphismProperty.of_isPullback (P := @Surjective) hL.flip
        (show Surjective q.left from inferInstance)
    haveI : Epi (pullback.fst x q) := _root_.GlobalTheory.FlatQuotient.epi_of_flat_surjective _
    have hg : pullback.snd x q ≫ f = toUnit _ ≫ η[B] := by
      rw [← hqβ, ← Category.assoc, ← pullback.condition, Category.assoc, hx, Hom.one_def,
        ← Category.assoc, toUnit_unique (pullback.fst x q ≫ toUnit X) (toUnit _)]
    have hgq : pullback.snd x q ≫ q = toUnit _ ≫ η[A] := by
      rw [← hf.lift_fst _ _ hg, Category.assoc, hq.w, ← Category.assoc,
        toUnit_unique (hf.lift _ _ hg ≫ toUnit Z) (toUnit _)]
    rw [← cancel_epi (pullback.fst x q), pullback.condition, hgq, Hom.one_def, ← Category.assoc,
      toUnit_unique (pullback.fst x q ≫ toUnit X) (toUnit _)]
  haveI : Mono β := ⟨fun a b hab => by
    have h1 : (a * b⁻¹) ≫ β = 1 := by
      rw [mul_comp, GrpObj.inv_comp, hab, _root_.mul_inv_cancel]
    have h2 := htriv _ h1
    exact (mul_inv_eq_one.mp h2)⟩
  haveI : Surjective (q.left ≫ β.left) := by
    rw [← Over.comp_left, hqβ]; infer_instance
  haveI : Surjective β.left := Surjective.of_comp q.left β.left
  haveI : IsProper (β.left ≫ B.hom) := by rw [Over.w β]; infer_instance
  haveI : IsProper β.left := IsProper.of_comp β.left B.hom
  haveI : IsClosedImmersion β.left :=
    (IsClosedImmersion.iff_isProper_and_mono (f := β.left)).mpr ⟨inferInstance, inferInstance⟩
  haveI : IsIso β.left := isIso_of_isClosedImmersion_of_surjective β.left
  refine ⟨Over.isoMk (asIso β.left) (Over.w β), ?_, ?_⟩
  · have : (Over.isoMk (asIso β.left) (Over.w β)).hom = β := by ext1; rfl
    rw [this]; exact hβ
  · have : (Over.isoMk (asIso β.left) (Over.w β)).hom = β := by ext1; rfl
    rw [this]; exact hqβ

end IsogenyModel

end GlobalTheory
