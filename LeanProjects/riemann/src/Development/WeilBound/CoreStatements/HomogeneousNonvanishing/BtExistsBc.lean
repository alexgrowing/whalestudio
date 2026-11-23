import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace PositivityTheory.UnitarySelfGeneration

open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

noncomputable def genSec (Γ : QFGroup R T) (t : T) :
    Spec (CommRingCat.of (FractionRing R)) ⟶ pullback Γ.G.hom (genPt R).hom :=
  pullback.lift (Γ.pt t).left (𝟙 _) (by rw [Category.id_comp]; exact Over.w (Γ.pt t))

theorem genSec_fst (Γ : QFGroup R T) (t : T) : genSec Γ t ≫ pullback.fst _ _ = (Γ.pt t).left :=
  pullback.lift_fst _ _ _

theorem genSec_snd (Γ : QFGroup R T) (t : T) : genSec Γ t ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

theorem gen_asIdeal (z : Spec (CommRingCat.of (FractionRing R))) : ((genPt R).hom z).asIdeal = ⊥ := by
  have hz : z.asIdeal = ⊥ := (Ideal.eq_bot_or_top z.asIdeal).resolve_right z.2.ne_top
  show Ideal.comap (algebraMap R (FractionRing R)) z.asIdeal = ⊥
  rw [hz]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))

theorem genSec_cover (Γ : QFGroup R T) (a : ↥(pullback Γ.G.hom (genPt R).hom)) : ∃ t z, genSec Γ t z = a := by
  haveI : IsPreimmersion (genPt R).hom := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h1 : Γ.G.hom (pullback.fst Γ.G.hom (genPt R).hom a) = (genPt R).hom (pullback.snd Γ.G.hom (genPt R).hom a) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  obtain ⟨t, z, hz⟩ := Γ.pt_onto (pullback.fst Γ.G.hom (genPt R).hom a) (by rw [h1]; exact gen_asIdeal _)
  refine ⟨t, z, (pullback.fst Γ.G.hom (genPt R).hom).isEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, genSec_fst, hz]

theorem genSec_open [Finite T] (Γ : QFGroup R T) (t : T) : IsOpenImmersion (genSec Γ t) := by
  haveI := Γ.separated
  haveI := Γ.gen_reduced
  have hcl : ∀ s, IsClosedImmersion (genSec Γ s) := fun s => by
    haveI : IsClosedImmersion (genSec Γ s ≫ pullback.snd _ _) := by rw [genSec_snd]; infer_instance
    exact IsClosedImmersion.of_comp _ (pullback.snd Γ.G.hom (genPt R).hom)
  haveI : Subsingleton ↥(Spec (CommRingCat.of (FractionRing R))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  let z₀ : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  haveI : Finite ↥(pullback Γ.G.hom (genPt R).hom) :=
    Finite.of_surjective (fun s => genSec Γ s z₀) fun a => by
      obtain ⟨s, z, rfl⟩ := genSec_cover Γ a
      exact ⟨s, by rw [Subsingleton.elim z z₀]⟩
  haveI : T1Space ↥(pullback Γ.G.hom (genPt R).hom) := ⟨fun a => by
    obtain ⟨s, z, rfl⟩ := genSec_cover Γ a
    haveI := hcl s
    have := (genSec Γ s).isClosedEmbedding.isClosedMap {z} (isClosed_discrete _)
    rwa [Set.image_singleton] at this⟩
  let U : (pullback Γ.G.hom (genPt R).hom).Opens := ⟨{genSec Γ t z₀}, isOpen_discrete _⟩
  have hU : Set.range (genSec Γ t) ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim z z₀]
    exact rfl
  have e := IsOpenImmersion.lift_fac U.ι (genSec Γ t) hU
  haveI : IsClosedImmersion (IsOpenImmersion.lift U.ι (genSec Γ t) hU ≫ U.ι) := by rw [e]; exact hcl t
  haveI : IsClosedImmersion (IsOpenImmersion.lift U.ι (genSec Γ t) hU) := IsClosedImmersion.of_comp _ U.ι
  haveI : Surjective (IsOpenImmersion.lift U.ι (genSec Γ t) hU) := ⟨fun u => ⟨z₀, by
    apply U.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, e]
    exact (u.2 : u.1 = _).symm⟩⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (IsOpenImmersion.lift U.ι (genSec Γ t) hU)
  rw [← e]
  infer_instance

variable {R' : Type} [CommRing R'] [IsDomain R']

noncomputable def fracMap {φ : R →+* R'} (hφ : Function.Injective φ) : FractionRing R →+* FractionRing R' :=
  IsFractionRing.lift (g := (algebraMap R' (FractionRing R')).comp φ)
    ((IsFractionRing.injective R' (FractionRing R')).comp hφ)

theorem fracMap_comp {φ : R →+* R'} (hφ : Function.Injective φ) :
    (fracMap hφ).comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp φ := by
  refine RingHom.ext fun a => ?_
  rw [RingHom.comp_apply, fracMap, IsFractionRing.lift_algebraMap]

theorem fracMap_sq {φ : R →+* R'} (hφ : Function.Injective φ) :
    spMap (fracMap hφ) ≫ (genPt R).hom = (genPt R').hom ≫ spMap φ := by
  show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, fracMap_comp]

noncomputable def bcPt (Γ : QFGroup R T) {φ : R →+* R'} (hφ : Function.Injective φ) (t : T) :
    genPt R' ⟶ (Over.pullback (spMap φ)).obj Γ.G :=
  Over.homMk (pullback.lift (spMap (fracMap hφ) ≫ (Γ.pt t).left) (genPt R').hom (by
    rw [Category.assoc, Over.w (Γ.pt t), fracMap_sq])) (pullback.lift_snd _ _ _)

theorem bcPt_fst (Γ : QFGroup R T) {φ : R →+* R'} (hφ : Function.Injective φ) (t : T) :
    (bcPt Γ hφ t).left ≫ pullback.fst Γ.G.hom (spMap φ) = spMap (fracMap hφ) ≫ (Γ.pt t).left :=
  pullback.lift_fst _ _ _

theorem bcPt_mul (Γ : QFGroup R T) {φ : R →+* R'} (hφ : Function.Injective φ) (s t : T) :
    bcPt Γ hφ (s * t) = bcPt Γ hφ s * bcPt Γ hφ t := by
  have h := isGrpPullback_pullback Γ.G (spMap φ)
  let U : Over.mk ((genPt R').hom ≫ spMap φ) ⟶ genPt R := Over.homMk (spMap (fracMap hφ)) (fracMap_sq hφ)
  refine Over.OverMorphism.ext (h.1.hom_ext ?_ ?_)
  · rw [← h.2 (genPt R') (bcPt Γ hφ s) (bcPt Γ hφ t) (U ≫ Γ.pt s) (U ≫ Γ.pt t) (bcPt_fst Γ hφ s).symm
      (bcPt_fst Γ hφ t).symm, ← MonObj.comp_mul, ← map_mul]
    exact bcPt_fst Γ hφ _
  · exact (Over.w _).trans (Over.w _).symm

noncomputable def bcSec (Γ : QFGroup R T) {φ : R →+* R'} (hφ : Function.Injective φ) (t : T) :
    Spec (CommRingCat.of (FractionRing R')) ⟶ pullback (pullback.snd Γ.G.hom (spMap φ)) (genPt R').hom :=
  pullback.lift (bcPt Γ hφ t).left (𝟙 _) (by rw [Category.id_comp]; exact Over.w (bcPt Γ hφ t))

theorem bcSec_spec [Finite T] (Γ : QFGroup R T) {φ : R →+* R'} (hφ : Function.Injective φ) :
    (∀ t, IsOpenImmersion (bcSec Γ hφ t)) ∧ ∀ a, ∃ t z, bcSec Γ hφ t z = a := by
  let q : pullback (pullback.snd Γ.G.hom (spMap φ)) (genPt R').hom ⟶ pullback Γ.G.hom (genPt R).hom :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ spMap (fracMap hφ)) (by
      rw [Category.assoc, Category.assoc, fracMap_sq, pullback.condition, pullback.condition_assoc])
  have hq₁ : q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
  have hq₂ : q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (fracMap hφ) := pullback.lift_snd _ _ _
  have big := (IsPullback.of_hasPullback (pullback.snd Γ.G.hom (spMap φ)) (genPt R').hom).paste_horiz
    (IsPullback.of_hasPullback Γ.G.hom (spMap φ))
  rw [← hq₁, ← fracMap_sq hφ] at big
  have hq : IsPullback q (pullback.snd _ _) (pullback.snd _ _) (spMap (fracMap hφ)) :=
    big.of_right hq₂ (IsPullback.of_hasPullback Γ.G.hom (genPt R).hom)
  have hs : ∀ t, IsPullback (spMap (fracMap hφ)) (bcSec Γ hφ t) (genSec Γ t) q := fun t => by
    have e₁ : bcSec Γ hφ t ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have e₂ : bcSec Γ hφ t ≫ pullback.fst _ _ = (bcPt Γ hφ t).left := pullback.lift_fst _ _ _
    refine IsPullback.of_bot ?_ ?_ hq
    · rw [e₁, genSec_snd]
      exact IsPullback.of_vert_isIso ⟨by simp⟩
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, genSec_fst, hq₁, reassoc_of% e₂, bcPt_fst]
      · rw [Category.assoc, Category.assoc, genSec_snd, hq₂, reassoc_of% e₁, Category.comp_id]
  refine ⟨fun t => ?_, fun a => ?_⟩
  · haveI := genSec_open Γ t
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hs t) this
  · obtain ⟨t, z, hz⟩ := genSec_cover Γ (q a)
    obtain ⟨w, -, hw⟩ := Scheme.exists_preimage_of_isPullback (hs t) z a hz
    exact ⟨t, w, hw⟩

noncomputable def bcGroup [Finite T] (Γ : QFGroup R T) {φ : R →+* R'} (hφ : Function.Injective φ) : QFGroup R' T where
  G := (Over.pullback (spMap φ)).obj Γ.G
  flat := haveI := Γ.flat; inferInstanceAs (Flat (pullback.snd Γ.G.hom (spMap φ)))
  quasiFinite := haveI := Γ.quasiFinite; inferInstanceAs (LocallyQuasiFinite (pullback.snd Γ.G.hom (spMap φ)))
  separated := haveI := Γ.separated; inferInstanceAs (IsSeparated (pullback.snd Γ.G.hom (spMap φ)))
  quasiCompact := haveI := Γ.quasiCompact; inferInstanceAs (QuasiCompact (pullback.snd Γ.G.hom (spMap φ)))
  finPres := haveI := Γ.finPres; inferInstanceAs (LocallyOfFinitePresentation (pullback.snd Γ.G.hom (spMap φ)))
  pt := MonoidHom.mk' (bcPt Γ hφ) (bcPt_mul Γ hφ)
  pt_inj s t x y h := by
    refine Γ.pt_inj s t (spMap (fracMap hφ) x) (spMap (fracMap hφ) y) ?_
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← bcPt_fst, ← bcPt_fst, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]
    exact congrArg _ h
  pt_onto g hg := by
    let z₀ : Spec (CommRingCat.of (FractionRing R')) := IsLocalRing.closedPoint (FractionRing R')
    obtain ⟨a, ha, -⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_hasPullback (pullback.snd Γ.G.hom (spMap φ)) (genPt R').hom) g z₀
      (PrimeSpectrum.ext (hg.trans (gen_asIdeal z₀).symm))
    obtain ⟨t, z, rfl⟩ := (bcSec_spec Γ hφ).2 a
    refine ⟨t, z, ?_⟩
    rw [← ha, ← Scheme.Hom.comp_apply]
    have e₂ : bcSec Γ hφ t ≫ pullback.fst _ _ = (bcPt Γ hφ t).left := pullback.lift_fst _ _ _
    rw [e₂]
    rfl
  gen_reduced := by
    haveI : ∀ a : ↥(pullback (pullback.snd Γ.G.hom (spMap φ)) (genPt R').hom),
        _root_.IsReduced ((pullback (pullback.snd Γ.G.hom (spMap φ)) (genPt R').hom).presheaf.stalk a) := fun a => by
      obtain ⟨t, z, rfl⟩ := (bcSec_spec Γ hφ).2 a
      haveI := (bcSec_spec Γ hφ).1 t
      exact isReduced_of_injective ((bcSec Γ hφ t).stalkMap z).hom
        (ConcreteCategory.bijective_of_isIso ((bcSec Γ hφ t).stalkMap z)).1
    exact isReduced_of_isReduced_stalk (pullback (pullback.snd Γ.G.hom (spMap φ)) (genPt R').hom)

theorem bt_exists_bc : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R'), Function.Injective φ → ∃ (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ φ F := by
  intro R _ _ T _ _ Γ R' _ _ φ hφ
  have h := isGrpPullback_pullback Γ.G (spMap φ)
  refine ⟨bcGroup Γ hφ, pullback.fst Γ.G.hom (spMap φ), h.1, h.2, FractionRing R, inferInstance, algebraMap R _,
    RingHom.id _, fracMap hφ, fun t => (Γ.pt t).left, Function.injective_id, rfl, fracMap_comp hφ,
    fun t => Over.w (Γ.pt t), fun t => ?_, fun t => (bcPt_fst Γ hφ t).symm⟩
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

end PositivityTheory.UnitarySelfGeneration
