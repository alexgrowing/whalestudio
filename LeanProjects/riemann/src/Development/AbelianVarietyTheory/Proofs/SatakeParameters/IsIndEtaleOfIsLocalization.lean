import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec

open CategoryTheory Limits

noncomputable section

namespace GlobalTheory.IndEtaleLoc

variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) {S : Type} [CommRing S]
  (s : D ⟶ (Functor.const J).obj (CommRingCat.of S)) (M : Submonoid S)

structure Idx where

  j : J

  e : D.obj j
  mem : (s.app j).hom e ∈ M

variable {D s M}

def Idx.unit (j : J) : Idx D s M := ⟨j, 1, by simpa using M.one_mem⟩

theorem app_map_apply {j k : J} (φ : j ⟶ k) (x : D.obj j) :
    (s.app k).hom ((D.map φ).hom x) = (s.app j).hom x := by
  have h := congr(($(s.naturality φ)).hom x)
  simpa using h

instance : SmallCategory (Idx D s M) where
  Hom a b := {φ : a.j ⟶ b.j // ∃ c : D.obj b.j, (D.map φ).hom a.e * c = b.e}
  id a := ⟨𝟙 a.j, 1, by simp⟩
  comp φ ψ := ⟨φ.1 ≫ ψ.1, by
    obtain ⟨c, hc⟩ := φ.2
    obtain ⟨d, hd⟩ := ψ.2
    exact ⟨(D.map ψ.1).hom c * d, by
      rw [Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, ← mul_assoc, ← map_mul, hc,
        hd]⟩⟩
  id_comp _ := Subtype.ext (Category.id_comp _)
  comp_id _ := Subtype.ext (Category.comp_id _)
  assoc _ _ _ := Subtype.ext (Category.assoc _ _ _)

@[simp] theorem comp_val {a b c : Idx D s M} (φ : a ⟶ b) (ψ : b ⟶ c) :
    (φ ≫ ψ).1 = φ.1 ≫ ψ.1 := rfl

@[simp] theorem id_val (a : Idx D s M) : (𝟙 a : a ⟶ a).1 = 𝟙 a.j := rfl

theorem isUnit_map {a b : Idx D s M} (φ : a ⟶ b) :
    IsUnit (algebraMap (D.obj b.j) (Localization.Away b.e) ((D.map φ.1).hom a.e)) := by
  obtain ⟨c, hc⟩ := φ.2
  refine isUnit_of_mul_isUnit_left (y := algebraMap _ (Localization.Away b.e) c) ?_
  rw [← map_mul, hc]
  exact IsLocalization.Away.algebraMap_isUnit b.e

def locMap {a b : Idx D s M} (φ : a ⟶ b) : Localization.Away a.e →+* Localization.Away b.e :=
  IsLocalization.Away.lift a.e (g := (algebraMap _ (Localization.Away b.e)).comp (D.map φ.1).hom)
    (isUnit_map φ)

@[simp] theorem locMap_algebraMap {a b : Idx D s M} (φ : a ⟶ b) (x : D.obj a.j) :
    locMap φ (algebraMap _ _ x) = algebraMap _ (Localization.Away b.e) ((D.map φ.1).hom x) := by
  simp [locMap, IsLocalization.Away.lift]

variable (D s M)

def diag : Idx D s M ⥤ CommRingCat.{0} where
  obj a := CommRingCat.of (Localization.Away a.e)
  map φ := CommRingCat.ofHom (locMap φ)
  map_id a := by
    ext : 1
    refine IsLocalization.ringHom_ext (Submonoid.powers a.e) (RingHom.ext fun x => ?_)
    simp
  map_comp {a b c} φ ψ := by
    ext : 1
    refine IsLocalization.ringHom_ext (Submonoid.powers a.e) (RingHom.ext fun x => ?_)
    simp

end GlobalTheory.IndEtaleLoc

namespace GlobalTheory.IndEtaleLoc

variable {J : Type} [SmallCategory J] {D : J ⥤ CommRingCat.{0}} {S : Type} [CommRing S]
  {s : D ⟶ (Functor.const J).obj (CommRingCat.of S)} {M : Submonoid S}

instance [IsFiltered J] : IsFiltered (Idx D s M) := by
  haveI : Nonempty (Idx D s M) := by
    obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
    exact ⟨⟨j, 1, by simpa using M.one_mem⟩⟩
  refine { cocone_objs := fun a b => ?_, cocone_maps := fun a b φ ψ => ?_ }
  · let u := IsFiltered.leftToMax a.j b.j
    let v := IsFiltered.rightToMax a.j b.j
    refine ⟨⟨IsFiltered.max a.j b.j, (D.map u).hom a.e * (D.map v).hom b.e, ?_⟩,
      ⟨u, (D.map v).hom b.e, rfl⟩, ⟨v, (D.map u).hom a.e, mul_comm _ _⟩, trivial⟩
    rw [map_mul, app_map_apply, app_map_apply]
    exact M.mul_mem a.mem b.mem
  · let h := IsFiltered.coeqHom φ.1 ψ.1
    refine ⟨⟨IsFiltered.coeq φ.1 ψ.1, (D.map h).hom b.e, by rw [app_map_apply]; exact b.mem⟩,
      ⟨h, 1, mul_one _⟩, Subtype.ext ?_⟩
    simpa using IsFiltered.coeq_condition φ.1 ψ.1

end GlobalTheory.IndEtaleLoc

namespace GlobalTheory.IndEtaleLoc

variable {J : Type} [SmallCategory J] {D : J ⥤ CommRingCat.{0}} {S : Type} [CommRing S]
  {s : D ⟶ (Functor.const J).obj (CommRingCat.of S)} {M : Submonoid S}

def fromBase {R : Type} [CommRing R] (t : (Functor.const J).obj (CommRingCat.of R) ⟶ D) :
    (Functor.const (Idx D s M)).obj (CommRingCat.of R) ⟶ diag D s M where
  app a := CommRingCat.ofHom ((algebraMap (D.obj a.j) (Localization.Away a.e)).comp (t.app a.j).hom)
  naturality a b φ := by
    ext x
    have h := congr(($(t.naturality φ.1)).hom x)
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
      CommRingCat.hom_comp, RingHom.comp_apply] at h
    change algebraMap _ (Localization.Away b.e) ((t.app b.j).hom x) =
      locMap φ (algebraMap _ (Localization.Away a.e) ((t.app a.j).hom x))
    rw [locMap_algebraMap, h]

variable (S' : Type) [CommRing S'] [Algebra S S'] [IsLocalization M S']

def leg (a : Idx D s M) : Localization.Away a.e →+* S' :=
  IsLocalization.Away.lift a.e (g := (algebraMap S S').comp ((s.app a.j).hom : D.obj a.j →+* S))
    (IsLocalization.map_units S' (⟨(s.app a.j).hom a.e, a.mem⟩ : M))

@[simp] theorem leg_algebraMap (a : Idx D s M) (x : D.obj a.j) :
    leg S' a (algebraMap (D.obj a.j) (Localization.Away a.e) x) =
      algebraMap S S' (((s.app a.j).hom : D.obj a.j →+* S) x) := by
  simp [leg, IsLocalization.Away.lift]

def toLoc : diag D s M ⟶ (Functor.const (Idx D s M)).obj (CommRingCat.of S') where
  app a := CommRingCat.ofHom (leg S' a)
  naturality a b φ := by
    ext : 1
    change (leg S' b).comp (locMap φ) = (RingHom.id S').comp (leg S' a)
    rw [RingHom.id_comp]
    refine IsLocalization.ringHom_ext (Submonoid.powers a.e) (RingHom.ext fun x => ?_)
    change leg S' b (locMap φ (algebraMap _ (Localization.Away a.e) x)) =
      leg S' a (algebraMap _ (Localization.Away a.e) x)
    rw [locMap_algebraMap, leg_algebraMap, leg_algebraMap]
    exact congrArg _ (app_map_apply φ.1 x)

def isColimitToLoc [IsFiltered J] (hs : IsColimit (Cocone.mk _ s)) :
    IsColimit (Cocone.mk _ (toLoc (s := s) (M := M) S')) := by
  have hc := isColimitOfPreserves (forget CommRingCat.{0}) hs
  haveI : ReflectsColimit (diag D s M) (forget CommRingCat.{0}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat.{0}) ?_
  have hsurj : ∀ x : S', ∃ (a : Idx D s M) (z : Localization.Away a.e), x = leg S' a z := by
    intro x
    obtain ⟨⟨y, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    obtain ⟨j, y', hy'⟩ := Types.jointly_surjective_of_isColimit hc y
    obtain ⟨k, m', hm'⟩ := Types.jointly_surjective_of_isColimit hc (m : S)
    change (s.app j).hom y' = y at hy'
    change (s.app k).hom m' = (m : S) at hm'
    let u := IsFiltered.leftToMax j k
    let v := IsFiltered.rightToMax j k
    let a : Idx D s M :=
      ⟨IsFiltered.max j k, (D.map v).hom m', by rw [app_map_apply, hm']; exact m.2⟩
    let p : Submonoid.powers a.e := ⟨a.e, Submonoid.mem_powers _⟩
    refine ⟨a, IsLocalization.mk' (Localization.Away a.e) ((D.map u).hom y') p, ?_⟩
    change _ = leg S' a _
    rw [IsLocalization.mk'_eq_iff_eq_mul]
    have h1 := congrArg (leg S' a) (IsLocalization.mk'_spec (Localization.Away a.e)
      ((D.map u).hom y') p)
    rw [map_mul, leg_algebraMap, leg_algebraMap] at h1
    have e1 : (s.app a.j).hom (p : D.obj a.j) = (m : S) := by
      change (s.app _).hom ((D.map v).hom m') = (m : S)
      rw [app_map_apply, hm']
    have e2 : (s.app a.j).hom ((D.map u).hom y') = (y : S) := by
      change (s.app _).hom ((D.map u).hom y') = (y : S)
      rw [app_map_apply, hy']
    rw [e1, e2] at h1
    exact h1.symm
  have hinj : ∀ (a : Idx D s M) (x y : Localization.Away a.e), leg S' a x = leg S' a y →
      ∃ (b : Idx D s M) (f : a ⟶ b), locMap f x = locMap f y := by
    intro a x y hxy
    suffices H : ∀ z, leg S' a z = 0 → ∃ (b : Idx D s M) (f : a ⟶ b), locMap f z = 0 by
      obtain ⟨b, f, hf⟩ := H (x - y) (by rw [map_sub, hxy, sub_self])
      refine ⟨b, f, ?_⟩
      rwa [map_sub, sub_eq_zero] at hf
    intro z hz
    obtain ⟨⟨c, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers a.e) z
    have hspec := IsLocalization.mk'_spec (Localization.Away a.e) c
      (⟨a.e ^ n, n, rfl⟩ : Submonoid.powers a.e)
    have hc0 : algebraMap S S' ((s.app a.j).hom c) = 0 := by
      have := congrArg (leg S' a) hspec
      rw [map_mul, hz, zero_mul, leg_algebraMap] at this
      exact this.symm
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff M S' _).1 hc0
    obtain ⟨k, m', hm'⟩ := Types.jointly_surjective_of_isColimit hc (m : S)
    change (s.app k).hom m' = (m : S) at hm'
    let u := IsFiltered.leftToMax a.j k
    let v := IsFiltered.rightToMax a.j k
    have h0 : (s.app (IsFiltered.max a.j k)).hom ((D.map v).hom m' * (D.map u).hom c) =
        (s.app (IsFiltered.max a.j k)).hom 0 := by
      rw [map_mul, app_map_apply, app_map_apply, hm', map_zero, hm]
    obtain ⟨l, f1, hf1⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc _ _).1 h0
    have hf1' : (D.map f1).hom ((D.map v).hom m' * (D.map u).hom c) = (D.map f1).hom 0 := hf1
    rw [map_zero, map_mul] at hf1'
    let b : Idx D s M := ⟨l, (D.map (u ≫ f1)).hom a.e * (D.map (v ≫ f1)).hom m', by
      rw [map_mul, app_map_apply, app_map_apply, hm']; exact M.mul_mem a.mem m.2⟩
    let f : a ⟶ b := ⟨u ≫ f1, (D.map (v ≫ f1)).hom m', rfl⟩
    refine ⟨b, f, ?_⟩
    have hu : IsUnit (locMap f (algebraMap _ _ (a.e ^ n))) := by
      rw [locMap_algebraMap, map_pow, map_pow]
      exact (isUnit_map f).pow n
    have hzero : algebraMap (D.obj b.j) (Localization.Away b.e) ((D.map f.1).hom c) = 0 := by
      have hb : IsUnit (algebraMap (D.obj b.j) (Localization.Away b.e) b.e) :=
        IsLocalization.Away.algebraMap_isUnit b.e
      refine (hb.mul_right_eq_zero).1 ?_
      rw [← map_mul]
      have : b.e * (D.map f.1).hom c = (D.map (u ≫ f1)).hom a.e *
          ((D.map f1).hom ((D.map v).hom m') * (D.map f1).hom ((D.map u).hom c)) := by
        simp only [b, f, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]
        ring
      rw [this, hf1', mul_zero, map_zero]
    have := congrArg (locMap f) hspec
    rw [map_mul, locMap_algebraMap f c, hzero] at this
    exact (hu.mul_left_eq_zero).1 this
  exact Types.FilteredColimit.isColimitOf' _ _ (fun x => hsurj x) (fun a x y h => hinj a x y h)

end GlobalTheory.IndEtaleLoc

namespace GlobalTheory.IndEtaleLoc

theorem isIndEtale_of_isLocalization : ∀ (R S S' : Type) [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] (M : Submonoid S)
    [IsLocalization M S'], GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap R S) →
      GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap R S') := by
  intro R S S' _ _ _ _ _ _ _ M _ h
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := h
  refine ⟨Idx D s M, inferInstance, inferInstance, diag D s M, fromBase t, toLoc S',
    isColimitToLoc S' hs, fun a => ⟨?_, ?_⟩⟩
  · show RingHom.Etale ((algebraMap (D.obj a.j) (Localization.Away a.e)).comp (t.app a.j).hom)
    exact RingHom.Etale.stableUnderComposition _ _ (hst a.j).1
      (RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway a.e))
  · ext x
    have h := congr(($((hst a.j).2)).hom x)
    change (s.app a.j).hom ((t.app a.j).hom x) = algebraMap R S x at h
    change leg S' a (algebraMap _ (Localization.Away a.e) ((t.app a.j).hom x)) = algebraMap R S' x
    rw [leg_algebraMap]
    change algebraMap S S' ((s.app a.j).hom ((t.app a.j).hom x)) = _
    rw [h, ← IsScalarTower.algebraMap_apply]

end GlobalTheory.IndEtaleLoc
