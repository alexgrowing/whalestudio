import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.AwayCont

variable {A : Type} [CommRing A] (M : Submonoid A)

structure Idx (M : Submonoid A) where

  val : A
  mem : val ∈ M

instance : Preorder (Idx M) where
  le a b := ∃ t ∈ M, b.val = a.val * t
  le_refl a := ⟨1, M.one_mem, by simp⟩
  le_trans a b c := by
    rintro ⟨t, ht, h1⟩ ⟨s, hs, h2⟩
    exact ⟨t * s, M.mul_mem ht hs, by rw [h2, h1, mul_assoc]⟩

instance : IsDirected (Idx M) (· ≤ ·) where
  directed a b := ⟨⟨a.val * b.val, M.mul_mem a.mem b.mem⟩, ⟨b.val, b.mem, rfl⟩, ⟨a.val, a.mem, mul_comm _ _⟩⟩

instance : Nonempty (Idx M) := ⟨⟨1, M.one_mem⟩⟩

theorem isUnit_of_le {a b : Idx M} (h : a ≤ b) :
    IsUnit (algebraMap A (Localization.Away b.val) a.val) := by
  obtain ⟨t, -, ht⟩ := h
  have hb := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away b.val) b.val
  rw [show algebraMap A (Localization.Away b.val) b.val =
      algebraMap A _ a.val * algebraMap A _ t by rw [← map_mul, ← ht]] at hb
  exact isUnit_of_mul_isUnit_left hb

def trans {a b : Idx M} (h : a ≤ b) : Localization.Away a.val →+* Localization.Away b.val :=
  IsLocalization.Away.lift a.val (isUnit_of_le M h)

theorem trans_comp {a b : Idx M} (h : a ≤ b) :
    (trans M h).comp (algebraMap A _) = algebraMap A _ :=
  IsLocalization.Away.lift_comp _ _

theorem ext_away {a : A} {P : Type} [CommRing P] {f g : Localization.Away a →+* P}
    (hf : f.comp (algebraMap A _) = g.comp (algebraMap A _)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers a) hf

def diag : Idx M ⥤ CommRingCat.{0} where
  obj a := CommRingCat.of (Localization.Away a.val)
  map {a b} h := CommRingCat.ofHom (trans M h.le)
  map_id a := by
    ext1; apply ext_away
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id]
    rw [trans_comp]; rfl
  map_comp {a b c} f g := by
    ext1; apply ext_away
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp]
    rw [RingHom.comp_assoc, trans_comp, trans_comp, trans_comp]

def toLoc (a : Idx M) : Localization.Away a.val →+* Localization M :=
  IsLocalization.Away.lift a.val (IsLocalization.map_units (Localization M) (⟨a.val, a.mem⟩ : M))

theorem toLoc_comp (a : Idx M) : (toLoc M a).comp (algebraMap A _) = algebraMap A _ :=
  IsLocalization.Away.lift_comp _ _

def cocone : Cocone (diag M) where
  pt := CommRingCat.of (Localization M)
  ι := { app := fun a => CommRingCat.ofHom (toLoc M a)
         naturality := fun a b h => by
           ext1; apply ext_away
           simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp, diag, Functor.const_obj_map,
             CommRingCat.hom_id, RingHom.id_comp]
           rw [RingHom.comp_assoc, trans_comp, toLoc_comp]
           exact (toLoc_comp M a).symm }

end GlobalTheory.EtC.AwayCont
end

noncomputable section

namespace GlobalTheory.EtC.AwayCont

variable {A : Type} [CommRing A] (M : Submonoid A)

theorem toLoc_trans {a b : Idx M} (h : a ≤ b) : (toLoc M b).comp (trans M h) = toLoc M a :=
  ext_away (by rw [RingHom.comp_assoc, trans_comp, toLoc_comp, toLoc_comp])

theorem trans_trans {a b c : Idx M} (h : a ≤ b) (h' : b ≤ c) :
    (trans M h').comp (trans M h) = trans M (h.trans h') :=
  ext_away (by rw [RingHom.comp_assoc, trans_comp, trans_comp, trans_comp])

theorem kill (a : Idx M) (z : Localization.Away a.val) (hz : toLoc M a z = 0) :
    ∃ (b : Idx M) (h : a ≤ b), trans M h z = 0 := by
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers a.val) z
  have h1 : algebraMap A (Localization M) x = 0 := by
    have := congrArg (toLoc M a) hs
    rw [map_mul, hz, zero_mul, ← RingHom.comp_apply, toLoc_comp] at this
    exact this.symm
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff M (Localization M) x).mp h1
  let b : Idx M := ⟨a.val * c, M.mul_mem a.mem c.2⟩
  have hab : a ≤ b := ⟨c, c.2, rfl⟩
  refine ⟨b, hab, ?_⟩
  have hu := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away b.val) b.val
  have hb : b.val = a.val * c := rfl
  rw [hb, map_mul] at hu
  have hua : IsUnit (algebraMap A (Localization.Away b.val) a.val) := isUnit_of_mul_isUnit_left hu
  have huc : IsUnit (algebraMap A (Localization.Away b.val) c) := isUnit_of_mul_isUnit_right hu
  have hx : algebraMap A (Localization.Away b.val) x = 0 := by
    have : algebraMap A (Localization.Away b.val) c * algebraMap A (Localization.Away b.val) x = 0 := by
      rw [← map_mul, hc, map_zero]
    exact (huc.mul_right_eq_zero).mp this
  have hs' := congrArg (trans M hab) hs
  rw [map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, trans_comp, hx] at hs'
  obtain ⟨k, hk⟩ := s.2
  have hus : IsUnit (algebraMap A (Localization.Away b.val) (s : A)) := by
    rw [← hk, map_pow]; exact hua.pow k
  exact (hus.mul_left_eq_zero).mp hs'

def isColimit : IsColimit (cocone M) := by
  haveI : ReflectsColimitsOfShape (Idx M) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (cocone M)) ?_ ?_)
  · intro (x : Localization M)
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    refine ⟨⟨s.1, s.2⟩, IsLocalization.mk' (Localization.Away s.1) a
      (⟨s.1, Submonoid.mem_powers _⟩ : Submonoid.powers s.1), ?_⟩
    show _ = toLoc M ⟨s.1, s.2⟩ _
    rw [eq_comm, IsLocalization.eq_mk'_iff_mul_eq]
    have e1 := RingHom.congr_fun (toLoc_comp M ⟨s.1, s.2⟩) s.1
    have e2 := RingHom.congr_fun (toLoc_comp M ⟨s.1, s.2⟩) a
    simp only [RingHom.comp_apply] at e1 e2
    rw [← e1, ← map_mul, IsLocalization.mk'_spec, e2]
  · intro i j (xi : Localization.Away i.val) (xj : Localization.Away j.val) h
    change toLoc M i xi = toLoc M j xj at h
    let k : Idx M := ⟨i.val * j.val, M.mul_mem i.mem j.mem⟩
    have hik : i ≤ k := ⟨j.val, j.mem, rfl⟩
    have hjk : j ≤ k := ⟨i.val, i.mem, mul_comm _ _⟩
    have hz : toLoc M k (trans M hik xi - trans M hjk xj) = 0 := by
      have e1 := RingHom.congr_fun (toLoc_trans M hik) xi
      have e2 := RingHom.congr_fun (toLoc_trans M hjk) xj
      simp only [RingHom.comp_apply] at e1 e2
      rw [map_sub, e1, e2, h, sub_self]
    obtain ⟨b, hkb, hb⟩ := kill M k _ hz
    refine ⟨b, homOfLE (hik.trans hkb), homOfLE (hjk.trans hkb), ?_⟩
    show trans M (hik.trans hkb) xi = trans M (hjk.trans hkb) xj
    rw [← trans_trans M hik hkb, ← trans_trans M hjk hkb, RingHom.comp_apply, RingHom.comp_apply,
      ← sub_eq_zero, ← map_sub]
    exact hb

end GlobalTheory.EtC.AwayCont
end

namespace GlobalTheory.EtC.AwayCont

theorem kill_of_loc : B1 → ∀ (q : ℕ) (A : Type) [CommRing A] (M : Submonoid A) (n i : ℤ), IsUnit (q : A) →
    ∀ m ∈ M, ∀ y : Ht q (sp (Localization.Away m)) n i, ∀ φ : Localization.Away m →+* Localization M,
    φ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap φ) _ _ y = 0 →
    ∃ m' ∈ M, ∀ ψ : Localization.Away m →+* Localization.Away (m * m'),
      ψ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ψ) _ _ y = 0 := by
  intro hB q A _ M n i hq m hm y φ hφ hy
  let a : Idx M := ⟨m, hm⟩
  have hq' : IsUnit ((q : ℕ) : (diag M).obj a) := by
    have h0 : IsUnit ((q : ℕ) : Localization.Away m) := by
      simpa using hq.map (algebraMap A (Localization.Away m))
    exact h0
  have hφ' : ((cocone M).ι.app a).hom = φ := by
    show toLoc M a = φ
    exact ext_away (by rw [hφ]; exact toLoc_comp M a)
  have hy' : pull _ (spMap ((cocone M).ι.app a).hom) _ _ y = 0 := by
    rw [hφ']; exact hy
  obtain ⟨⟨k1, hk1⟩, f, hk⟩ := (hB q (diag M) (cocone M) (isColimit M) n i).2 a y hq' hy'
  obtain ⟨t, ht, hkt⟩ := f.le
  change k1 = m * t at hkt
  subst hkt
  refine ⟨t, ht, fun ψ hψ => ?_⟩
  have hψ' : ((diag M).map f).hom = ψ := by
    show trans M f.le = ψ
    exact ext_away (by rw [hψ]; exact trans_comp M f.le)
  rw [← hψ']
  exact hk

end GlobalTheory.EtC.AwayCont
