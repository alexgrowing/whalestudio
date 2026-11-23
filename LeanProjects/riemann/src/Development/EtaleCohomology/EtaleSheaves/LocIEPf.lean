import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi
import Mathlib.Algebra.Category.Ring.FilteredColimits

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.LocIEPf

variable {A : Type} [CommRing A]

def DivS (S : Submonoid A) : Type := S

def val {S : Submonoid A} (s : DivS S) : A := (show S from s).1

lemma val_mem {S : Submonoid A} (s : DivS S) : val s ∈ S := (show S from s).2

instance (S : Submonoid A) : Preorder (DivS S) where
  le s t := val s ∣ val t
  le_refl s := dvd_refl _
  le_trans _ _ _ h1 h2 := dvd_trans h1 h2

def mkD {S : Submonoid A} (a : A) (h : a ∈ S) : DivS S := (⟨a, h⟩ : S)

instance (S : Submonoid A) : IsDirected (DivS S) (· ≤ ·) :=
  ⟨fun s t => ⟨mkD (val s * val t) (S.mul_mem (val_mem s) (val_mem t)),
    Dvd.intro _ rfl, Dvd.intro_left _ rfl⟩⟩

instance (S : Submonoid A) : Nonempty (DivS S) := ⟨mkD 1 S.one_mem⟩

lemma unit_of_dvd {a b : A} (h : a ∣ b) : IsUnit (algebraMap A (Localization.Away b) a) := by
  obtain ⟨c, rfl⟩ := h
  refine isUnit_of_mul_isUnit_left (y := algebraMap A (Localization.Away (a * c)) c) ?_
  rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit _

def mp {a b : A} (h : a ∣ b) : Localization.Away a →+* Localization.Away b :=
  IsLocalization.Away.lift a (unit_of_dvd h)

lemma mp_comp {a b : A} (h : a ∣ b) : (mp h).comp (algebraMap A _) = algebraMap A _ :=
  IsLocalization.lift_comp _

lemma mp_alg {a b : A} (h : a ∣ b) (x : A) : mp h (algebraMap A _ x) = algebraMap A _ x :=
  RingHom.congr_fun (mp_comp h) x

lemma ext_away {a : A} {P : Type} [CommRing P] {j k : Localization.Away a →+* P}
    (h : j.comp (algebraMap A _) = k.comp (algebraMap A _)) : j = k :=
  IsLocalization.ringHom_ext (Submonoid.powers a) h

variable (S : Submonoid A)

def F : DivS S ⥤ CommRingCat.{0} where
  obj s := CommRingCat.of (Localization.Away (val s))
  map f := CommRingCat.ofHom (mp (leOfHom f))
  map_id s := by
    ext1; apply ext_away; ext x; exact mp_alg (leOfHom (𝟙 s)) x
  map_comp f g := by
    ext1; apply ext_away; ext x
    exact (by rw [mp_alg, mp_alg, mp_alg] : mp (leOfHom (f ≫ g)) (algebraMap A _ x) =
      mp (leOfHom g) (mp (leOfHom f) (algebraMap A _ x)))

def tN : (Functor.const (DivS S)).obj (CommRingCat.of A) ⟶ F S where
  app s := CommRingCat.ofHom (algebraMap A (Localization.Away (val s)))
  naturality s t f := by
    ext1; apply RingHom.ext; intro x
    exact (mp_alg (leOfHom f) x).symm

variable (B : Type) [CommRing B] [Algebra A B] [IsLocalization S B]

def lB (s : DivS S) : Localization.Away (val s) →+* B :=
  IsLocalization.Away.lift (val s) (IsLocalization.map_units B ⟨val s, val_mem s⟩)

lemma lB_alg (s : DivS S) (x : A) : lB S B s (algebraMap A _ x) = algebraMap A B x :=
  RingHom.congr_fun (IsLocalization.lift_comp _) x

def sN : F S ⟶ (Functor.const (DivS S)).obj (CommRingCat.of B) where
  app s := CommRingCat.ofHom (lB S B s)
  naturality s t f := by
    ext1; apply ext_away; ext x
    exact (by rw [mp_alg, lB_alg, lB_alg] :
      lB S B t (mp (leOfHom f) (algebraMap A _ x)) = lB S B s (algebraMap A _ x))

lemma isColim : Nonempty (IsColimit (Cocone.mk _ (sN S B))) := by
  have : ReflectsColimitsOfShape (DivS S) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat.{0}) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)⟩
  · intro (x : B)
    obtain ⟨⟨a, m⟩, hx⟩ := IsLocalization.surj S x
    let s : DivS S := mkD (m : A) m.2
    refine ⟨s, IsLocalization.mk' (Localization.Away (val s)) a
      (⟨val s, Submonoid.mem_powers _⟩ : Submonoid.powers (val s)), ?_⟩
    change x = lB S B s _
    have hu := IsLocalization.map_units B m
    refine hu.mul_right_cancel ?_
    rw [hx]
    have h2 : algebraMap A B (m : A) = lB S B s (algebraMap A _ (val s)) := by rw [lB_alg]; rfl
    rw [h2, ← map_mul, IsLocalization.mk'_spec, lB_alg]
  · intro i (y : Localization.Away (val i)) (y' : Localization.Away (val i)) h
    change lB S B i y = lB S B i y' at h
    obtain ⟨⟨c, m⟩, hd⟩ := IsLocalization.surj (Submonoid.powers (val i)) (y - y')
    have hc : algebraMap A B c = algebraMap A B 0 := by
      have := congrArg (lB S B i) hd
      rw [map_mul, map_sub, h, sub_self, zero_mul, lB_alg] at this
      rw [map_zero]; exact this.symm
    obtain ⟨u, hu⟩ := IsLocalization.exists_of_eq (M := S) hc
    let k : DivS S := mkD (val i * (u : A)) (S.mul_mem (val_mem i) u.2)
    have hik : val i ∣ val k := Dvd.intro _ rfl
    refine ⟨k, homOfLE hik, ?_⟩
    change mp hik y = mp hik y'
    rw [← sub_eq_zero, ← map_sub]
    have hm : IsUnit (algebraMap A (Localization.Away (val k)) (m : A)) := by
      obtain ⟨n, hn⟩ := m.2
      rw [← hn, map_pow]; exact (unit_of_dvd hik).pow n
    have hck : algebraMap A (Localization.Away (val k)) c = 0 := by
      have hu' : IsUnit (algebraMap A (Localization.Away (val k)) (u : A)) :=
        unit_of_dvd (Dvd.intro_left _ rfl)
      have := congrArg (algebraMap A (Localization.Away (val k))) hu
      rw [mul_zero, map_mul, map_zero] at this
      exact (hu'.mul_right_eq_zero).1 this
    refine (hm.mul_left_eq_zero).1 ?_
    rw [← mp_alg hik, ← map_mul, hd, mp_alg, hck]

theorem LocIE_of : LateralTheory.E.t_E3Cut.LocIE := by
  intro A B _ _ _ S _
  obtain ⟨hc⟩ := isColim S B
  refine ⟨DivS S, inferInstance, inferInstance, F S, tN S, sN S B, hc, fun j => ⟨?_, ?_⟩⟩
  · change (algebraMap A (Localization.Away (val j))).Etale
    rw [RingHom.etale_algebraMap]
    exact Algebra.Etale.of_isLocalizationAway (val j)
  · ext1; ext x
    exact lB_alg S B j x

end LateralTheory.E.LocIEPf
