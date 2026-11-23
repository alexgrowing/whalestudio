import Development.EtaleCohomology.EtaleSheaves.SHExistsPf

noncomputable section
open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.LocAtPf

structure DivIdx {A : Type} [CommRing A] (S : Submonoid A) : Type where
  val : S

variable {A : Type} [CommRing A] (S : Submonoid A)

instance : Preorder (DivIdx S) where
  le a b := ∃ c : A, (b.val : A) = (a.val : A) * c
  le_refl a := ⟨1, (mul_one _).symm⟩
  le_trans a b c := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x * y, by rw [hy, hx, mul_assoc]⟩

instance : IsDirected (DivIdx S) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.val * b.val⟩, ⟨(b.val : A), by simp⟩, ⟨(a.val : A), by simp [mul_comm]⟩⟩⟩

instance : Nonempty (DivIdx S) := ⟨⟨1⟩⟩

lemma one_le (a : DivIdx S) : (⟨1⟩ : DivIdx S) ≤ a := ⟨(a.val : A), by simp⟩

lemma unit_of_le {a b : DivIdx S} (h : a ≤ b) :
    IsUnit (algebraMap A (Localization.Away (b.val : A)) (a.val : A)) := by
  obtain ⟨c, hc⟩ := h
  have hb := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (b.val : A)) (b.val : A)
  have e : algebraMap A (Localization.Away (b.val : A)) (b.val : A) =
      algebraMap A (Localization.Away (b.val : A)) (a.val : A) * algebraMap A (Localization.Away (b.val : A)) c := by
    rw [← map_mul, ← hc]
  rw [e] at hb
  exact isUnit_of_mul_isUnit_left hb

def tr {a b : DivIdx S} (h : a ≤ b) :
    Localization.Away (a.val : A) →+* Localization.Away (b.val : A) :=
  IsLocalization.Away.lift (a.val : A) (unit_of_le S h)

lemma tr_alg {a b : DivIdx S} (h : a ≤ b) (x : A) :
    tr S h (algebraMap A _ x) = algebraMap A _ x :=
  IsLocalization.Away.lift_eq _ _ x

def Dg : DivIdx S ⥤ CommRingCat.{0} where
  obj a := CommRingCat.of (Localization.Away (a.val : A))
  map {a b} f := CommRingCat.ofHom (tr S f.le)
  map_id a := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers (a.val : A))
    ext x; simp [tr_alg]
  map_comp {a b c} f g := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers (a.val : A))
    ext x; simp [tr_alg]

def tN : (Functor.const (DivIdx S)).obj (CommRingCat.of A) ⟶ Dg S where
  app a := CommRingCat.ofHom (algebraMap A (Localization.Away (a.val : A)))
  naturality a b f := by
    apply CommRingCat.hom_ext; ext x
    exact (tr_alg S f.le x).symm

lemma away_ext (a : DivIdx S) {R : CommRingCat.{0}} {f g : (Dg S).obj a ⟶ R}
    (h : ∀ x : A, f ((tN S).app a x) = g ((tN S).app a x)) : f = g := by
  apply CommRingCat.hom_ext
  exact IsLocalization.ringHom_ext (M := Submonoid.powers (a.val : A))
    (S := Localization.Away (a.val : A)) (RingHom.ext h)

lemma Dg_map_tN {a b : DivIdx S} (f : a ⟶ b) (x : A) :
    (Dg S).map f ((tN S).app a x) = (tN S).app b x := tr_alg S f.le x

variable (B : Type) [CommRing B] [Algebra A B] [IsLocalization S B]

def sApp (a : DivIdx S) : CommRingCat.of (Localization.Away (a.val : A)) ⟶ CommRingCat.of B :=
  CommRingCat.ofHom (IsLocalization.Away.lift (a.val : A) (IsLocalization.map_units B a.val))

lemma sApp_tN (a : DivIdx S) (x : A) : sApp S B a ((tN S).app a x) = algebraMap A B x :=
  IsLocalization.Away.lift_eq _ (IsLocalization.map_units B a.val) x

def sN : Dg S ⟶ (Functor.const (DivIdx S)).obj (CommRingCat.of B) where
  app a := sApp S B a
  naturality a b f := by
    apply CommRingCat.hom_ext
    refine IsLocalization.ringHom_ext (M := Submonoid.powers (a.val : A))
      (S := Localization.Away (a.val : A)) (RingHom.ext fun x => ?_)
    change IsLocalization.Away.lift (b.val : A) (IsLocalization.map_units B b.val) (tr S f.le (algebraMap A _ x)) =
      IsLocalization.Away.lift (a.val : A) (IsLocalization.map_units B a.val) (algebraMap A _ x)
    rw [tr_alg, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]

lemma cocone_alg (c : Cocone (Dg S)) (a : DivIdx S) :
    (tN S).app a ≫ c.ι.app a = (tN S).app ⟨1⟩ ≫ c.ι.app ⟨1⟩ := by
  rw [← c.w (homOfLE (one_le S a)), ← Category.assoc, ← (tN S).naturality]
  simp

def g0 (c : Cocone (Dg S)) : A →+* c.pt := ((tN S).app ⟨1⟩ ≫ c.ι.app ⟨1⟩).hom

lemma awayDivisibilityCocone_baseHom_submonoid_isUnit (c : Cocone (Dg S)) (s : S) : IsUnit (g0 S c (s : A)) := by
  have e : g0 S c (s : A) = c.ι.app ⟨s⟩ ((tN S).app ⟨s⟩ (s : A)) := by
    rw [← CategoryTheory.comp_apply, cocone_alg]; rfl
  rw [e]
  exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (s : A)) (s : A)).map
    (c.ι.app ⟨s⟩).hom

def isColim : IsColimit (Cocone.mk (CommRingCat.of B) (sN S B)) where
  desc c := CommRingCat.ofHom (IsLocalization.lift (M := S) (S := B) (g := g0 S c) (awayDivisibilityCocone_baseHom_submonoid_isUnit S c))
  fac c a := by
    apply away_ext S a
    intro x
    rw [CategoryTheory.comp_apply]
    change CommRingCat.Hom.hom _ (sApp S B a ((tN S).app a x)) = _
    rw [sApp_tN]
    change IsLocalization.lift _ (algebraMap A B x) = _
    rw [IsLocalization.lift_eq, ← CategoryTheory.comp_apply, cocone_alg]
    rfl
  uniq c m hm := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext S
    ext x
    change m.hom (algebraMap A B x) = IsLocalization.lift _ (algebraMap A B x)
    rw [IsLocalization.lift_eq, ← sApp_tN S B ⟨1⟩ x]
    have := congrArg (fun f => f ((tN S).app ⟨1⟩ x)) (hm ⟨1⟩)
    simp only [CategoryTheory.comp_apply] at this
    exact this

theorem locIE (S : Submonoid A) (B : Type) [CommRing B] [Algebra A B] [IsLocalization S B] :
    IE (CommRingCat.ofHom (algebraMap A B)) := by
  refine ⟨DivIdx S, inferInstance, inferInstance, Dg S, tN S, sN S B, isColim S B, fun a => ⟨?_, ?_⟩⟩
  · show RingHom.Etale (CommRingCat.Hom.hom (CommRingCat.ofHom (algebraMap A (Localization.Away (a.val : A)))))
    rw [CommRingCat.hom_ofHom, RingHom.etale_algebraMap]
    infer_instance
  · apply CommRingCat.hom_ext; ext x
    exact sApp_tN S B a x

theorem LocAt_of : LateralTheory.E.SHExistsPf.LocAt := by
  intro A r _
  exact locIE r.primeCompl (Localization.AtPrime r)

end LateralTheory.E.LocAtPf
