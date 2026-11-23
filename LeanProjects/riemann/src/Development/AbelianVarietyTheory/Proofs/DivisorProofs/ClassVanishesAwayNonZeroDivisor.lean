import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuityStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.TotFracAway

variable (R : Type) [CommRing R]

structure Idx where

  val : R
  mem : val ∈ nonZeroDivisors R

instance : Preorder (Idx R) where
  le a b := a.val ∣ b.val
  le_refl a := dvd_refl a.val
  le_trans _ _ _ := dvd_trans

instance : IsDirected (Idx R) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.val * b.val, Submonoid.mul_mem _ a.mem b.mem⟩, dvd_mul_right _ _, dvd_mul_left _ _⟩⟩

instance : Nonempty (Idx R) := ⟨⟨1, Submonoid.one_mem _⟩⟩

variable {R}

theorem isUnit_of_dvd {a b : R} (h : a ∣ b) : IsUnit (algebraMap R (Localization.Away b) a) :=
  isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit b)

def tr {a b : R} (h : a ∣ b) : Localization.Away a →+* Localization.Away b :=
  Localization.awayLift (algebraMap R _) a (isUnit_of_dvd h)

theorem tr_comp {a b : R} (h : a ∣ b) : (tr h).comp (algebraMap R _) = algebraMap R _ :=
  IsLocalization.Away.lift_comp a (isUnit_of_dvd h)

theorem away_ext {a : R} {S : Type} [CommRing S] {f g : Localization.Away a →+* S}
    (h : f.comp (algebraMap R _) = g.comp (algebraMap R _)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers a) h

variable (R) in

def diag : Idx R ⥤ CommRingCat.{0} where
  obj a := CommRingCat.of (Localization.Away a.val)
  map {a b} h := CommRingCat.ofHom (tr (leOfHom h : a.val ∣ b.val))
  map_id a := by
    ext1
    refine away_ext ?_
    simp [tr_comp]
  map_comp {a b c} f g := by
    ext1
    refine away_ext ?_
    simp [RingHom.comp_assoc, tr_comp]

def toFrac (a : Idx R) : Localization.Away a.val →+* FractionRing R :=
  Localization.awayLift (algebraMap R _) a.val
    (IsLocalization.map_units (FractionRing R) (⟨a.val, a.mem⟩ : nonZeroDivisors R))

theorem toFrac_comp (a : Idx R) : (toFrac a).comp (algebraMap R _) = algebraMap R (FractionRing R) :=
  IsLocalization.Away.lift_comp a.val
    (IsLocalization.map_units (FractionRing R) (⟨a.val, a.mem⟩ : nonZeroDivisors R))

variable (R) in

def cocone : Cocone (diag R) where
  pt := CommRingCat.of (FractionRing R)
  ι :=
    { app := fun a => CommRingCat.ofHom (toFrac a)
      naturality := fun a b h => by
        ext1
        refine away_ext ?_
        simp [diag, RingHom.comp_assoc, tr_comp, toFrac_comp] }

def idx1 : Idx R := ⟨1, Submonoid.one_mem _⟩

theorem desc_unit (s : Cocone (diag R)) (y : nonZeroDivisors R) :
    IsUnit (((s.ι.app idx1).hom.comp (algebraMap R (Localization.Away (1 : R)))) y) := by
  let b : Idx R := ⟨y.1, y.2⟩
  have hw := s.w (homOfLE (show (idx1 : Idx R) ≤ b from one_dvd _))
  rw [← hw]
  change IsUnit ((s.ι.app b).hom ((tr (one_dvd y.1)) (algebraMap R _ y.1)))
  rw [← RingHom.comp_apply (tr _), tr_comp]
  exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away y.1) y.1).map (s.ι.app b).hom

variable (R) in

def isColim : IsColimit (cocone R) where
  desc s := CommRingCat.ofHom (IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) (desc_unit s))
  fac s a := by
    have hw := s.w (homOfLE (show (idx1 : Idx R) ≤ a from one_dvd _))
    ext1
    change (IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) (desc_unit s)).comp (toFrac a) = (s.ι.app a).hom
    refine away_ext ?_
    rw [RingHom.comp_assoc, toFrac_comp, IsLocalization.lift_comp, ← hw]
    ext b
    exact congrArg (s.ι.app a).hom (DFunLike.congr_fun (tr_comp (one_dvd a.val)) b)
  uniq s m hm := by
    ext1
    change m.hom = IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) (desc_unit s)
    refine IsLocalization.ringHom_ext (S := FractionRing R) (nonZeroDivisors R) ?_
    rw [IsLocalization.lift_comp, ← hm idx1]
    ext b
    exact congrArg m.hom (DFunLike.congr_fun (toFrac_comp idx1) b).symm

theorem spMap_comp {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] (f : A →+* A') (g : A' →+* A'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

end GlobalTheory.EtC.TotFracAway

open GlobalTheory.EtC.TotFracAway in

theorem GlobalTheory.EtC.classVanishesAwayNZD : ∀ (q : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → ∀ (n i : ℤ)
    (z : Ht q (sp R) n i), pull _ (spMap (algebraMap R (FractionRing R))) _ _ z = 0 →
    ∃ g ∈ nonZeroDivisors R, pull _ (spMap (algebraMap R (Localization.Away g))) _ _ z = 0 := by
  intro q R _ hq n i x hx
  have hB1 := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (diag R) (cocone R) (isColim R) n i).2
  have hq1 : IsUnit (q : Localization.Away (idx1 : Idx R).val) := by
    have := hq.map (algebraMap R (Localization.Away (idx1 : Idx R).val))
    rwa [map_natCast] at this
  have h2 : pull _ (spMap (toFrac (idx1 : Idx R))) _ _
      (pull _ (spMap (algebraMap R (Localization.Away (idx1 : Idx R).val))) _ _ x) = 0 := by
    rw [← pull_comp, ← spMap_comp, toFrac_comp]
    exact hx
  obtain ⟨k, f, hk⟩ := hB1 idx1 (pull _ (spMap (algebraMap R (Localization.Away (idx1 : Idx R).val))) _ _ x) hq1 h2
  have hf : (idx1 : Idx R).val ∣ k.val := leOfHom f
  refine ⟨k.val, k.mem, ?_⟩
  have e : algebraMap R (Localization.Away k.val) =
      (tr hf).comp (algebraMap R (Localization.Away (idx1 : Idx R).val)) := by
    rw [tr_comp]
  rw [e, spMap_comp, pull_comp]
  exact hk

example : ∀ (q : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → ∀ (n i : ℤ) (z : Ht q (sp R) n i), pull _ (spMap (algebraMap R (FractionRing R))) _ _ z = 0 → ∃ g ∈ nonZeroDivisors R, pull _ (spMap (algebraMap R (Localization.Away g))) _ _ z = 0 :=
  GlobalTheory.EtC.classVanishesAwayNZD
