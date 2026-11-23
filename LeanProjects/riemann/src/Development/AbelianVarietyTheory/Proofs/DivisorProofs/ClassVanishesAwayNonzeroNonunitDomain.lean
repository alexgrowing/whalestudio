import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayHomCompAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuityStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

namespace GlobalTheory.EtC.FracAway

variable (B : Type) [CommRing B] [IsDomain B]

structure Idx where

  val : B
  ne : val ≠ 0

instance : Preorder (Idx B) where
  le a b := a.val ∣ b.val
  le_refl a := dvd_refl a.val
  le_trans _ _ _ := dvd_trans

instance : IsDirected (Idx B) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.val * b.val, mul_ne_zero a.ne b.ne⟩, dvd_mul_right _ _, dvd_mul_left _ _⟩⟩

instance : Nonempty (Idx B) := ⟨⟨1, one_ne_zero⟩⟩

variable {B}

theorem isUnit_of_dvd {a b : B} (h : a ∣ b) : IsUnit (algebraMap B (Localization.Away b) a) :=
  isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit b)

def tr {a b : B} (h : a ∣ b) : Localization.Away a →+* Localization.Away b :=
  Localization.awayLift (algebraMap B _) a (isUnit_of_dvd h)

theorem tr_comp {a b : B} (h : a ∣ b) : (tr h).comp (algebraMap B _) = algebraMap B _ :=
  IsLocalization.Away.lift_comp a (isUnit_of_dvd h)

theorem away_ext {a : B} {R : Type} [CommRing R] {f g : Localization.Away a →+* R}
    (h : f.comp (algebraMap B _) = g.comp (algebraMap B _)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers a) h

variable (B) in

def diag : Idx B ⥤ CommRingCat.{0} where
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

def toFrac (a : Idx B) : Localization.Away a.val →+* FractionRing B :=
  Localization.awayLift (algebraMap B _) a.val
    (IsLocalization.map_units (FractionRing B) (⟨a.val, mem_nonZeroDivisors_of_ne_zero a.ne⟩ : nonZeroDivisors B))

theorem toFrac_comp (a : Idx B) : (toFrac a).comp (algebraMap B _) = algebraMap B (FractionRing B) :=
  IsLocalization.Away.lift_comp a.val
    (IsLocalization.map_units (FractionRing B) (⟨a.val, mem_nonZeroDivisors_of_ne_zero a.ne⟩ : nonZeroDivisors B))

variable (B) in

def cocone : Cocone (diag B) where
  pt := CommRingCat.of (FractionRing B)
  ι :=
    { app := fun a => CommRingCat.ofHom (toFrac a)
      naturality := fun a b h => by
        ext1
        refine away_ext ?_
        simp [diag, RingHom.comp_assoc, tr_comp, toFrac_comp] }

def idx1 : Idx B := ⟨1, one_ne_zero⟩

theorem desc_unit (s : Cocone (diag B)) (y : nonZeroDivisors B) :
    IsUnit (((s.ι.app idx1).hom.comp (algebraMap B (Localization.Away (1 : B)))) y) := by
  let b : Idx B := ⟨y.1, nonZeroDivisors.ne_zero y.2⟩
  have hw := s.w (homOfLE (show (idx1 : Idx B) ≤ b from one_dvd _))
  rw [← hw]
  change IsUnit ((s.ι.app b).hom ((tr (one_dvd y.1)) (algebraMap B _ y.1)))
  rw [← RingHom.comp_apply (tr _), tr_comp]
  exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away y.1) y.1).map (s.ι.app b).hom

variable (B) in

def isColim : IsColimit (cocone B) where
  desc s := CommRingCat.ofHom (IsLocalization.lift (M := nonZeroDivisors B) (S := FractionRing B) (desc_unit s))
  fac s a := by
    have hw := s.w (homOfLE (show (idx1 : Idx B) ≤ a from one_dvd _))
    ext1
    change (IsLocalization.lift (M := nonZeroDivisors B) (S := FractionRing B) (desc_unit s)).comp (toFrac a) = (s.ι.app a).hom
    refine away_ext ?_
    rw [RingHom.comp_assoc, toFrac_comp, IsLocalization.lift_comp, ← hw]
    ext b
    exact congrArg (s.ι.app a).hom (DFunLike.congr_fun (tr_comp (one_dvd a.val)) b)
  uniq s m hm := by
    ext1
    change m.hom = IsLocalization.lift (M := nonZeroDivisors B) (S := FractionRing B) (desc_unit s)
    refine IsLocalization.ringHom_ext (S := FractionRing B) (nonZeroDivisors B) ?_
    rw [IsLocalization.lift_comp, ← hm idx1]
    ext b
    exact congrArg m.hom (DFunLike.congr_fun (toFrac_comp idx1) b).symm

theorem spMap_comp {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] (f : A →+* A') (g : A' →+* A'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

end GlobalTheory.EtC.FracAway

open GlobalTheory.EtC.FracAway in
theorem GlobalTheory.EtC.classVanishesAway : ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B], ¬ IsField B → IsUnit (q : B) →
    ∀ (n i : ℤ) (x : Ht q (sp B) n i), pull _ (spMap (algebraMap B (FractionRing B))) _ _ x = 0 →
    ∃ f : B, f ≠ 0 ∧ ¬ IsUnit f ∧ pull _ (spMap (algebraMap B (Localization.Away f))) _ _ x = 0 := by
  intro q B _ _ hF hq n i x hx
  have hB1 := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (diag B) (cocone B) (isColim B) n i).2
  have hq1 : IsUnit (q : Localization.Away (idx1 : Idx B).val) := by
    have := hq.map (algebraMap B (Localization.Away (idx1 : Idx B).val))
    rwa [map_natCast] at this
  have h2 : pull _ (spMap (toFrac (idx1 : Idx B))) _ _
      (pull _ (spMap (algebraMap B (Localization.Away (idx1 : Idx B).val))) _ _ x) = 0 := by
    rw [← pull_comp, ← spMap_comp, toFrac_comp]
    exact hx
  obtain ⟨k, f, hk⟩ := hB1 idx1 (pull _ (spMap (algebraMap B (Localization.Away (idx1 : Idx B).val))) _ _ x) hq1 h2
  obtain ⟨g, hg0, hgu⟩ := Ring.exists_not_isUnit_of_not_isField hF
  have hf : (idx1 : Idx B).val ∣ k.val := leOfHom f
  refine ⟨k.val * g, mul_ne_zero k.ne hg0, fun hu => hgu (isUnit_of_mul_isUnit_right hu), ?_⟩
  have e : algebraMap B (Localization.Away (k.val * g)) =
      (tr (dvd_mul_right k.val g)).comp ((tr hf).comp (algebraMap B (Localization.Away (idx1 : Idx B).val))) := by
    rw [tr_comp, tr_comp]
  rw [e, spMap_comp, pull_comp, spMap_comp, pull_comp]
  have hk' : pull _ (spMap (tr hf)) _ _
      (pull _ (spMap (algebraMap B (Localization.Away (idx1 : Idx B).val))) _ _ x) = 0 := hk
  rw [hk', map_zero]
