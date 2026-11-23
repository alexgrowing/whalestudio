import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def imageIdealSheaf {S X : Scheme.{u}} (σ : S ⟶ X) (I : S.IdealSheafData) : X.IdealSheafData :=
  (I.subschemeι ≫ σ).ker

theorem map_eq_imageIdealSheaf {S X : Scheme.{u}} (f : S ⟶ X) (I : S.IdealSheafData) :
    I.map f = imageIdealSheaf f I := rfl

theorem imageIdealSheaf_comp {W A B : Scheme.{u}} (g : W ⟶ A) (w : A ⟶ B) (I : W.IdealSheafData) :
    imageIdealSheaf (g ≫ w) I = imageIdealSheaf w (imageIdealSheaf g I) := by
  simp only [← map_eq_imageIdealSheaf, Scheme.IdealSheafData.map_comp]

theorem imageIdealSheaf_eq_ker {S X : Scheme.{u}} (σ : S ⟶ X) (I : S.IdealSheafData) :
    imageIdealSheaf σ I = (I.subschemeι ≫ σ).ker := rfl

def SequenceOfBlowups.Isomorphic {X : Scheme.{u}} (B B' : SequenceOfBlowups X) : Prop :=
  B.length = B'.length ∧
    ∃ e : ∀ i : ℕ, i ≤ B.length → (B.schemeAt i ≅ B'.schemeAt i),
      ((e 0 (Nat.zero_le _)).hom ≫ B'.isoZero.hom = B.isoZero.hom) ∧
      (∀ i : ℕ, ∀ hi : i < B.length,
        (e (i + 1) hi).hom ≫ B'.transitionMapSucc i = B.transitionMapSucc i ≫ (e i hi.le).hom) ∧
      (∀ i : ℕ, ∀ hi : i < B.length,
        (B'.center i).comap (e i hi.le).hom = B.center i)

theorem SequenceOfBlowups.isomorphic_refl {X : Scheme.{u}} (B : SequenceOfBlowups X) : B.Isomorphic B := by
  refine ⟨rfl, fun i _ => Iso.refl _, ?_, ?_, ?_⟩ <;> simp

def IsPushforwardBlowupSeq {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X) : Prop :=
  BS.length = B.length ∧
    ∃ σ : ∀ i : ℕ, i ≤ BS.length → (BS.schemeAt i ⟶ B.schemeAt i),
      (∀ i : ℕ, ∀ hi : i ≤ BS.length, IsClosedImmersion (σ i hi)) ∧
      (σ 0 (Nat.zero_le _) ≫ B.isoZero.hom = BS.isoZero.hom ≫ j) ∧
      (∀ i : ℕ, ∀ hi : i < BS.length,
        σ (i + 1) hi ≫ B.transitionMapSucc i = BS.transitionMapSucc i ≫ σ i hi.le) ∧
      (∀ i : ℕ, ∀ hi : i < BS.length,
        B.center i = imageIdealSheaf (σ i hi.le) (BS.center i)) ∧
      (∀ i : ℕ, ∀ hi : i < BS.length,
        (σ (i + 1) hi).ker =
          Blowup.strictTransform (B.transitionMapSucc i) (B.center i) (σ i hi.le).ker)

def IsStrictPullbackBlowupSeq {X' X : Scheme.{u}} (φ : X' ⟶ X)
    (B' : SequenceOfBlowups X') (B : SequenceOfBlowups X) : Prop :=
  B'.length = B.length ∧
    ∃ σ : ∀ i : ℕ, i ≤ B'.length → (B'.schemeAt i ⟶ B.schemeAt i),
      (σ 0 (Nat.zero_le _) ≫ B.isoZero.hom = B'.isoZero.hom ≫ φ) ∧
      (∀ i : ℕ, ∀ hi : i < B'.length,
        IsPullback (σ (i + 1) hi) (B'.transitionMapSucc i) (B.transitionMapSucc i) (σ i hi.le)) ∧
      (∀ i : ℕ, ∀ hi : i < B'.length,
        B'.center i = (B.center i).comap (σ i hi.le))

private def schemeAtHomOfEqZero {X' X : Scheme.{u}} (g : X' ⟶ X) (t : SequenceOfBlowups X') (s : SequenceOfBlowups X)
    (i : ℕ) (hi0 : i = 0) : t.schemeAt i ⟶ s.schemeAt i :=
  eqToHom (congrArg t.schemeAt hi0) ≫ t.isoZero.hom ≫ g ≫ s.isoZero.inv ≫
    eqToHom (congrArg s.schemeAt hi0).symm

theorem IsStrictPullbackBlowupSeq.of_length_zero {X' X : Scheme.{u}} (g : X' ⟶ X) (t : SequenceOfBlowups X')
    (s : SequenceOfBlowups X) (ht : t.length = 0) (hs : s.length = 0) :
    IsStrictPullbackBlowupSeq g t s := by
  refine ⟨ht.trans hs.symm,
    fun i hi => schemeAtHomOfEqZero g t s i (Nat.eq_zero_of_le_zero (le_of_le_of_eq hi ht)),
    ?_, ?_, ?_⟩
  · simp [schemeAtHomOfEqZero]
  · intro i hi
    exact absurd (lt_of_lt_of_eq hi ht) (Nat.not_lt_zero i)
  · intro i hi
    exact absurd (lt_of_lt_of_eq hi ht) (Nat.not_lt_zero i)

theorem IsStrictPullbackBlowupSeq.length_eq {X' X : Scheme.{u}} {φ : X' ⟶ X}
    {B' : SequenceOfBlowups X'} {B : SequenceOfBlowups X} (h : IsStrictPullbackBlowupSeq φ B' B) :
    B'.length = B.length := h.1

end FunctorialResolution.EmbeddedResolution
