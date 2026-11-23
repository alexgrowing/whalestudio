import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem tangent_lift_of_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (x : KeyIn ℂ)
    (φ : x.P.A.left ⟶ D.P.A.left), IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ →
    eSec x.P.A ≫ φ = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A →
    ∀ b : TE R ℂ ⟶ D.P.A, redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left →
      ∃ b' : epsR ℂ ⟶ x.P.A, IsTangent b' ∧ b'.left ≫ φ = b.left := by
  intro R _ _ _ D x φ hφ he b hb
  have hTF : (TF (R := R) ℂ).hom = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := by
    simp only [TF, Over.mk_hom, jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hw : b.left ≫ D.P.A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫
      spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) := by
    rw [Over.w b, ← hTF]; rfl
  let l := hφ.1.lift b.left (spMap (algebraMap ℂ (DualNumber ℂ))) hw
  have hl1 : l ≫ φ = b.left := hφ.1.lift_fst _ _ _
  have hl2 : l ≫ x.P.A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := hφ.1.lift_snd _ _ _
  refine ⟨Over.homMk l hl2, ?_, hl1⟩
  show spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ l = eSec x.P.A
  apply hφ.1.hom_ext
  · rw [Category.assoc, hl1, he]
    change redE ℂ ≫ b.left = _
    rw [hb, DegPre.zeroF, Over.comp_left, ← hTF]
    congr 1
  · rw [Category.assoc, hl2]
    have h1 : eSec x.P.A ≫ x.P.A.hom = 𝟙 _ := by
      simp only [eSec]
      rw [Over.w η[x.P.A]]; rfl
    rw [h1]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
      ext z; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id]; rfl

end GlobalTheory.MBLow.Cl
