import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem isPullback_kernel_baseChange {S S' : Scheme.{0}} (f : S' ⟶ S) {T G B : Over S} [GrpObj B]
    {i : T ⟶ G} {q : G ⟶ B} (h : IsPullback i (toUnit _) q (η[B])) :
    IsPullback ((Over.pullback f).map i) (toUnit _) ((Over.pullback f).map q) (η[(Over.pullback f).obj B]) := by
  refine (h.map (Over.pullback f)).of_iso (Iso.refl _) (Iso.refl _)
    (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _) (by simp) (toUnit_unique _ _) (by simp) ?_
  simp [Functor.obj.η_def]

theorem isPullback_pullback_map_left {S S' : Scheme.{0}} (f : S' ⟶ S) {G B : Over S} (q : G ⟶ B) :
    IsPullback (pullback.fst G.hom f) ((Over.pullback f).map q).left q.left (pullback.fst B.hom f) := by
  have h₁ : IsPullback (pullback.fst G.hom f) (((Over.pullback f).map q).left ≫ pullback.snd B.hom f)
      (q.left ≫ B.hom) f := by
    have : ((Over.pullback f).map q).left ≫ pullback.snd B.hom f = pullback.snd G.hom f :=
      Over.w ((Over.pullback f).map q)
    rw [this, Over.w]
    exact IsPullback.of_hasPullback _ _
  exact h₁.of_bot (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)

theorem TQ.exists_isGrpPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X] (G : Over S)
    [GrpObj G] (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F →
    ∀ (Q : TQ G X) (Q' : TQ G' X), TorusCompat f F Q'.i Q.i →
    ∃ β : Q'.B.left ⟶ Q.B.left, Q'.q.left ≫ β = F ≫ Q.q.left ∧ IsGrpPullback Q'.B Q.B f β := by
  intro S S' f X _ G _ G' _ F hF Q Q' hT
  obtain ⟨e, he, heF⟩ := grpPullback_iso hF (isGrpPullback_pullback G f)
  have := Q.q_hom
  have := Q.q_flat
  have := Q.q_surj
  have := Q.q_affine
  have := Q'.q_affine
  have sq := isPullback_pullback_map_left f Q.q
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S').map e.hom))
  have hi : Q'.i ≫ e.hom = (SplitTorus.bcIso f X).hom ≫ (Over.pullback f).map Q.i := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have a := (isPullback_pullback_map_left f Q.i).w
    have b := SplitTorus.bcIso_hom_fst f X
    exact ((Category.assoc _ _ _).trans ((congrArg (Q'.i.left ≫ ·) heF).trans (torusCompat_iff.1 hT).symm)).trans
      ((congrArg (· ≫ Q.i.left) b.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) a).trans (Category.assoc _ _ _).symm)))
  have hk : IsPullback Q'.i (toUnit _) (e.hom ≫ (Over.pullback f).map Q.q) (η[(Over.pullback f).obj Q.B]) := by
    refine (isPullback_kernel_baseChange f Q.isKernel).of_iso (SplitTorus.bcIso f X).symm e.symm (Iso.refl _)
      (Iso.refl _) ?_ (toUnit_unique _ _) (by simp) (by simp)
    rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, hi, Iso.inv_hom_id_assoc]
  have h₁ : Flat ((Over.pullback f).map Q.q).left := MorphismProperty.of_isPullback (P := @Flat) sq inferInstance
  have h₂ : Surjective ((Over.pullback f).map Q.q).left :=
    MorphismProperty.of_isPullback (P := @Surjective) sq inferInstance
  have h₃ : QuasiCompact ((Over.pullback f).map Q.q).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  obtain ⟨β, hβ, hq⟩ := flatQuotient_iso_of_same_kernel S' G' ((Over.pullback f).obj Q.B) Q'.B _ _
    (e.hom ≫ (Over.pullback f).map Q.q) Q'.i Q'.q Q'.i inferInstance Q'.i_hom
    (by rw [Over.comp_left]; infer_instance) (by rw [Over.comp_left]; infer_instance)
    (by rw [Over.comp_left]; infer_instance) hk Q'.q_hom Q'.i_hom Q'.q_flat Q'.q_surj inferInstance Q'.isKernel
    hk.w Q'.isKernel.w
  refine ⟨β.hom.left ≫ pullback.fst Q.B.hom f, ?_,
    ((isGrpPullback_of_iso β).comp (isGrpPullback_pullback Q.B f)).congr (Category.id_comp f) rfl⟩
  rw [← Category.assoc, ← Over.comp_left, hq, Over.comp_left, Category.assoc, ← heF, Category.assoc]
  exact congrArg (_ ≫ ·) sq.w.symm

end GlobalTheory.UU
