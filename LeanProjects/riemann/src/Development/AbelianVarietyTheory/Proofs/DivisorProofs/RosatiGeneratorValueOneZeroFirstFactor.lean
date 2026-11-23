import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAddInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RosZeroLeft

theorem val_lift_one_left : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), L.IsLB →
    IsAbelianScheme A → ∀ (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)), u.IsGen →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L) →
    ∀ (T : Over S) (y : T ⟶ A) (z : T.left) (J : (T.left ⟶ A.left) → L.ι), Good L z J →
      val u (lift (1 : T ⟶ A) y).left z J = 1 := by
  intro S A _ _ L hL hA f g _ _ u hu h₀ T y z J hJ
  have one_isGen : (LB.oneGen L (Y := A.left)).IsGen :=
    isGen_of_gm _ fun _ _ _ _ _ =>
      (map_one _).trans (Eq.symm ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
        (_root_.mul_one _)))
  have key := gen_unique' hL (u := LB.pullGen L _ _ u (lift (1 : A ⟶ A) (𝟙 A)).left)
    (u' := LB.oneGen L) (fun U _ h => by
      refine (Fintype.prod_empty _).trans (Eq.symm ((prod_ros f g 1 (𝟙 A) h).trans ?_))
      rw [MonObj.one_comp, _root_.one_mul, _root_.one_mul, Category.id_comp]
      simp)
    A.hom η[A].left (Over.w η[A]) (GlobalTheory.globalFns_holds _ _ hA).2 (DVR.pullGen_isGen _ _ _ _ hu _)
    one_isGen (fun y I hI => by
      have := val_corr hI h₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp, val_one] at this
      rw [val_pull hI, val_one, ← Over.comp_left]
      have e : η[A] ≫ lift (1 : A ⟶ A) (𝟙 A) = lift η[A] η[A] := by simp [Hom.one_def]
      rw [e]; exact this) _ y.left z J hJ
  rw [val_pull hJ, val_one, ← Over.comp_left, comp_lift, Category.comp_id, MonObj.comp_one] at key
  exact key

end GlobalTheory.RosZeroLeft
