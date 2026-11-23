import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCoordEnd
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordCompatOfPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick

noncomputable section
namespace GlobalTheory.Mum.EndThick

theorem isCoordEnd_thickMap_compat : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ) (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X) (u : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A a' a) rosatiε)) (F : thickObj R I e G ⟶ thickObj R I e G) (F' : thickObj R I (e + 1) G ⟶ thickObj R I (e + 1) G), IsCoordEnd (U.gt e) a a' h' u F → IsCoordEnd (U.gt (e + 1)) a a' h' u F' → thickMap R I e G ≫ F'.left = F.left ≫ thickMap R I e G := by
  intro R _ _ I D A G _ _ U e a a' h' u F F' hF hF'
  have hq := U.gt_q e
  have hO : GlobalTheory.LevelCompat.thickMapOver I e G ≫ (U.gt (e + 1)).pG = (U.gt e).pG := Over.OverMorphism.ext hq
  have hL : ∀ χ, thickMap R I e G ≫ (lift (toUnit _ ≫ D.toPre.c χ) (U.gt (e + 1)).pG).left =
      (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left := by
    intro χ
    have : GlobalTheory.LevelCompat.thickMapOver I e G ≫ lift (toUnit _ ≫ D.toPre.c χ) (U.gt (e + 1)).pG =
        lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG := by
      simp only [comp_lift, comp_toUnit_assoc, hO]
    exact congrArg (·.left) this
  refine GlobalTheory.TorusCoord.ext_of_val (U.gt (e + 1)) _ _ ?_ ?_
  · calc (thickMap R I e G ≫ F'.left) ≫ (U.gt (e + 1)).pG.left
          = thickMap R I e G ≫ ((U.gt (e + 1)).pG.left ≫ a.left) := by rw [Category.assoc, hF'.1]
      _ = (U.gt e).pG.left ≫ a.left := by rw [← Category.assoc, hq]
      _ = F.left ≫ (U.gt e).pG.left := hF.1.symm
      _ = (F.left ≫ thickMap R I e G) ≫ (U.gt (e + 1)).pG.left := by rw [Category.assoc, hq]
  · intro χ w J hJ
    have e1 := hF'.2 χ _ (thickMap R I e G) w J hJ
    have e2 := hF.2 χ _ (𝟙 _) w J hJ
    rw [Category.id_comp] at e2
    rw [e1, ← val_pull hJ, val_corr hJ (U.gt_t e χ), e2]
    congr 1
    · have e3 := val_pull hJ ((U.gt (e + 1)).t (h' χ)) (thickMap R I e G) (𝟙 _)
      rw [Category.id_comp] at e3
      rw [← e3, val_corr hJ (U.gt_t e _)]
    · rw [val_pull hJ, val_pull hJ, hL, Category.id_comp]

end GlobalTheory.Mum.EndThick
end
