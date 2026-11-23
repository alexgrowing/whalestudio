import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT

theorem exists_genericFibre_iso_of_model_iso : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I D A G) (U' : UnifPre I D' A' G') (ψ : G' ≅ G), IsMonHom ψ.hom → LBIso U'.LG.L (U.LG.L.pull ψ.hom.left) → ∃ φ : A'.A ≅ A.A, IsMonHom φ.hom ∧ (Over.pullback (jK R)).map ψ.hom ≫ U.gen.hom = U'.gen.hom ≫ φ.hom ∧ LBIso A'.L (A.L.pull φ.hom.left) := by
  intro R _ _ I D D' A A' G G' _ _ _ _ U U' ψ hψ hL
  have := U.gen_hom
  have := U'.gen_hom
  have := hψ
  have hm : ((Over.pullback (jK R)).map ψ.hom).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R) ≫ ψ.hom.left :=
    pullback.lift_fst _ _ _
  have hi : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
  refine ⟨U'.gen.symm ≪≫ (Over.pullback (jK R)).mapIso ψ ≪≫ U.gen, ?_, by simp, ?_⟩
  · show IsMonHom (U'.gen.inv ≫ (Over.pullback (jK R)).map ψ.hom ≫ U.gen.hom)
    infer_instance
  · have h₁ : LBIso A'.L (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R))) :=
      LBIso.chartPull (chartPullSec A'.L _ U'.gen.inv.left hi)
        (chartPullSame U'.LG.L _ (fun _ => pullback.fst G'.hom (jK R)) _ U'.gen.inv.left fun _ => rfl) U'.ext
    have h₂ : LBIso (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)))
        (U.LG.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) ≫ ψ.hom.left)) :=
      LBIso.chartPull (chartPullPull U'.LG.L _ _ rfl)
        (chartPullSame U.LG.L _ (fun _ => ψ.hom.left) _ _ fun _ => rfl) hL
    have h₃ : LBIso (A.L.pull (U'.gen.symm ≪≫ (Over.pullback (jK R)).mapIso ψ ≪≫ U.gen).hom.left)
        (U.LG.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) ≫ ψ.hom.left)) :=
      LBIso.chartPull (h := U'.gen.inv.left ≫ ((Over.pullback (jK R)).map ψ.hom).left)
        (chartPullSame A.L _ (fun _ => U.gen.hom.left) _ _ fun _ => (Category.assoc _ _ _).symm)
        (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ =>
          (Category.assoc _ _ _).trans ((congrArg (U'.gen.inv.left ≫ ·) hm.symm).trans (Category.assoc _ _ _).symm))
        U.ext
    exact LBIso.trans A'.isLB (pull_isLB U.LG.isLB _) (pull_isLB A.isLB _)
      (LBIso.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB U.LG.isLB _) h₁ h₂) h₃.symm

end GlobalTheory.UT
end
