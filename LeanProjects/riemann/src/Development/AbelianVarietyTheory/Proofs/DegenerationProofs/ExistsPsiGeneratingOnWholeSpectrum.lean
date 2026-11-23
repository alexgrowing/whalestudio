import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.PsiTop

theorem exists_setPsi_psiOn_top : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), ∃ ψ h, Nonempty (PsiOn (setPsi D ψ h) ⊤) := by
  intro R _ _ _ D
  have H : ∀ χ : D.X, ∃ t : LB.Gen (LB.LinComb D.P.L (K := PUnit) (Y := Spec (CommRingCat.of R))
      (fun _ => (D.c χ).left) (fun _ => -1)), t.IsGen := fun χ =>
    DVR.exists_gen_of_local D.P.L D.P.isLB _ _
  choose t ht using H
  refine ⟨fun χ => LB.pullGen D.P.L _ _ (t χ) (jK R), fun χ => DVR.pullGen_isGen _ _ _ _ (ht χ) _,
    ⟨⟨fun χ => LB.pullGen D.P.L _ _ (t χ) (⊤ : (Spec (CommRingCat.of R)).Opens).ι,
      fun χ => DVR.pullGen_isGen _ _ _ _ (ht χ) _, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩⟩
  refine (val_pull hJ _ _ _).trans ((val_pull hJ (t χ) _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  refine Eq.trans ?_ (val_pull hJ (t χ) _ _).symm
  rw [Category.assoc, Category.assoc, morphismRestrict_ι]

end GlobalTheory.PsiTop
end
