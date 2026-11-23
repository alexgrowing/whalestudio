import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem cube_of_exists_relAmple {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {H₀ : LB B.left} (hH : H₀.IsLB) (hamp : Out.RelAmple B H₀)
    {M : LB B.left} (hM : M.IsLB) : ∃ t : LB.Gen (Theta B M), t.IsGen := by
  have hG := GlobalTheory.laws_without_cohomology.1
  exact GlobalTheory.Biadditive.triv_of_faces hG hB hH hamp hM (thφ B (x3 B)) thε
    (fun r i b h => GlobalTheory.AbLaw.CubeGen.trivAt_of_formal hM r (GlobalTheory.AbLaw.CubeGen.prod_face r i b h))
    (fun r b h U _ k => GlobalTheory.AbLaw.CubeGen.prod_face r 0 b h U k)

theorem cube_of_relAmple :
    ∀ (S : Scheme.{0}) [IsReduced S] (B : Over S) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∃ t : LB.Gen (Theta B M), t.IsGen := fun _ _ _ _ _ _ hB hM hamp => cube_of_exists_relAmple hB hM hamp hM

end GlobalTheory.HkFam
