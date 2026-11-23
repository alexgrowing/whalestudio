import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Sh

variable {R : Type} [CommRing R]

theorem isAbelianScheme_tensor' (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A)
    (hB : IsAbelianScheme B) : IsAbelianScheme (A ⊗ B) :=
  ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB

theorem smooth_tensor {A B : Over (Sp R)} {g g' : ℕ} (hA : SmoothOfRelativeDimension g A.hom)
    (hB : SmoothOfRelativeDimension g' B.hom) : SmoothOfRelativeDimension (g + g') (A ⊗ B).hom := by
  have e : (A ⊗ B).hom = Limits.pullback.fst A.hom B.hom ≫ A.hom := rfl
  haveI := hA
  haveI : SmoothOfRelativeDimension g' (Limits.pullback.fst A.hom B.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := g')).of_isPullback
      (IsPullback.of_hasPullback A.hom B.hom).flip hB
  rw [e, add_comm]
  infer_instance

end MainStatements.Hodge.Sh
