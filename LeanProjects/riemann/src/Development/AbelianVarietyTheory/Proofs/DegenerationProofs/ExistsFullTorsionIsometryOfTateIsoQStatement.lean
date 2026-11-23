import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullTorsionIsometryOfTateIsoQ
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_full_torsion_isometry_of_tateIsoQ : GlobalTheory.UT.LL → AllD fun {E} _ _ _ {H} D => ∀ (C : Type) [NormedField C] (o : Full D C) (M : Mdl o) (I' : TateIsoQ D M.P.D.toPre M.P.oD C), ∃ I : FullI o, I.ζ = I'.ζ ∧ ∀ j, 0 < j → ∀ x, ∃ z : TFK (R := M.W) C ⟶ M.P.A.A, z.left = (I.ev j x).left ≫ M.φ ∧ M.P.ToA C j (I'.ev j x) z := by
  first | exact @GlobalTheory.Relabel.exists_fullI_of_tateIsoQ | exact GlobalTheory.Relabel.exists_fullI_of_tateIsoQ | (intros; apply GlobalTheory.Relabel.exists_fullI_of_tateIsoQ <;> assumption)
