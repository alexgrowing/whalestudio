import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechFlatComplex
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CechFlatComplex : CIFlat := by
  first | exact @GlobalTheory.CompanionTheory.CIFlatPf.ciFlat | exact GlobalTheory.CompanionTheory.CIFlatPf.ciFlat | (intros; apply GlobalTheory.CompanionTheory.CIFlatPf.ciFlat <;> assumption)
