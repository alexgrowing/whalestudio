import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamVectorExtensionIsoOfHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamVectorExtensionIso_of_hodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.DeRhamVectorExtension := by
  first | exact @GlobalTheory.deRhamVectorExtension_of_abelianHodgeDeRham | exact GlobalTheory.deRhamVectorExtension_of_abelianHodgeDeRham | (intros; apply GlobalTheory.deRhamVectorExtension_of_abelianHodgeDeRham <;> assumption)
