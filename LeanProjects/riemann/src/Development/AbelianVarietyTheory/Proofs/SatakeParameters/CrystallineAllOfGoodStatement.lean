import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CrystallineAllOfGood
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_all_of_good : Inputs → SphericalLevelCondition .good .crys → SphericalLevelCondition .all .crys := by
  first | (exact @GlobalTheory.RoadU.holdsS_all_crys) | (exact GlobalTheory.RoadU.holdsS_all_crys) | (intros; apply GlobalTheory.RoadU.holdsS_all_crys  <;> assumption)
