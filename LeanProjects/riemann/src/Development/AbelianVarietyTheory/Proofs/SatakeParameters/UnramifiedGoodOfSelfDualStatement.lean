import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedGoodOfSelfDual
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_good_of_self_dual : Inputs → SphericalLevelCondition .csd .unr → SphericalLevelCondition .good .unr := by
  first | (exact @GlobalTheory.RoadU.holdsS_good_unr) | (exact GlobalTheory.RoadU.holdsS_good_unr) | (intros; apply GlobalTheory.RoadU.holdsS_good_unr  <;> assumption)
