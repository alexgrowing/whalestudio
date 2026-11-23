import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRegAlgTwistOfHalfIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoreAllOfCore
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalCodimOneStalkDvr
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong
open GlobalTheory.RoadU

namespace GlobalTheory.Row9

theorem coreAll_of_rowStarCore : Inputs → GlobalTheory.RoadW.RowStarCore → CoreAll :=
  fun hI hR => GlobalTheory.RoadU.coreAll_of_core hI (GlobalTheory.RoadW.core_of_rowStarCore hR)

end GlobalTheory.Row9
