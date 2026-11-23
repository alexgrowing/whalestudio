import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsMonoOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBC0OfQuadBaseChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.GaloisRepRankTwoRealOf

namespace UpperTheory.V.Af

open UpperTheory.V.Published

structure Hypotheses₂ : Prop where
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitN
  cohC : ClozelCohC
  conjC : ClozelConjC
  borelC : BorelInjC
  galR : Z.Bc.GaloisRepRankTwoReal
  smoR : StrongMultOneReal
  gkR : GelfandKazhdanReal
  admR : AdmissibleReal
  bc : Br.QuadBC0
  newform : NewformRep
  ss : Lev.CsdSs := Lev.csdSs_of_full litN.aut.car
  mono : Lev.CsdMonoOdd := Lev.csdMonoOdd_of_full litN.aut.car

end UpperTheory.V.Af
