import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.MinimalHyps
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GelfandKazhdanReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PCuspSS
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistsContRep

namespace UpperTheory.V.Af

open UpperTheory.V.Published

structure MinimalHyp2 : Prop where
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitN
  cohC : ClozelCohC
  cohR : ClozelCohR
  conjC : ClozelConjC
  conjR : ClozelConjR
  borelC : BorelInjC
  borelR : BorelInjR
  galR : GaloisRepReal
  smoR : StrongMultOneReal
  bc : QuadBaseChange
  thorne : ThorneAdjoint
  descU : DescentUnitary
  types : TypesNZero
  sign : SignCsd
  cyc : CyclicBaseChange
  jl : JacquetLanglands
  finR : FormsFiniteReal

end UpperTheory.V.Af
