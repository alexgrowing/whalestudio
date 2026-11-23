import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.MinimalHyp2
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBCwOfQuadBC0
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.StrongMultOneReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ClozelCohC

namespace UpperTheory.V.Af

open UpperTheory.V.Published

structure MinimalHyp5 : Prop where
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitN
  conjC : ClozelConjC
  borelC : BorelInjC
  galR : GaloisRepReal
  thorne : ThorneAdjoint
  descU : DescentUnitary
  types : TypesNZero
  cyc : CyclicBaseChange
  jl : JacquetLanglands

theorem MinimalHyp5.toClassicalTheorems (h : MinimalHyp5) : Hypotheses₂ :=
  { litN := h.litN, cohC := clozelCohC h.litN, conjC := h.conjC, borelC := h.borelC,
    galR := Z.Bc.galoisRepRankTwoReal_of h.galR, smoR := strongMultOneReal, gkR := gelfandKazhdanReal strongMultOneReal, admR := admissibleReal,
    bc := Br.quadBC0_of_cyclic h.litN.aut.art strongMultOneReal h.cyc,
    newform := newformRepOf cuspSemisimpleReal admissibleReal }

end UpperTheory.V.Af
