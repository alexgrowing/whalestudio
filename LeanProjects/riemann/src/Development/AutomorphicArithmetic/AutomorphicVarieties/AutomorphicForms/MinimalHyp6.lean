import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CsdMonoOddLitN
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.MinimalHyp2
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBCwOfQuadBC0
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.StrongMultOneReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ClozelCohC

namespace UpperTheory.V.Af

open UpperTheory.V.Published

structure MinimalHyp6 : Prop where
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitN
  conjC : ClozelConjC
  borelC : BorelInjC
  galR : GaloisRepReal
  thorne : ThorneAdjoint
  descU : Z.Desc.DescWeak
  cyc : CyclicBaseChange

theorem MinimalHyp6.toClassicalTheorems (h : MinimalHyp6) : Hypotheses₂ :=
  { litN := h.litN, cohC := clozelCohC h.litN, conjC := h.conjC, borelC := h.borelC,
    galR := Z.Bc.galoisRepRankTwoReal_of h.galR, smoR := strongMultOneReal, gkR := gelfandKazhdanReal strongMultOneReal, admR := admissibleReal,
    bc := Br.quadBC0_of_cyclic h.litN.aut.art strongMultOneReal h.cyc,
    newform := newformRepOf cuspSemisimpleReal admissibleReal,
    ss := UpperTheory.Lit.Car.csdSs_litN h.litN, mono := UpperTheory.Lit.Car.csdMonoOdd_litN h.litN }

end UpperTheory.V.Af
