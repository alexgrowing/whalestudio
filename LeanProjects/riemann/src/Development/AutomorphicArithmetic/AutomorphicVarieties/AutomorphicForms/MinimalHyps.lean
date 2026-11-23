import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.DefQuatExists
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformRepOf

namespace UpperTheory.V.Af

open UpperTheory.V.Published

structure MinimalHyps : Prop where
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitN
  cohC : ClozelCohC
  cohR : ClozelCohR
  conjC : ClozelConjC
  conjR : ClozelConjR
  borelC : BorelInjC
  borelR : BorelInjR
  galR : GaloisRepReal
  smoR : StrongMultOneReal
  gkR : GelfandKazhdanReal
  admR : AdmissibleReal
  bc : QuadBaseChange
  thorne : ThorneAdjoint
  descU : DescentUnitary
  types : TypesNZero
  sign : SignCsd
  cyc : CyclicBaseChange
  jl : JacquetLanglands
  finR : FormsFiniteReal
  ssR : CuspSemisimpleReal

theorem MinimalHyps.toClassicalTheorems (h : MinimalHyps) : Hypotheses₂ :=
  { litN := h.litN, cohC := h.cohC, conjC := h.conjC, borelC := h.borelC,
    galR := Z.Bc.galoisRepRankTwoReal_of h.galR, smoR := h.smoR, gkR := h.gkR, admR := h.admR, bc := Br.quadBC0_of_quadBaseChange h.bc,
    newform := newformRepOf h.ssR h.admR }

end UpperTheory.V.Af
