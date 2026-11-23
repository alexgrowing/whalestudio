import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.InputsOfHida
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoefIsCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.MinimalHyp2
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.IsOpenKerKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.Seed3N
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.SeedII
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.SeedIII
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.AutNew

open UpperTheory.Top

namespace UpperTheory.V

open UpperTheory.V.Published

structure HypothesesV : Prop where
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
  adj : AdjointLift
  cube : SymCube
  ind : QuadInduction
  eis : HilbertEisOne
  one : HilbertOne
  kato : Kato
  k : KPublished

end UpperTheory.V
