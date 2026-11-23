import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.MinimalHyp5
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.KBridgeOfKPublishedW
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HypothesesV
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KatoEulerSystems.VwinOfInputs

open UpperTheory.Top

namespace UpperTheory.V

open UpperTheory.V.Published

structure PublishedTheorems : Prop where
  conjC : ClozelConjC
  borelC : BorelInjC
  galR : GaloisRepReal
  thorne : ThorneAdjoint
  descU : DescentUnitary
  types : TypesNZero
  cyc : CyclicBaseChange
  jl : JacquetLanglands
  adj : AdjointLift
  cube : SymCube
  ind : QuadInduction
  eis : HilbertEisOne
  one : HilbertOne
  kato : Lit.KatoO
  k : KPublishedW

end UpperTheory.V
