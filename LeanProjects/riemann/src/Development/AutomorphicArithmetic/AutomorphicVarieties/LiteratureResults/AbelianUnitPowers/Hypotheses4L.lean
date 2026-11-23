import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.AbelianUnitPowers.Hypotheses2

namespace UpperTheory.V.Sd

structure Hypotheses4L : Prop where
  h : Af.HypothesesH
  adj : Lit.AdAutQ
  cube : Lit.SymmetricCubeAutomorphyOverRationals
  ind : Published.QuadInduction
  eis : Published.HilbertEisOne
  one : Published.HilbertOne

end UpperTheory.V.Sd
