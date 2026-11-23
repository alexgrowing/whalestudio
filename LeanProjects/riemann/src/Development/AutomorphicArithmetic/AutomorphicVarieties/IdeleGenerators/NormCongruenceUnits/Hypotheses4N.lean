import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.Hypotheses2

namespace UpperTheory.V.Sd

structure Hypotheses4N : Prop where
  h : Af.HypothesesH
  adj : Published.AdjointLift
  cube : Published.SymCube
  ind : Published.QuadInduction
  eis : Published.HilbertEisOne
  one : Published.HilbertOne

end UpperTheory.V.Sd
