import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.AbelianUnitPowers.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.OneUseOf

namespace UpperTheory.V.Sd

structure MixedUnitPublishedTheorems : Prop where
  h : Af.HypothesesH
  adj : Lit.AdAutQ
  ind : Published.QuadInduction
  eis : Published.HilbertEisOne
  one : Lit.OneUse

end UpperTheory.V.Sd
