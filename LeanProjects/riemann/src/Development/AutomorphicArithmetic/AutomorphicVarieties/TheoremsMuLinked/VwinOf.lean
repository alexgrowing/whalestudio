import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.VwinOfInputs
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.OrdVan
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.CoreOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.PhiAll

open UpperTheory.Top UpperTheory.V.HV

namespace UpperTheory.V.Th

theorem core (hH : Af.HypothesesH) (hC : Pa.CohP) : Core := core_of (ordVan2 hH) (W.phiAll hC)

theorem adL (hH : Af.HypothesesH) (hC : Pa.CohP) : AdL := adL_of (U.localGaloisCohomology₂ hH.litN) (core hH hC)

end UpperTheory.V.Th
