import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AtFormAdmOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecLowPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecInfPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Admissible
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne

namespace CompanionTheory.Lime.BM

theorem inputs : CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs := by
  refine ⟨Formalism.L2.SG.OwnFacts.factDecLow.out, Formalism.L2.SG.BesselDiscreteSeries.decInf, ?_, trivial⟩
  first
    | exact Formalism.L2.SG.Pf.k_finite_smooth
    | exact Formalism.L2.SG.Pf.k_finite_smooth_bessel

end CompanionTheory.Lime.BM
