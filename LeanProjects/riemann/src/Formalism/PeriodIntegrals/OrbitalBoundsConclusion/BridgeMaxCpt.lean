import Mathlib
import Formalism.PeriodIntegrals.AdBridgeSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MaximalCompactConjugacy.Assembly
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeRealK
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeFinK

theorem adelic_maximal_compact : ∀ I : Formalism.MainNotions.S.AutInst, Formalism.L2.SG.AdBridge.AdBridgeK I :=
  PI.BridgeMaxCptWork.bridgeMaxCpt_of adelic_compact_real_places adelic_compact_finite_places
