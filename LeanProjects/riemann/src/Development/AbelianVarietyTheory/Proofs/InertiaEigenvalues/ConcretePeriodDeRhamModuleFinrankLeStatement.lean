import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLe
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.concretePeriod_deRham_module_finrank_le : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) ρ) ∧ Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ) ≤ Module.finrank ℚ_[l] ↥K.1 * Module.finrank ↥LL.1 V := by
  first | exact @GlobalTheory.Per.TiedDdR.ddR_finrank_le | exact GlobalTheory.Per.TiedDdR.ddR_finrank_le | (intros; apply GlobalTheory.Per.TiedDdR.ddR_finrank_le <;> assumption)
