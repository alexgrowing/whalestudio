import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumps
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_restrict_finite_extension_jumps : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm12 D := by
  first | exact @GlobalTheory.Per.ResFinite.adm12_elementDenominator | exact GlobalTheory.Per.ResFinite.adm12_elementDenominator | (intros; apply GlobalTheory.Per.ResFinite.adm12_elementDenominator <;> assumption)
