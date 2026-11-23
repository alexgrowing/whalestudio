import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_sums_twists_characters_expected_jumps : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ S : TopSit P, S.CrysCalc := by
  first | exact @GlobalTheory.TopSteps.CrysRules.crysCalc | exact GlobalTheory.TopSteps.CrysRules.crysCalc | (intros; apply GlobalTheory.TopSteps.CrysRules.crysCalc <;> assumption)
