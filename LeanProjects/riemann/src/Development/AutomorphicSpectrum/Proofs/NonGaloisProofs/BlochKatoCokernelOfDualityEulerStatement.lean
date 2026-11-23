import Mathlib
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.BlochKatoCokernelOfDualityEuler
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_cokernel_of_duality_euler : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), bkACore ((D.loc l).PD K) → bkBCore ((D.loc l).PD K) → LocalSituation.bkC ((D.loc l).PD K) := by
  first | exact @GlobalTheory.CompanionTheory.BKTorsion.main | exact GlobalTheory.CompanionTheory.BKTorsion.main | (intros; apply GlobalTheory.CompanionTheory.BKTorsion.main <;> assumption)
