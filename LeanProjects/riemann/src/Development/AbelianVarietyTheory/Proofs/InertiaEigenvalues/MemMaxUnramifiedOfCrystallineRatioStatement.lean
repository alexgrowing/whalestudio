import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaxUnramifiedOfCrystallineRatio
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maxUnramified_of_crystallineRatio : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (a b : P.R.B) (x : Om l), b ≠ 0 → P.ιB a = algebraMap (Om l) P.R.BdR x * P.ιB b → x ∈ MaximalUnramifiedExtension l := by
  first | exact @GlobalTheory.FracAlg.mem_Kur_of_ratio | exact GlobalTheory.FracAlg.mem_Kur_of_ratio | (intros; apply GlobalTheory.FracAlg.mem_Kur_of_ratio <;> assumption)
