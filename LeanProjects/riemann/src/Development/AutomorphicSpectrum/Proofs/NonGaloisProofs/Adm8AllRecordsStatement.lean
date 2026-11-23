import Mathlib
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Adm8AllRecords
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localSituation_adm8_forall : ∀ D : D7, LocalSituation.adm8 D := by
  first | exact @GlobalTheory.CompanionTheory.TateDualRow.blochKato_dimFormula_all_finiteExt_coeffField | exact GlobalTheory.CompanionTheory.TateDualRow.blochKato_dimFormula_all_finiteExt_coeffField | (intros; apply GlobalTheory.CompanionTheory.TateDualRow.blochKato_dimFormula_all_finiteExt_coeffField <;> assumption)
