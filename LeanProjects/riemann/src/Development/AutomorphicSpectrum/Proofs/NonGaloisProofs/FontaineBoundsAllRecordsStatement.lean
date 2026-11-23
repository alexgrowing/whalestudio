import Mathlib
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.FontaineBoundsAllRecords
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localSituation_adm7_of_D7 : ∀ D : D7, LocalSituation.adm7 D := by
  first | exact @GlobalTheory.CompanionTheory.Fontaine.adm7_all | exact GlobalTheory.CompanionTheory.Fontaine.adm7_all | (intros; apply GlobalTheory.CompanionTheory.Fontaine.adm7_all <;> assumption)
