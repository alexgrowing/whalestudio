import Mathlib
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.FundamentalSequenceContinuityAll
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localSituation_adm6_of_D7 : ∀ D : D7, LocalSituation.adm6 D := by
  first | exact @GlobalTheory.CompanionTheory.AdmSix.adm6_all | exact GlobalTheory.CompanionTheory.AdmSix.adm6_all | (intros; apply GlobalTheory.CompanionTheory.AdmSix.adm6_all <;> assumption)
