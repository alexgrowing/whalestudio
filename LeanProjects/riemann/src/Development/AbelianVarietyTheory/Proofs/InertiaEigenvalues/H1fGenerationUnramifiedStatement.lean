import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGenerationUnramified
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h1fGeneratorBoundAll_loc : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorBoundAll D.loc := by
  first | exact @GlobalTheory.GenCountUnram.admGenL_all | exact GlobalTheory.GenCountUnram.admGenL_all | (intros; apply GlobalTheory.GenCountUnram.admGenL_all <;> assumption)
