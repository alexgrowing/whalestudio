import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualDeRhamAndFilZeroDimAll
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateDual_deRham_and_filZero_dim_all : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm8 D := by
  first | exact @GlobalTheory.TateDualFil.main | exact GlobalTheory.TateDualFil.main | (intros; apply GlobalTheory.TateDualFil.main <;> assumption)
