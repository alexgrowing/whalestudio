import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCrystallineExtensionCriterion
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_crystalline_extension_criterion : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm15 D := by
  first | exact @GlobalTheory.ExtCrysCrit.blochKato_ext_all | exact GlobalTheory.ExtCrysCrit.blochKato_ext_all | (intros; apply GlobalTheory.ExtCrysCrit.blochKato_ext_all <;> assumption)
