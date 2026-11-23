import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntegersFiniteExtensionOpen
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_integers_finite_extension_open : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), IsOpen ((OL LL : Subalgebra ℤ_[l] ↥LL.1) : Set ↥LL.1) := by
  first | exact @GlobalTheory.isOpen_integers_finExt | exact GlobalTheory.isOpen_integers_finExt | (intros; apply GlobalTheory.isOpen_integers_finExt <;> assumption)
