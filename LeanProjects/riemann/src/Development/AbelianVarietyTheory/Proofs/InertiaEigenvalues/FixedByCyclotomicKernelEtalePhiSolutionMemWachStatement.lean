import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedByCyclotomicKernelEtalePhiSolutionMemWach
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedByCyclotomicKernel_etalePhi_solution_mem_wach : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) R.EE) (A' : Matrix (Fin q) (Fin q) R.EE) (Y : Matrix (Fin p) (Fin q) R.EE) (U : Matrix (Fin p) (Fin q) (RW LL)), IsUnit A → IsUnit A' → (∀ i j, FixH AI K (U i j)) → A.map I.ioE * U.map (φRW LL) = U * A'.map I.ioE + Y.map I.ioE → ∀ i j, U i j ∈ Set.range I.ioE := by
  first | exact @GlobalTheory.HWL.Rational.main | exact GlobalTheory.HWL.Rational.main | (intros; apply GlobalTheory.HWL.Rational.main <;> assumption)
