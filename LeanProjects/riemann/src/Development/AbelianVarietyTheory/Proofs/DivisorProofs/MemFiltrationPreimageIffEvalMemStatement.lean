import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiltrationPreimageIffEvalMem
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAddValuationIntegerRingNormalizedIff
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_filtrationPreimage_iff_eval_mem : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C)), (∀ x ∈ F, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.unif a x ∈ F) → ∀ x, x ∈ filPre (liftA hv a) F ↔ evalVec (liftA hv a) N x ∈ F := by
  first | exact @GlobalTheory.FilPreMem.filPre_mem_iff | exact GlobalTheory.FilPreMem.filPre_mem_iff | (intros; apply GlobalTheory.FilPreMem.filPre_mem_iff <;> assumption)
