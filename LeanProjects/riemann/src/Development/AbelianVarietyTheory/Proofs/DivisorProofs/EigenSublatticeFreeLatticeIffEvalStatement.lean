import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenSublatticeFreeLatticeIffEval
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAddValuationIntegerRingNormalizedIff
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenSublattice_freeLattice_iff_eval : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (τ : S), Function.Injective a → Function.Injective (evalVec (liftA hv a) N) → (∀ y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y) → ∀ y : Fin N → C, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin N → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) τ ↔ ∃ z ∈ eigSub (liftA hv a) τ (Fin N → RS (liftA hv a)), (fun i => ((comp (liftA hv a) N τ z i : Int0 v) : C)) = y := by
  first | exact @GlobalTheory.EigenSubEval.eigenSub_iff_eval | exact GlobalTheory.EigenSubEval.eigenSub_iff_eval | (intros; apply GlobalTheory.EigenSubEval.eigenSub_iff_eval <;> assumption)
