import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankAddValuationIntegerSubmoduleEqFinrankSpan
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_int0_submodule_eq_finrank_span : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (N : ℕ) (X : Submodule (Int0 v) (Fin N → Int0 v)), Module.Finite (Int0 v) X → finrank (Int0 v) X = finrank C (Submodule.span C ((fun (x : Fin N → Int0 v) (i : Fin N) => (x i : C)) '' (X : Set (Fin N → Int0 v)))) := by
  first | exact @GlobalTheory.finrank_addValuationInteger_submodule_eq_finrank_span | exact GlobalTheory.finrank_addValuationInteger_submodule_eq_finrank_span | (intros; apply GlobalTheory.finrank_addValuationInteger_submodule_eq_finrank_span <;> assumption)
