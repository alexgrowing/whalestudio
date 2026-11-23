import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEigenFiltrationPiecesAddValInt
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_eigenFiltration_pieces_addValInt : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, Module.Finite (Int0 v) (Fil.restrictScalars (Int0 v)) ∧ Module.Finite (Int0 v) (preEig a Fil τ) ∧ Module.Finite (Int0 v) (filKer a Fil τ) ∧ Module.Finite (Int0 v) (eigSub a τ (Fin N → RS a)) ∧ Module.Finite (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)) ∧ Module.Finite (Int0 v) (eigSub a τ Fil) ∧ Module.Finite (Int0 v) (kerMul a (cofac a τ) Fil) := by
  first | exact @GlobalTheory.HerbFin.finite_main | exact GlobalTheory.HerbFin.finite_main | (intros; apply GlobalTheory.HerbFin.finite_main <;> assumption)
