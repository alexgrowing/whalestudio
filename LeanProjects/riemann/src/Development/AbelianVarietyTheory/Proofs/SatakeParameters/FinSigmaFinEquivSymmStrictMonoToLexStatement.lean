import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinSigmaFinEquivSymmStrictMonoToLex
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finSigmaFinEquiv_symm_strictMono_toLex : ∀ (s : ℕ) (t : Fin s → ℕ), StrictMono fun c : Fin (∑ a, t a) => (toLex (finSigmaFinEquiv.symm c) : Σₗ a, Fin (t a)) := by
  first | exact @GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex | exact GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex | (intros; apply GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex <;> assumption)
