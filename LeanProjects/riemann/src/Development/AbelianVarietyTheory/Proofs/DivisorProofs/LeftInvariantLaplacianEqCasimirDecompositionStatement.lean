import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInvariantLaplacianEqCasimirDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftInvariantLaplacian_eq_casimir_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    lapOp E a = (2 : ℂ) • casKOp E a + ∑ τ : E →+* ℂ, (4 : ℂ) • Formalism.REAL.Cas (Eop (a := a) τ) := by
  first | exact @GlobalTheory.HCAlpha.lapOp_eq_casKOp_add_cas | exact GlobalTheory.HCAlpha.lapOp_eq_casKOp_add_cas | (intros; apply GlobalTheory.HCAlpha.lapOp_eq_casKOp_add_cas <;> assumption)
