import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AcrisMemBetaAdicClosureAinfAdjoinBeta
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_mem_betaAdicClosure_ainfAdjoinBeta : ∀ (l : ℕ) [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l), IsCrisP j → ∀ (ϖ : Per.Fl l),
  (∀ a : Per.Acris0 l, (a : Per.AinfP l) ∈ Sa ϖ) → (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ x : Per.Acris l, j x ∈ Clos (Sg ϖ) (betaD ϖ) := by
  first | exact @GlobalTheory.Pst.StLat.acris_mem_clos | exact GlobalTheory.Pst.StLat.acris_mem_clos | (intros; apply GlobalTheory.Pst.StLat.acris_mem_clos <;> assumption)
