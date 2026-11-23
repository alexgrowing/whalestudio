import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivPowerEnvelopeMemAinfAdjoinBeta
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divPowerEnvelope_mem_ainfAdjoinBeta : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) →
  ∀ a : Per.Acris0 l, (a : Per.AinfP l) ∈ Sa ϖ := by
  first | exact @GlobalTheory.Pst.StLat.acris0_le_sa | exact GlobalTheory.Pst.StLat.acris0_le_sa | (intros; apply GlobalTheory.Pst.StLat.acris0_le_sa <;> assumption)
