import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemBlockUpperUnipotentRadical
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockParOpp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPartMul
open MeasureTheory Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_mem_blockUpperUnipotentRadical : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b),
  ∀ p ∈ GlobalTheory.OrbDesc.blockPar (K := K) e, ∀ n ∈ GlobalTheory.OrbDesc.blockUni e, p * n * p⁻¹ ∈ GlobalTheory.OrbDesc.blockUni e := by
  first | exact @GlobalTheory.OrbDesc.blockUni_conj_mem | exact GlobalTheory.OrbDesc.blockUni_conj_mem | (intros; apply GlobalTheory.OrbDesc.blockUni_conj_mem <;> assumption)
