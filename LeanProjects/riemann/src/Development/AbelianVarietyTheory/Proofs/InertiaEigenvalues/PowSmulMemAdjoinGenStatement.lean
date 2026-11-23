import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulMemAdjoinGen
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_mem_adjoin_gen_of_separable : ∀ (K : UQ) (B : InvAlg K) (a : K.O), B.P.Separable → K.Small a → ∃ N : ℕ, ∀ r : B.A, IsIntegral K.O r → (al K a ^ N) • r ∈ Algebra.adjoin K.O {B.g} := by
  first | exact @GlobalTheory.UnitLemma.Desc.pow_smul_mem_adjoin_gen | exact GlobalTheory.UnitLemma.Desc.pow_smul_mem_adjoin_gen | (intros; apply GlobalTheory.UnitLemma.Desc.pow_smul_mem_adjoin_gen <;> assumption)
