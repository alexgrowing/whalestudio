import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory.BrPairF

variable {K ι : Type} [Field K] [Fintype ι] {n N : ℕ}

def brPairF (σ : ι → DomWeight n) (hN : N = n + 1) (Λ : ι → DomWeight N) :
    VV K Λ →ₗ[K] (VV K fun τ => (σ τ).dual) →ₗ[K] K :=
  (pairBK σ).compl₁₂ (Formalism.L2.Col.Br.brStd hN Λ σ) (GlobalTheory.FunObj.funEquiv σ).symm.toLinearMap

theorem brPairF_apply (σ : ι → DomWeight n) (hN : N = n + 1) (Λ : ι → DomWeight N) (u : VV K Λ)
    (v : VV K fun τ => (σ τ).dual) :
    brPairF σ hN Λ u v = pairBK σ (Formalism.L2.Col.Br.brStd hN Λ σ u) ((GlobalTheory.FunObj.funEquiv σ).symm v) := rfl

end GlobalTheory.BrPairF

end
