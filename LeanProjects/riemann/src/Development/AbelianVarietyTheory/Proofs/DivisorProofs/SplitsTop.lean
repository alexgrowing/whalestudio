import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.GroupBplus

namespace GlobalTheory.BplusDescent

variable {X : Scheme.{0}} [IsIntegral X]

def Splits (U : AffOp X) {h n : ℕ} (L : Submodule U.Bp (Fin h → U.Bp)) (g : Fin n → Fin h → U.Bp)
    (S : Fin n → Fin h → Kbar X) : Prop :=
  (∀ k, g k ∈ L) ∧ (∀ i i' : Fin h, ∑ k, (g k i : Kbar X) * S k i' = if i = i' then 1 else 0) ∧
    ∀ v ∈ L, ∀ k, ∃ r : U.Bp, (r : Kbar X) = ∑ i, S k i * (v i : Kbar X)

end GlobalTheory.BplusDescent
