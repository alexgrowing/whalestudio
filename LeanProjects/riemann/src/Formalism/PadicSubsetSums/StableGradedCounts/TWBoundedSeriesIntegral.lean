import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.CentralIdempotentIntegral

open Filter Topology

namespace Formalism.IrreducibleCountingLemmas.TW

noncomputable def consEquiv (n : ℕ) : ℕ × (Fin n →₀ ℕ) ≃ (Fin (n + 1) →₀ ℕ) where
  toFun p := Finsupp.cons p.1 p.2
  invFun m := (m 0, Finsupp.tail m)
  left_inv p := by simp
  right_inv m := by simp

end Formalism.IrreducibleCountingLemmas.TW
