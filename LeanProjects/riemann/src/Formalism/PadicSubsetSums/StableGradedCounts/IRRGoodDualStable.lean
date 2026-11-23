import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

section
variable {K : Type} [Field K]

theorem rev_natDegree {h : K[X]} (h0 : h.coeff 0 ≠ 0) : h.reverse.natDegree = h.natDegree := by
  rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr h0), Nat.sub_zero]

theorem rev_rev {h : K[X]} (h0 : h.coeff 0 ≠ 0) : h.reverse.reverse = h := by
  ext n
  rw [coeff_reverse, coeff_reverse, rev_natDegree h0, revAt_invol]

variable {L : Type} [Field L] [Algebra K L]

end

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
