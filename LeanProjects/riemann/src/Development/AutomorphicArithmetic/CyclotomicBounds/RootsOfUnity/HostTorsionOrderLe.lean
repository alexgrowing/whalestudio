import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.Monomial

open NumberField Formalism.BasicNotions

namespace UpperTheory.Mu

theorem host_torsionOrder_le {R : Ranks} (H : Host R) : Units.torsionOrder H.E ≤ 8 * R.f ^ 2 := by
  have h := torsionOrder_le H.E
  rw [H.finrank_cmField] at h
  have hn : R.f = 2 * R.ord := rfl
  rw [hn]
  calc Units.torsionOrder H.E ≤ 2 * (4 * R.ord) ^ 2 := h
    _ = 8 * (2 * R.ord) ^ 2 := by ring

theorem one_le_f (R : Ranks) : 1 ≤ R.f := by
  have h := R.ord_pos
  show 1 ≤ 2 * R.ord
  omega

end UpperTheory.Mu
