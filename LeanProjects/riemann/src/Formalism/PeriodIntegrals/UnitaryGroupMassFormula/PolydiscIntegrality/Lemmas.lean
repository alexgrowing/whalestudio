import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolydiscIntegrality.NormPPosLtOne

namespace PI.PolydiscIntegrality₂

open Filter Topology

variable {p : ℕ} [Fact p.Prime]

theorem norm_natCast_eq_one {N : ℕ} (h : ¬ p ∣ N) : ‖(N : ℂ_[p])‖ = 1 := by
  have h1 := PadicComplex.norm_extends' p (N : ℚ_[p])
  simp only [map_natCast, PadicComplex.coe_natCast] at h1
  rw [h1]
  exact Padic.norm_natCast_eq_one_iff.mpr (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr h)

end PI.PolydiscIntegrality₂
