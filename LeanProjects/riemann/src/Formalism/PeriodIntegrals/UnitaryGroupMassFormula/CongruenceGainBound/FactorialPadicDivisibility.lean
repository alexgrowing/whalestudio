import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CongruenceGainBound.Development

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound

def PDiv (p n : ℕ) (r : ℝ) : Prop := ∃ V : ℕ, p ^ V ∣ n ∧ r ≤ V

theorem PDiv.mono {p n : ℕ} {r r' : ℝ} (h : PDiv p n r) (hr : r' ≤ r) : PDiv p n r' := by
  obtain ⟨V, h1, h2⟩ := h
  exact ⟨V, h1, hr.trans h2⟩

end PI.UnitaryGroupMassFormula.PadicGainBound
