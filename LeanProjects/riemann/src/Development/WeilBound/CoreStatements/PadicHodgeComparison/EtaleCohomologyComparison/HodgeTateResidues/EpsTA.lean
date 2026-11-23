import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInFamily
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.ExistsEpsPeriodTUnit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

variable (l : ℕ) [Fact l.Prime]

theorem eps_tA : ∃ (ε : B.Eps l) (u : Acris l), tA l = ε.μ * u := by
  obtain ⟨u, hu, e⟩ := ACris.exists_periodT_eq_mu_mul_unit (K := ℂ_[l]) (p := l) (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one
  exact ⟨GlueBE.eps l, u, by rw [GlueBE.eps_μ]; exact e⟩

theorem tFil : TFil l := fun A n =>
  (eps_tA l).elim fun ε h => h.elim fun u hu => by
    rw [hu, map_mul]
    exact Ideal.mul_mem_right _ _ (ε.μ_mem false A n)

end CrystallineSemistableComparison.HT
