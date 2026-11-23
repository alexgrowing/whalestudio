import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DSymmHypsInhabited
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFock

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def physFock (ε : Fin n → Bool) : Submodule ℂ (Fock n) :=
  ⨅ i : Fin n, ⨅ a : Fin n, ⨅ (_ : ¬ (ε i = true ∧ ε a = false)), LinearMap.ker (cmFock i a)

section
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

def khwSub (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ W) (γ : Fin n → ℝ) : Submodule ℂ W :=
  (⨅ a, LinearMap.ker (F a a - ((γ a : ℝ) : ℂ) • (1 : Module.End ℂ W))) ⊓
    ⨅ a, ⨅ b, ⨅ (_ : a < b ∧ ε a = ε b), LinearMap.ker (F a b)
end

end ReciprocityTheory.ChartRestriction.DS
