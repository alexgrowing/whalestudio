import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolydiscIntegrality.NormPPosLtOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolydiscIntegrality.Lemmas

namespace PI.PolydiscIntegrality₂

open Filter Topology

variable {p : ℕ} [Fact p.Prime]

theorem exists_coord_bound {n : ℕ} (S : Finset (Fin n →₀ ℕ)) :
    ∃ B : ℕ, ∀ γ ∈ S, ∀ i, γ i ≤ B := by
  refine ⟨∑ γ ∈ S, ∑ i, γ i, fun γ hγ i => ?_⟩
  calc γ i ≤ ∑ i, γ i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ ≤ ∑ γ ∈ S, ∑ i, γ i := Finset.single_le_sum (f := fun γ : Fin n →₀ ℕ => ∑ i, γ i)
        (fun _ _ => Nat.zero_le _) hγ

end PI.PolydiscIntegrality₂
