import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.Val

theorem valuation_lt_one_of_tendsto_pow_zero :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      ∀ t : kˣ, Filter.Tendsto (fun n : ℕ => (t : k) ^ n) Filter.atTop (nhds 0) →
        ValuativeRel.valuation k (t : k) < 1 := by
  intro k _ _ _ _ t ht
  by_contra hge
  have hge' : 1 ≤ ValuativeRel.valuation k (t : k) := not_lt.mp hge
  have hU : {x : k | ValuativeRel.valuation k x < 1} ∈ nhds (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem one_ne_zero
  obtain ⟨n, hn⟩ := (ht.eventually hU).exists
  have hn' : ValuativeRel.valuation k ((t : k) ^ n) < 1 := hn
  rw [map_pow] at hn'
  exact absurd hn' (not_lt.mpr (one_le_pow₀ hge'))

end GlobalTheory.CompanionTheory.Val
