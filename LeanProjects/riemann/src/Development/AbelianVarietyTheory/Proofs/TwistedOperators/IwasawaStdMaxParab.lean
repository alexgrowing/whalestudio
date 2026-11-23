import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Formalism.JacquetSubsetSums.JacquetSubsetSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

noncomputable section

namespace GlobalTheory.MaxParabIwasawa

theorem iwasawa_stdMaxParab : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r a b : ℕ) (h : a + b = r) (g : GL (Fin r) k),
    (∃ κ ∈ KO k (Fin r), ∃ p ∈ stdMaxParab k h, g = κ * p) ∧
      ∃ p ∈ stdMaxParab k h, ∃ κ ∈ KO k (Fin r), g = p * κ := by
  intro k _ _ _ _ r a b h g
  have key : ∀ x : GL (Fin r) k, ∃ κ ∈ KO k (Fin r), ∃ p ∈ stdMaxParab k h, x = κ * p := by
    intro x
    obtain ⟨k₀, p, hp, hx⟩ := GlobalTheory.ValIwasawa.iwasawa 𝒪[k] k r x
    have hpP : p ∈ stdMaxParab k h := (mem_stdMaxParab h).2 fun i j hj hi =>
      hp (show j < i from by rw [Fin.lt_def]; omega)
    exact ⟨_, ⟨k₀, rfl⟩, p, hpP, hx⟩
  refine ⟨key g, ?_⟩
  obtain ⟨κ, hκ, p, hp, e⟩ := key g⁻¹
  refine ⟨p⁻¹, inv_mem hp, κ⁻¹, inv_mem hκ, ?_⟩
  rw [← mul_inv_rev, ← e, inv_inv]

end GlobalTheory.MaxParabIwasawa

example : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r a b : ℕ)
    (h : a + b = r) (g : GL (Fin r) k), (∃ κ ∈ KO k (Fin r), ∃ p ∈ stdMaxParab k h, g = κ * p) ∧
    ∃ p ∈ stdMaxParab k h, ∃ κ ∈ KO k (Fin r), g = p * κ := GlobalTheory.MaxParabIwasawa.iwasawa_stdMaxParab
