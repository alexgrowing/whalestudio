import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_diag :
    ∀ (F : Filter ℕ), F ≤ atTop → ∀ P : ℕ → ℕ → Prop, (∀ j, ∀ᶠ N in F, P j N) →
      ∃ ν : ℕ → ℕ, Tendsto ν F atTop ∧ ∀ᶠ N in F, ∀ j ≤ ν N, P j N := by
  classical
  intro F hF P hP
  have hall : ∀ j, ∀ᶠ N in F, ∀ i ≤ j, P i N := fun j =>
    (Filter.eventually_all_finite (Set.finite_Iic j)).2 (fun i _ => hP i)
  refine ⟨fun N => Nat.findGreatest (fun j => ∀ i ≤ j, P i N) N, ?_, ?_⟩
  · rw [tendsto_atTop]
    intro j
    filter_upwards [hall j, hF (eventually_ge_atTop j)] with N h1 h2
    exact Nat.le_findGreatest (P := fun j => ∀ i ≤ j, P i N) h2 h1
  · filter_upwards [hall 0] with N h1
    exact Nat.findGreatest_spec (P := fun j => ∀ i ≤ j, P i N) (Nat.zero_le N) h1
