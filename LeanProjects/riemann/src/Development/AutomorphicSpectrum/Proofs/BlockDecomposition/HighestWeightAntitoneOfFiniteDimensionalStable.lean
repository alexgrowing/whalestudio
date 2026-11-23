import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents.HighestWeightDifferencesNat

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount

theorem highestWeight_antitone_of_finiteDimensional_stable :
    ∀ {n : ℕ} (V : Type) [AddCommGroup V] [Module ℂ V] (Kf : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V)
    (ν : Fin n → ℝ) (v : V), Formalism.REAL.GlRel Kf → FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, Kf a b w ∈ S) → v ∈ S → v ≠ 0 →
    Formalism.REAL.KHighest (fun _ => true) Kf ν v → Antitone ν := by
  intro n V _ _ Kf S ν v hG hfd hS hv hv0 hK a b hab
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.DS.HW.exists_nat_weight_sub_eq_of_highest_vector_in_stable (ε := fun _ => true) (F := Kf)
      (Formalism.REAL.glRel_kRel (fun _ => true) Kf hG) (ne_of_lt hlt) rfl S (fun y hy => hS b a y hy)
      hv hv0 (hK.1 a) (hK.1 b) (hK.2 a b hlt rfl)
    have hm' : ν a - ν b = (m : ℝ) := by
      apply Complex.ofReal_injective
      push_cast
      exact hm
    have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith

end GlobalTheory.CompanionTheory.RealCount
