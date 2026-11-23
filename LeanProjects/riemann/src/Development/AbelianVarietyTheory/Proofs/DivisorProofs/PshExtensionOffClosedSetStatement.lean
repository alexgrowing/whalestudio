import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PshExtensionOffClosedSet
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psh_extension_off_closed_set : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Om : LocPot X) (Z : Set X) (u : X → ℝ) (M : ℝ), 2 ≤ M → IsClosed Z → IsPotential A Om → IsPsh A Om → A.SmoothOn Zᶜ u → (∀ x ∈ Zᶜ, u x ≤ 0) → (∀ x j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (Om.U x ∩ Zᶜ), ∀ w : Fin e → ℂ, 0 ≤ levi ((fun z => Om.φ x z + u z) ∘ (A.chart j).symm) y w) → (∀ a : ℝ, closure {x | x ∈ Zᶜ ∧ -a ≤ u x} ⊆ Zᶜ) → ∃ (v : X → ℝ) (η : ℝ), A.Smooth v ∧ IsPsh A (Om + LocPot.ofFun v) ∧ (∀ x, -M ≤ v x ∧ v x ≤ 0) ∧ 0 ≤ η ∧ η ≤ 1 / 4 ∧ (∀ x ∈ Zᶜ, -M + 2 ≤ u x → v x = u x - η) ∧ ∀ x ∈ Zᶜ, u x - η ≤ v x := by
  first | exact @GlobalTheory.QuasiPshTruncation.exists_truncation | exact GlobalTheory.QuasiPshTruncation.exists_truncation | (intros; apply GlobalTheory.QuasiPshTruncation.exists_truncation <;> assumption)
