import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KillsTranslatesSumMulMeanDifferenceEqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableRegularizedEisensteinLatticeTermStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem dif_comm (L : ℕ) (v w : ℤ × ℤ) (F : ℤ × ℤ → ℂ) :
    dif L v (dif L w F) = dif L w (dif L v F) := by
  funext x
  simp only [dif]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h : ∑ s ∈ Finset.range L, ∑ r ∈ Finset.range L, F (x + (s : ℤ) • v + (r : ℤ) • w)
      = ∑ r ∈ Finset.range L, ∑ s ∈ Finset.range L, F (x + (r : ℤ) • w + (s : ℤ) • v) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    rw [add_right_comm]
  rw [h]
  ring

theorem sum_dif_dif (L : ℕ) (w : ℤ × ℤ) (Φ G : ℤ × ℤ → ℂ) (hL : 0 < L) (hΦ : ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C)
    (hw : Kills L w Φ) (hG : Summable fun x => ‖G x‖) :
    ∑' x, Φ x * dif L w (dif L w G) x = ∑' x, Φ x * G x := by
  obtain ⟨hs1, he1⟩ := GlobalTheory.T.killsTranslates_sum_mul_meanDifference_eq L w Φ G hL hΦ hw hG
  obtain ⟨_, he2⟩ := GlobalTheory.T.killsTranslates_sum_mul_meanDifference_eq L w Φ (dif L w G) hL hΦ hw hs1
  exact he2.trans he1

theorem lat_indep : ∀ (j L : ℕ) (v w : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ), 1 ≤ j → 0 < L →
    (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Kills L v Φ → Kills L w Φ → lat j 0 L v Φ τ = lat j 0 L w Φ τ := by
  intro j L v w Φ τ hj hL hΦ hv hw
  set T : ℤ × ℤ → ℂ := fun y => trm j 0 ((y.1 : ℂ) * τ + y.2) with hT
  have hsv := GlobalTheory.T.summable_regularizedEisensteinLatticeTerm j L v τ hj hL
  have hsw := GlobalTheory.T.summable_regularizedEisensteinLatticeTerm j L w τ hj hL
  simp only [lat]
  calc ∑' x, Φ x * dif L v (dif L v T) x
      = ∑' x, Φ x * dif L w (dif L w (dif L v (dif L v T))) x :=
        (sum_dif_dif L w Φ _ hL hΦ hw hsv).symm
    _ = ∑' x, Φ x * dif L v (dif L v (dif L w (dif L w T))) x := by
        have c1 : ∀ F : ℤ × ℤ → ℂ, dif L w (dif L v (dif L v F)) = dif L v (dif L v (dif L w F)) := by
          intro F; rw [dif_comm L w v (dif L v F), dif_comm L w v F]
        rw [c1 T, c1 (dif L w T)]
    _ = ∑' x, Φ x * dif L w (dif L w T) x := sum_dif_dif L v Φ _ hL hΦ hv hsw

end GlobalTheory.EisM
