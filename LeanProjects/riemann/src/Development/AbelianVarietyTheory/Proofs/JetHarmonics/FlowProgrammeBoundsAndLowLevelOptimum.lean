import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MulFlowValLe
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DropLevelsBasic
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSums

open Formalism.IncomingBounds

namespace GlobalTheory.FlowProgrammeFacts

variable {l d : ℕ} [NeZero d]

lemma succ_mul_flowVal_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ}
    (hx : IsFlow l d D x) : ((l : ℝ) + 1) * flowVal d x ≤ ∑ a, D a := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : (l : ℝ) * flowVal d x ≤ ∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i := by
    unfold flowVal
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact absurd (Finset.mem_filter.1 hi).2 (by decide)
    exact mul_le_mul_of_nonneg_right (le_self_pow₀ hl1 hi0) (hx.1 a i)
  have h2 : ∑ a : ZMod d, ∑ i ∈ oddLevels d, x (a - (i : ZMod d)) i = flowVal d x := by
    unfold flowVal
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Equiv.sum_comp (Equiv.subRight (i : ZMod d)) (fun a => x a i)
  have h3 := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hx.2 a
  rw [Finset.sum_add_distrib, h2] at h3
  linarith

lemma rho_mul_le_Fnum (hl : 2 ≤ l) {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) :
    Formalism.IncomingBounds.rho l * ∑ a, D a ≤ Fnum l d D := by
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hp : (0 : ℝ) < (l : ℝ) + 1 := by linarith
  have hm : maxFlow l d D ≤ (∑ a, D a) / ((l : ℝ) + 1) :=
    GlobalTheory.FlowScaling.maxFlow_le hD fun x hx => by
      rw [le_div_iff₀ hp, mul_comm]
      exact succ_mul_flowVal_le (by omega) hx
  have hq : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have e : Formalism.IncomingBounds.gam l * ∑ a, D a - (∑ a, D a) / ((l : ℝ) + 1)
      = Formalism.IncomingBounds.rho l * ∑ a, D a := by
    unfold Formalism.IncomingBounds.gam Formalism.IncomingBounds.rho
    field_simp
    ring
  unfold Fnum
  linarith

theorem main : ∀ (l d : ℕ) [NeZero d] (D : ZMod d → ℝ), 2 ≤ l → (∀ a, 0 ≤ D a) →
    Formalism.IncomingBounds.rho l * ∑ a, D a ≤ Fnum l d D ∧
    (∀ t : ℝ, 0 ≤ t → Fnum l d (fun a => t * D a) = t * Fnum l d D) ∧
    Formalism.BasicNotions.lpF l d D = Fnum l d D ∧
    ∀ i₀ : ℕ, ∃ x : ZMod d → ℕ → ℝ, IsFlow l d D x ∧ (∀ a i, i₀ ≤ i → x a i = 0) ∧
      Formalism.IncomingBounds.gam l * ∑ a, D a - flowVal d x ≤
        Fnum l d D + ((l : ℝ) ^ i₀)⁻¹ * ∑ a, D a := by
  intro l d _ D hl hD
  refine ⟨rho_mul_le_Fnum hl hD, fun t ht => ?_, GlobalTheory.LevelsOrbits.lpF_eq l d D, fun i₀ => ?_⟩
  · unfold Fnum
    rw [GlobalTheory.FlowScaling.maxFlow_mul (by omega) ht hD, ← Finset.mul_sum]
    ring
  · obtain ⟨x, ⟨hx, hx0⟩, hmax⟩ := GlobalTheory.BasicFlow.low_optimum l d hl D hD i₀
    have hm : maxFlow l d D ≤ flowVal d x + (∑ a, D a) / (l : ℝ) ^ i₀ :=
      GlobalTheory.FlowScaling.maxFlow_le hD fun z hz => by
        obtain ⟨z', h1, h2, h3⟩ := GlobalTheory.BasicFlow.truncate l d hl D i₀ z hz
        linarith [hmax z' h1 h2]
    refine ⟨x, hx, fun a i h => hx0 a i (Or.inl h), ?_⟩
    rw [div_eq_inv_mul] at hm
    unfold Fnum
    linarith

end GlobalTheory.FlowProgrammeFacts
