import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightMulLeOfIsCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightPositiveDiagonalLeSumAddInvStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGLIteratedDecayModerateGrowthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RapidDecaySmallestRatioAbsorbsHeightAndCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLUniformModerateGrowthStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem cuspForm_rapidDecay_siegel : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∀ t : ℝ, 0 < t → ∀ lam : Fin a → ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∏ i, r i = 1 → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * ∏ i, r i ^ lam i := by
  intro hP E _ _ _ a ψ hψ Ω hΩ t ht lam
  obtain ⟨N, hN⟩ := GlobalTheory.T.automorphicForm_GL_uniform_moderate_growth hP E a ψ hψ.1
  obtain ⟨m, C1, hC1, hreal⟩ := GlobalTheory.T.rapidDecay_smallestRatio_absorbs_height_and_character a t ht lam N
  obtain ⟨B, hB1, hB⟩ := GlobalTheory.T.exists_height_mul_le_of_isCompact E a Ω hΩ
  obtain ⟨C0, hC0⟩ := hN []
  simp only [List.map_nil, List.prod_nil, Module.End.one_apply] at hC0
  have hC0' : ∀ y, ‖ψ.1 (infGL E a y)‖ ≤ max C0 0 * height y ^ N := fun y =>
    (hC0 y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (by linarith [one_le_height y]) _))
  have hex : ∀ i j : Fin a, ∃ C : ℝ, 0 ≤ C ∧ ((j : ℕ) = i + 1 → ∀ (r : Fin a → ℝ)
      (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
      d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) →
      ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) ^ m * height d ^ N) := by
    intro i j
    by_cases hij : (j : ℕ) = i + 1
    · obtain ⟨C, hC, h⟩ := GlobalTheory.T.cuspForm_GL_iterated_decay_moderateGrowth hP E a N t ht i j hij m ψ hψ hN Ω hΩ
      exact ⟨C, hC, fun _ => h⟩
    · exact ⟨0, le_rfl, fun h => absurd h hij⟩
  choose Cf hCf0 hCf using hex
  have hS0 : 0 ≤ ∑ p : Fin a × Fin a, Cf p.1 p.2 := Finset.sum_nonneg fun p _ => hCf0 p.1 p.2
  have hK0 : 0 ≤ max C0 0 * B ^ N := mul_nonneg (le_max_right _ _) (pow_nonneg (by linarith) _)
  refine ⟨(max C0 0 * B ^ N + ∑ p : Fin a × Fin a, Cf p.1 p.2) * C1,
    mul_nonneg (add_nonneg hK0 hS0) hC1, ?_⟩
  intro r d hr hrt hd hprod c hc
  have hhd : height d ^ N ≤ (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N :=
    pow_le_pow_left₀ (by linarith [one_le_height d]) (GlobalTheory.T.height_positiveDiagonal_le_sum_add_inv E a r d hr hd) N
  have hP0 : 0 ≤ ∏ i, r i ^ lam i := Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hr i).le _
  have hsplit : (max C0 0 * B ^ N + ∑ p : Fin a × Fin a, Cf p.1 p.2) * C1 * ∏ i, r i ^ lam i
      = max C0 0 * B ^ N * (C1 * ∏ i, r i ^ lam i)
        + (∑ p : Fin a × Fin a, Cf p.1 p.2) * (C1 * ∏ i, r i ^ lam i) := by ring
  have hA := mul_nonneg hK0 (mul_nonneg hC1 hP0)
  have hB' := mul_nonneg hS0 (mul_nonneg hC1 hP0)
  rcases hreal r hr hrt hprod with h1 | ⟨i, j, hij, h2⟩
  · have hdc : height (d * c) ^ N ≤ (B * height d) ^ N :=
      pow_le_pow_left₀ (by linarith [one_le_height (d * c)]) (hB c hc d) N
    calc ‖ψ.1 (infGL E a (d * c))‖ ≤ max C0 0 * height (d * c) ^ N := hC0' _
      _ ≤ max C0 0 * (B * height d) ^ N := mul_le_mul_of_nonneg_left hdc (le_max_right _ _)
      _ = max C0 0 * B ^ N * height d ^ N := by rw [mul_pow]; ring
      _ ≤ max C0 0 * B ^ N * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N := mul_le_mul_of_nonneg_left hhd hK0
      _ ≤ max C0 0 * B ^ N * (C1 * ∏ i, r i ^ lam i) := mul_le_mul_of_nonneg_left h1 hK0
      _ ≤ _ := by rw [hsplit]; linarith
  · have hq : 0 ≤ (r j / r i) ^ m := pow_nonneg (div_nonneg (hr j).le (hr i).le) _
    have hle : Cf i j ≤ ∑ p : Fin a × Fin a, Cf p.1 p.2 :=
      Finset.single_le_sum (f := fun p : Fin a × Fin a => Cf p.1 p.2) (fun p _ => hCf0 p.1 p.2)
        (Finset.mem_univ (i, j))
    calc ‖ψ.1 (infGL E a (d * c))‖ ≤ Cf i j * (r j / r i) ^ m * height d ^ N :=
          hCf i j hij r d hr hrt hd c hc
      _ ≤ Cf i j * ((r j / r i) ^ m * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhd hq) (hCf0 i j)
      _ ≤ Cf i j * (C1 * ∏ i, r i ^ lam i) := mul_le_mul_of_nonneg_left h2 (hCf0 i j)
      _ ≤ (∑ p : Fin a × Fin a, Cf p.1 p.2) * (C1 * ∏ i, r i ^ lam i) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg hC1 hP0)
      _ ≤ _ := by rw [hsplit]; linarith

end GlobalTheory
