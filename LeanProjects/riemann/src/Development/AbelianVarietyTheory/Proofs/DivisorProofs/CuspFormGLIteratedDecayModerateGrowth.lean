import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightMulLeOfIsCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFormOperatorActStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGLSiegelConeDecayOneStepStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CuspRapid

theorem iterated_decay : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (N : ℕ) (t : ℝ), 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (m : ℕ) (ψ : Sm E a), IsCuspForm ψ → (∀ l : List (Lie E a), ∃ C : ℝ, ∀ y, ‖((l.map (lie E a)).prod ψ).1 (infGL E a y)‖ ≤ C * height y ^ N) → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) ^ m * height d ^ N := by
  intro hfin E _ _ _ a N t ht i j hij m
  induction m with
  | zero =>
    intro ψ _ htame Ω hΩ
    obtain ⟨C0, hC0⟩ := htame []
    obtain ⟨B, hB1, hB⟩ := GlobalTheory.T.exists_height_mul_le_of_isCompact E a Ω hΩ
    refine ⟨|C0| * B ^ N, by positivity, ?_⟩
    intro r d _ _ _ c hc
    have h1 := hC0 (d * c)
    simp only [List.map_nil, List.prod_nil, Module.End.one_apply] at h1
    have hh0 : 0 ≤ height (d * c) := le_trans zero_le_one (one_le_height _)
    have hh : height (d * c) ^ N ≤ (B * height d) ^ N := pow_le_pow_left₀ hh0 (hB c hc d) N
    calc ‖ψ.1 (infGL E a (d * c))‖ ≤ C0 * height (d * c) ^ N := h1
      _ ≤ |C0| * height (d * c) ^ N := mul_le_mul_of_nonneg_right (le_abs_self C0) (pow_nonneg hh0 N)
      _ ≤ |C0| * (B * height d) ^ N := mul_le_mul_of_nonneg_left hh (abs_nonneg C0)
      _ = |C0| * B ^ N * (r j / r i) ^ 0 * height d ^ N := by rw [mul_pow]; ring
  | succ m ih =>
    intro ψ hψ htame Ω hΩ
    obtain ⟨Ω', B, C, hΩ', hC, hstep⟩ := GlobalTheory.T.cuspForm_GL_siegel_cone_decay_one_step E a ψ hψ t ht i j hij Ω hΩ
    have hY : ∀ Y ∈ B, ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) →
        (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) →
        ∀ c ∈ Ω', ‖(lie E a Y ψ).1 (infGL E a (d * c))‖ ≤ C' * (r j / r i) ^ m * height d ^ N := by
      intro Y _
      have hcusp : IsCuspForm (lie E a Y ψ) := GlobalTheory.T.isCuspForm_operator_act hfin E a (.lie Y) ψ hψ
      refine ih (lie E a Y ψ) hcusp ?_ Ω' hΩ'
      intro l
      obtain ⟨C1, hC1⟩ := htame (l ++ [Y])
      refine ⟨C1, fun y => ?_⟩
      have e : (l.map (lie E a)).prod (lie E a Y ψ) = ((l ++ [Y]).map (lie E a)).prod ψ := by
        simp [List.map_append, List.prod_append, Module.End.mul_apply]
      rw [e]
      exact hC1 y
    choose! CY hCY0 hCY using hY
    refine ⟨C * ∑ Y ∈ B, CY Y, mul_nonneg hC (Finset.sum_nonneg hCY0), ?_⟩
    intro r d hr hrt hd c hc
    have hq : 0 ≤ (r j / r i) ^ m * height d ^ N :=
      mul_nonneg (pow_nonneg (div_nonneg (hr j).le (hr i).le) m)
        (pow_nonneg (le_trans zero_le_one (one_le_height d)) N)
    have hM0 : 0 ≤ (∑ Y ∈ B, CY Y) * ((r j / r i) ^ m * height d ^ N) :=
      mul_nonneg (Finset.sum_nonneg hCY0) hq
    have h := hstep r d hr hrt hd _ hM0 (fun Y hYB c' hc' => by
      have h2 : lieD Y ψ.1 = (lie E a Y ψ).1 := rfl
      rw [h2]
      calc ‖(lie E a Y ψ).1 (infGL E a (d * c'))‖ ≤ CY Y * (r j / r i) ^ m * height d ^ N := hCY Y hYB r d hr hrt hd c' hc'
        _ = CY Y * ((r j / r i) ^ m * height d ^ N) := by ring
        _ ≤ (∑ Y ∈ B, CY Y) * ((r j / r i) ^ m * height d ^ N) :=
          mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun Y hY => hCY0 Y hY) hYB) hq) c hc
    calc ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) * ((∑ Y ∈ B, CY Y) * ((r j / r i) ^ m * height d ^ N)) := h
      _ = (C * ∑ Y ∈ B, CY Y) * (r j / r i) ^ (m + 1) * height d ^ N := by ring

end GlobalTheory.CuspRapid
