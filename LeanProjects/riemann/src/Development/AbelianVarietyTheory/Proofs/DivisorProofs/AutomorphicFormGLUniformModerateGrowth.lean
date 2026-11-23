import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormEqOwnRealLieSmoothingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingGrowthExponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordEqSmoothingOfReproducedStatement

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem GlobalTheory.AutGrowth.uniform_growth_of_autForm : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E]
    [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∃ N : ℕ, ∀ l : List (Lie E a),
    ∃ C : ℝ, ∀ y, ‖((l.map (lie E a)).prod φ).1 (infGL E a y)‖ ≤ C * height y ^ N := by
  intro hP E _ _ _ a φ hφ
  let ν : Measure (Lie E a) := Measure.addHaar
  obtain ⟨C, N, hC⟩ := hφ.growth 1
  simp only [one_mul] at hC
  obtain ⟨α, hα, hconv⟩ := GlobalTheory.T.automorphicForm_eq_own_realLieSmoothing hP E a ν φ hφ
  refine ⟨N, fun l => ?_⟩
  obtain ⟨β, hβ, hw⟩ := GlobalTheory.T.exists_test_word_eq_smoothing E a ν α hα φ hconv l
  obtain ⟨C', hC'⟩ := GlobalTheory.T.exists_smoothing_norm_le_height_pow E a ν β hβ φ.1 C N hC
  exact ⟨C', fun y => by rw [hw]; exact hC' y⟩
