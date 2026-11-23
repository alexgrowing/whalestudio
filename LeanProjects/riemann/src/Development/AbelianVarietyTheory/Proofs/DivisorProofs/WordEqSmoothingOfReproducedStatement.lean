import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordEqSmoothingOfReproduced
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_test_word_eq_smoothing : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ φ : Sm E a, smoothing ν α φ.1 = φ.1 → ∀ l : List (Lie E a), ∃ β : Lie E a → ℂ, IsTest (invSet E a) β ∧ ((l.map (lie E a)).prod φ).1 = smoothing ν β φ.1 := by
  first | exact @GlobalTheory.AutGrowth.word_eq_smoothing_of_reproduced | exact GlobalTheory.AutGrowth.word_eq_smoothing_of_reproduced | (intros; apply GlobalTheory.AutGrowth.word_eq_smoothing_of_reproduced <;> assumption)
