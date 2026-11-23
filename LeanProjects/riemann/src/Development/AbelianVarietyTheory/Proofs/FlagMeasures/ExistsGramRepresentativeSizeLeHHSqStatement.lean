import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGramRepresentativeSizeLeHHSq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gram_representative_size_le_HH_sq : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ (F0 : Fb D u) (Λ : LatV D), IsBase D u F0 → IsRowLat D F0 Λ → ∀ (Z : GramM D) (F' : FlagU D u'), RelZ D Z → IsTermF D Λ (lf D F0) F' → ZEquiv (ZhatL (lf D F0) F') Z → ∃ Z₁, ZEquiv Z Z₁ ∧ QOK D u u' Z₁ (HHZ D large₂.sc.b C Z ^ 2) := by
  first | exact @GlobalTheory.LoopC.GramSize.main | exact GlobalTheory.LoopC.GramSize.main | (intros; apply GlobalTheory.LoopC.GramSize.main <;> assumption)
