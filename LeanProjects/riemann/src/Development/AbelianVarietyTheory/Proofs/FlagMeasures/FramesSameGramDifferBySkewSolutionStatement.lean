import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesSameGramDifferBySkewSolution
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_same_gram_differ_by_skew_solution : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ (P : LatW D) (φ : P →ₗ[𝓞 D.host.E] (hS D).V) (Z : GramM D), (∀ p, φ p ∈ XLam Λ (lf D F0)) → ∀ F₁ ∈ FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ, ∀ F₂ ∈ FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ, (∀ b, ∃ w, IsWcomp D P (frame F₁ b) w ∧ IsWcomp D P (frame F₂ b) w) → ∃ x : Matrix (Fin D.R.rS) (Fin (D.R.rS + 1)) D.host.E, (∀ b, frame F₂ b = frame F₁ b + ∑ a, x a b • F0.e a) ∧ (∀ a b, x a b ∈ (ddS D ^ (-(D.R.rS : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧ xᴴ * Z.submatrix Fin.castSucc id + (Z.submatrix Fin.castSucc id)ᴴ * x = 0 := by
  first | exact @GlobalTheory.LoopC.FrameDiff.frame_diff | exact GlobalTheory.LoopC.FrameDiff.frame_diff | (intros; apply GlobalTheory.LoopC.FrameDiff.frame_diff <;> assumption)
