import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzExtensionFromSubspace
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_extension_from_subspace : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (P : Submodule ℝ Y),
    ∃ E : SchwartzMap P ℂ →L[ℂ] SchwartzMap Y ℂ, ∀ (φ : SchwartzMap P ℂ) (p : P), E φ (p : Y) = φ p := by
  first | exact @GlobalTheory.SchwartzExtend.extend_clm_of_submodule | exact GlobalTheory.SchwartzExtend.extend_clm_of_submodule | (intros; apply GlobalTheory.SchwartzExtend.extend_clm_of_submodule <;> assumption)
