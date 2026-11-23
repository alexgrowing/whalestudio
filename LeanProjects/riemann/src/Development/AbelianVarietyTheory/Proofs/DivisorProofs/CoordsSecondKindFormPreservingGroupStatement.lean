import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsSecondKindFormPreservingGroup
import Mathlib
open Filter Topology Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordsSecondKind_formPreservingGroup : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ), ∃ (d : ℕ) (Z : Fin d → Matrix (Fin m) (Fin m) ℂ) (s : Matrix (Fin m) (Fin m) ℂ → Fin d → ℝ), (∀ i, (Z i)ᴴ * A + A * Z i = 0) ∧ Tendsto s (𝓝[{X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}] 1) (𝓝 0) ∧ ∀ᶠ X in 𝓝[{X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}] 1, X = (List.ofFn fun i => NormedSpace.exp (s X i • Z i)).prod := by
  first | exact @GlobalTheory.ClosedMatGroup.coords_second_kind_unitary | exact GlobalTheory.ClosedMatGroup.coords_second_kind_unitary | (intros; apply GlobalTheory.ClosedMatGroup.coords_second_kind_unitary <;> assumption)
