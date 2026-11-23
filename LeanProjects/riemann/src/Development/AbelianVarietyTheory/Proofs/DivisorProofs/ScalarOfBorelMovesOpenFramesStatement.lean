import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarOfBorelMovesOpenFrames
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_of_borel_moves_open_frames : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (m : GL (Fin r) E) (W : Set (Frame X.Ψ r)), IsOpen W → W.Nonempty → W ⊆ X.dom → (∀ x ∈ W, ∃ b ∈ Bor X.Ψ r, lact m x = rmul x b) → ∃ s : E, (m : Matrix (Fin r) (Fin r) E) = Matrix.scalar (Fin r) s := by
  first | exact @GlobalTheory.scalar_of_triangular_moves_open | exact GlobalTheory.scalar_of_triangular_moves_open | (intros; apply GlobalTheory.scalar_of_triangular_moves_open <;> assumption)
