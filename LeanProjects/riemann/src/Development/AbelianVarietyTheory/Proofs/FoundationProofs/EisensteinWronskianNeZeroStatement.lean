import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinWronskianNeZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_wronskian_ne_zero : ∀ τ : ℍ, 2 * E₄ τ * deriv (⇑E₆ ∘ ofComplex) τ - 3 * E₆ τ * deriv (⇑E₄ ∘ ofComplex) τ ≠ 0 := by
  first | exact @GlobalTheory.EisWronskian.wronskian_E₄_E₆_ne_zero | exact GlobalTheory.EisWronskian.wronskian_E₄_E₆_ne_zero | (intros; apply GlobalTheory.EisWronskian.wronskian_E₄_E₆_ne_zero <;> assumption)
