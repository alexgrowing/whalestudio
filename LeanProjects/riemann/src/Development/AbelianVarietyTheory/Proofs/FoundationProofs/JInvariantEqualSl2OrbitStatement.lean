import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JInvariantEqualSl2Orbit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.j_invariant_equal_sl2_orbit : ∀ τ σ : ℍ, E₄ τ ^ 3 * E₆ σ ^ 2 = E₆ τ ^ 2 * E₄ σ ^ 3 → ∃ γ : SL(2, ℤ), τ = γ • σ := by
  first | exact @GlobalTheory.JOrbit.exists_smul_of_E₄_E₆ | exact GlobalTheory.JOrbit.exists_smul_of_E₄_E₆ | (intros; apply GlobalTheory.JOrbit.exists_smul_of_E₄_E₆ <;> assumption)
