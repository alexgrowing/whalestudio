import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricPositionCharMultiplicityParabolicInduct
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPositionCharMultiplicity_parabolicInduction : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ ρ k : ℕ, ρ + k + 1 ≤ r → nPos ψ (parInd b σ) ρ k = ∑ j ∈ Finset.range (k + 1), splitDoublingNBlock b j * gam (Fintype.card F) (k - j) := by
  first | exact @GlobalTheory.FinGL.nPos_parInd | exact GlobalTheory.FinGL.nPos_parInd | (intros; apply GlobalTheory.FinGL.nPos_parInd <;> assumption)
