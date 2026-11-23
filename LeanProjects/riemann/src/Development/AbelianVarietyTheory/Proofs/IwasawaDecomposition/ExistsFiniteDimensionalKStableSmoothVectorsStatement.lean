import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDimensionalKStableSmoothVectors
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteDimensional_kStable_smoothVectors : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → (∃ Λ S, IsKTypeOf ε σ Λ S) → ∃ W : Submodule ℂ H, FiniteDimensional ℂ W ∧ W ≠ ⊥ ∧ W ≤ smSub G (trRep σ P) ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∀ w ∈ W, σ k w ∈ W := by
  first | exact @GlobalTheory.SmVec.exists_finiteDimensional_kStable_smooth | exact GlobalTheory.SmVec.exists_finiteDimensional_kStable_smooth | (intros; apply GlobalTheory.SmVec.exists_finiteDimensional_kStable_smooth <;> assumption)
