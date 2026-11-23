import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraFormalDegreeCompactDualLargeGaps
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
open Formalism.BasicNotions Formalism.MainNotions.S MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandra_formalDegree_compactDual_large_gaps : ∀ (cd : CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal),
    (∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
      (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
      ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
        ((sc n ε : ENNReal) • Formalism.REAL.muG ε) A =
          cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)}) →
    ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (h : ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      (∃ a, ε a = true) → (∃ a, ε a = false) → Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrE ε + 1 < h →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
        IsFdeg ((sc N ε : ENNReal) • Formalism.REAL.muG ε) σ (Formalism.QuantumDeterminants.fdegHC lam) := by
  first | exact @GlobalTheory.FdegGap.fdeg_gap | exact GlobalTheory.FdegGap.fdeg_gap | (intros; apply GlobalTheory.FdegGap.fdeg_gap <;> assumption)
