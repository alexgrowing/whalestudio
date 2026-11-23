import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DenseKFiniteVectorsUnitaryGroupRep
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactUnitaryFiniteInvariantSubspace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_kFinite_vectors_unitaryGroupRep : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ → Dense {v : H | Formalism.MainNotions.S.IsKFin ε σ v} := by
  first | exact @GlobalTheory.CompactRep.dense_isKFin | exact GlobalTheory.CompactRep.dense_isKFin | (intros; apply GlobalTheory.CompactRep.dense_isKFin <;> assumption)
