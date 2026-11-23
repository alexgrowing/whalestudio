import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniqueIrreducibleSubLengthTwo
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unique_irreducible_sub_length_two : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ∃ S : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
        S.toRepresentation.IsIrreducible ∧
        (∀ S' : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)),
          S'.toRepresentation.IsIrreducible → S' = S) ∧
        Nonempty ((jac (GlobalTheory.Published.consecBlocks 2 d) S.toRepresentation).Equiv (piTensor (segTerm σ.ρ 2)))) →
  GlobalTheory.Published.SegmentRepresentation := by
  first | exact @GlobalTheory.CompanionTheory.SegZRep.segmentRepresentation_of_two | exact GlobalTheory.CompanionTheory.SegZRep.segmentRepresentation_of_two | (intros; apply GlobalTheory.CompanionTheory.SegZRep.segmentRepresentation_of_two <;> assumption)
