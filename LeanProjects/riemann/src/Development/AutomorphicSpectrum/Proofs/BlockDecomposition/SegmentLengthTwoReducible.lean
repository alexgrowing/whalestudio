import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FalseOfOpenParts
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.BZReducible

theorem cusp_times_nu_reducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), 0 < d →
    ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ¬ (multiProd (GlobalTheory.Published.consecBlocks 2 d) (segTerm σ.ρ 2)).IsIrreducible :=
  fun k _ _ _ _ d hd σ hσ => GlobalTheory.CompanionTheory.BZShell.red_cusp_nu k d hd σ hσ

end GlobalTheory.CompanionTheory.BZReducible
