import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.RowsConc
namespace GlobalTheory.Core.Diag

def DiagSmall : Prop :=
  ∀ δ Cg cb Cu cT CT C0 : ℝ, 0 < δ → 0 < cb → 0 < cT → 1 ≤ C0 → ∃ CG₀ : ℝ, ∀ CG : ℝ, CG₀ ≤ CG →
    ∃ thr : ℝ, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (L : ℝ), TrueS D → TFrameAt D → HasLed D L CG → GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT → StandingNumericalData D C0 →
      ∀ u, GlobalTheory.Core.Rk.DiagS D u δ
end GlobalTheory.Core.Diag
