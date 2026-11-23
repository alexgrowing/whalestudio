import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsArtinianRingFibQuot
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
open GlobalTheory.PD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isArtinianRing_rB_quot_span_tco_of_isFinCover : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (F : Type) [Field F] [Algebra k F] [Algebra F K]
    [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    IsArtinianRing (rB k K x {0} ⧸ Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0}))) := by
  first | (exact @GlobalTheory.PD.isArtinianRing_fib_quot) | (exact GlobalTheory.PD.isArtinianRing_fib_quot) | (intros; apply GlobalTheory.PD.isArtinianRing_fib_quot  <;> assumption)
