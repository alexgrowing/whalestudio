import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiMemInvertedLattice
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_mem_invertedLattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ v ∈ D.MMl, D.phi v ∈ D.MMl := by
  first | exact @GlobalTheory.BK.BKDat.phi_mem_MMl | exact GlobalTheory.BK.BKDat.phi_mem_MMl | (intros; apply GlobalTheory.BK.BKDat.phi_mem_MMl <;> assumption)
