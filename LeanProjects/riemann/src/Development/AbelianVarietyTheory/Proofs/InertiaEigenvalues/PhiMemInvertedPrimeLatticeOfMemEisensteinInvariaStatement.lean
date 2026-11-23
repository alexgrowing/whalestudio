import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiMemInvertedPrimeLatticeOfMemEisensteinInvaria
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_mem_invertedPrime_lattice_of_mem_eisensteinInvariants : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, D.phi y ∈ D.MMl := by
  first | exact @GlobalTheory.BK.phi_mem_MMl_of_mem_Y | exact GlobalTheory.BK.phi_mem_MMl_of_mem_Y | (intros; apply GlobalTheory.BK.phi_mem_MMl_of_mem_Y <;> assumption)
