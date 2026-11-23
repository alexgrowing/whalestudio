import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiSubSubMemXiOfMonodromyEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_sub_sub_mem_xi_of_monodromy_eq : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, ∀ σ : Vec K a ι, D.conn σ = D.zeta y → ∃ d : D.D, D.phi σ - σ - D.phi y = D.xi d := by
  first | exact @GlobalTheory.BK.BKDat.phi_sub_sub_mem_xi | exact GlobalTheory.BK.BKDat.phi_sub_sub_mem_xi | (intros; apply GlobalTheory.BK.BKDat.phi_sub_sub_mem_xi <;> assumption)
