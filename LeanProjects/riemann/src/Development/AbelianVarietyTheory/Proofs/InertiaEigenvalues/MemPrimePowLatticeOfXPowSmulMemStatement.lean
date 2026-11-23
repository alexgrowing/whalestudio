import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPrimePowLatticeOfXPowSmulMem
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiagScaleApply
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_prime_pow_lattice_of_X_pow_smul_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (P : PhiMod O K l e a ι) (n b : ℕ) (w z : Vec K a ι), w ∈ P.L → z ∈ P.L → ((X : K⟦X⟧) ^ e) ^ n • w = (l : K) ^ b • z → ∃ z' ∈ P.L, w = (l : K) ^ b • z' := by
  first | exact @GlobalTheory.CokerL.mem_lpow_L_of_vpow_smul | exact GlobalTheory.CokerL.mem_lpow_L_of_vpow_smul | (intros; apply GlobalTheory.CokerL.mem_lpow_L_of_vpow_smul <;> assumption)
