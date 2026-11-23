import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinXiExtMemRigidTensorIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (k : ℝ), 1 / ((e : ℝ) * l) < k → ∀ w : Vec K a ι, P.xiExt w ∈ P.Lk k ↔ w ∈ P.Mext (R O K l k) := by
  first | exact @GlobalTheory.BK.xiExt_mem_Lk_iff | exact GlobalTheory.BK.xiExt_mem_Lk_iff | (intros; apply GlobalTheory.BK.xiExt_mem_Lk_iff <;> assumption)
