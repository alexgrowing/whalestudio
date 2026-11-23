import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEisensteinPowSmulMonodromyMemBreuilKisin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eisensteinPow_smul_monodromy_mem_breuilKisin : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι), ∃ n : ℕ, ∀ m ∈ P.M, E K l e ^ n • P.EN m ∈ P.Man := by
  first | exact @GlobalTheory.BK.exists_pow_E_smul_EN_mem_Man | exact GlobalTheory.BK.exists_pow_E_smul_EN_mem_Man | (intros; apply GlobalTheory.BK.exists_pow_E_smul_EN_mem_Man <;> assumption)
