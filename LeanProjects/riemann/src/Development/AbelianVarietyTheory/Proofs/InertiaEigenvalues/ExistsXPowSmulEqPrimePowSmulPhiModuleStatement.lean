import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsXPowSmulEqPrimePowSmulPhiModule
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_X_pow_smul_eq_prime_pow_smul_phiModule : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι), ∀ (n : ℕ), ∀ w ∈ P.MM, ∃ w' ∈ P.MM, (X : K⟦X⟧) ^ (e * l ^ (n + 1)) • w = (l : K) ^ (l ^ n) • w' := by
  first | exact @GlobalTheory.BK.PhiMod.exists_X_pow_smul_eq_l_pow_smul | exact GlobalTheory.BK.PhiMod.exists_X_pow_smul_eq_l_pow_smul | (intros; apply GlobalTheory.BK.PhiMod.exists_X_pow_smul_eq_l_pow_smul <;> assumption)
