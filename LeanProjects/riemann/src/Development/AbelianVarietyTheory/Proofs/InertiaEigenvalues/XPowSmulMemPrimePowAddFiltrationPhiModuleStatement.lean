import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XPowSmulMemPrimePowAddFiltrationPhiModule
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.X_pow_smul_mem_prime_pow_add_filtration_phiModule : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι), ∀ (j : ℕ), j ≤ l → ∀ w ∈ P.MM, ∃ s ∈ P.MM, ∃ f ∈ P.FilMM j, (X : K⟦X⟧) ^ (e * l) • w = (l : K) ^ (l - j) • s + f := by
  first | exact @GlobalTheory.BK.X_pow_smul_mem_l_pow_MM_add_FilMM | exact GlobalTheory.BK.X_pow_smul_mem_l_pow_MM_add_FilMM | (intros; apply GlobalTheory.BK.X_pow_smul_mem_l_pow_MM_add_FilMM <;> assumption)
