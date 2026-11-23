import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulConnectionSeriesTermMemLattice
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_smul_connection_series_term_mem_lattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (y₀ : Vec K a ι), 1 ≤ η → E K l e ^ η • y₀ ∈ D.M → ∀ n : ℕ, ∃ w ∈ D.MM, (l : K) ^ (H + 2 * η + n * (η - 1)) • (D.lphi ^ (n + 1)) (D.conn ((X : K⟦X⟧) ^ e • y₀)) = (X : K⟦X⟧) ^ (e * l ^ (n + 1)) • w := by
  first | exact @GlobalTheory.BK.lphi_pow_conn_X_pow_smul_mem | exact GlobalTheory.BK.lphi_pow_conn_X_pow_smul_mem | (intros; apply GlobalTheory.BK.lphi_pow_conn_X_pow_smul_mem <;> assumption)
