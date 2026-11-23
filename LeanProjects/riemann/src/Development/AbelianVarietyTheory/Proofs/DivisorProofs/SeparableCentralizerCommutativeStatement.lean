import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableCentralizerCommutative
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
open Matrix GlobalTheory.LKRes
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separable_centralizer_commutative : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r →
    ∀ N : GL (Fin n) (GlobalTheory.LKRes.KQ p K r), N.val.charpoly.Separable →
    ∀ a ∈ Subgroup.centralizer {N}, ∀ b ∈ Subgroup.centralizer {N}, a * b = b * a := by
  first | (exact @GlobalTheory.LKRes.CentComm.centralizer_comm) | (exact GlobalTheory.LKRes.CentComm.centralizer_comm) | (intros; apply GlobalTheory.LKRes.CentComm.centralizer_comm  <;> assumption)
