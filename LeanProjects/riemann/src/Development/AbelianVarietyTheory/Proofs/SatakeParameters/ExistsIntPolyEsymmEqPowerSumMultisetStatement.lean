import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntPolyEsymmEqPowerSumMultiset
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
open GlobalTheory.Cong
theorem _root_.GlobalTheory.T.exists_intPoly_esymm_eq_powerSum_multiset : ∀ a n : ℕ, 1 ≤ n → ∃ P : MvPolynomial (Fin (a + 1)) ℤ, ∀ s : Multiset ℂ, Multiset.card s = a → MvPolynomial.aeval (fun j : Fin (a + 1) => s.esymm j) P = (s.map (· ^ n)).sum := by
  first | exact @GlobalTheory.PowerSumPoly.exists_intPoly_psum_eq | exact GlobalTheory.PowerSumPoly.exists_intPoly_psum_eq | (intros; apply GlobalTheory.PowerSumPoly.exists_intPoly_psum_eq <;> assumption)
