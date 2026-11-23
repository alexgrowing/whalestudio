import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowPrimesConductor
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_host_degree_and_log_q_and_conductor_bounds : SzRow (fun C D L => (L.sc.x ^ (2 * L.Ct + 5) < (D.host.q : ℝ) ∧ L.sc.x ^ (2 * L.Ct + 5) < (D.host.d : ℝ)) ∧ (L.sc.x ^ (L.sc.ez / 6) ≤ Real.log D.host.q) ∧ (|L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps) ∧ ((condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 ≤ L.sc.b ^ ((1 : ℝ) / 2)) ∧ (Real.log D.host.pde ≤ L.sc.L ∧ Real.log D.host.pde' ≤ L.sc.L)) := by
  first | exact @GlobalTheory.EX.szRow_primes_conductor | exact GlobalTheory.EX.szRow_primes_conductor | (intros; apply GlobalTheory.EX.szRow_primes_conductor <;> assumption)
