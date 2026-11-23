import Formalism.SharpRestriction.LevelLetterCocycles.StmtLocFOfCountsAll
import Formalism.PeriodIntegrals.SqfRootsInj
import Formalism.PeriodIntegrals.SqfRootShift
import Formalism.PeriodIntegrals.SqfDivDeg
import Formalism.PeriodIntegrals.SqfPrimeFactor
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SqfRootsInj
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SqfRootShift
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SqfDivDeg
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PrimesDyadicRS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.SqfPrimeFactorOf

noncomputable section

namespace Formalism.MainNotions.N.LocalShareBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Polynomial

theorem counts_of_sqf (h3 : PI.SqfRootsInj.Claim) (h4 : PI.SqfRootShift.Claim)
    (h5 : PI.SqfDivDeg.Claim) (h6 : PI.SqfPrimeFactor.Claim) (D : D7) : Counts D := by
  intro hA hr k hg
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨hq, hd, hq8, hd16, -⟩ := D.host.hyp
  have ht : 1 ≤ D.R.t := D.R.t_odd.pos
  have hqb := D.host.qd_big
  have hq16 : 16 ≤ D.host.q := by nlinarith [hqb.1]
  have hd16' : 16 ≤ D.host.d := by nlinarith [hqb.2]
  have hcond : D.host.g k % (4 * 2 ^ D.R.e * D.host.q * D.host.d) = 1 := by
    have h0 : D.host.g k % (D.host.QS * D.host.q * D.host.d) = 1 := (hA k).2.2.2
    have hQ : 4 * 2 ^ D.R.e ∣ D.host.QS := by
      have h1 : 2 ^ (D.R.e + 2) ∣ D.host.QS := D.host.tower_dvd
      rwa [show 2 ^ (D.R.e + 2) = 4 * 2 ^ D.R.e by ring] at h1
    have hdv : 4 * 2 ^ D.R.e * D.host.q * D.host.d ∣ D.host.QS * D.host.q * D.host.d :=
      Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_right hQ _) _
    rw [← Nat.mod_mod_of_dvd _ hdv, h0]
    have hp : 1 ≤ 2 ^ D.R.e := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ D.R.e * D.host.q * D.host.d :=
      Nat.mul_pos (Nat.mul_pos hp hq.pos) hd.pos
    exact Nat.mod_eq_of_lt (by nlinarith)
  refine ⟨fun T hT => h3 _ _ hr hg T hT, fun c T hT => ?_, fun a ha1 ha2 T hT => h5 _ _ hr hg a ha1 ha2 T hT,
    fun T hT => h6 _ _ hr hg T hT⟩
  exact h4 (D.host.g k) D.R.r D.host.q D.host.d D.R.e hq hd hq8 hd16 D.host.two_le_e hq16 hd16' hcond hr hg c T hT

theorem counts_closed (D : D7) : Counts D :=
  counts_of_sqf squarefree_roots_injective squarefree_root_shift squarefree_div_degree
    (PI.SqfPrimeFactor.W.sqfPrimeFactor_of primes_dyadic_range) D

end Formalism.MainNotions.N.LocalShareBounds
