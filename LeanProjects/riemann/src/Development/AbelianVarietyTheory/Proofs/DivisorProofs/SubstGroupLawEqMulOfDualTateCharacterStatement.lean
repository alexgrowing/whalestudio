import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstGroupLawEqMulOfDualTateCharacter
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_groupLaw_eq_mul_of_dualTateCharacter : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O), (∀ n, c.ev n u = charElem χ n) → subst c.μ u = inL u * inR u := by
  first | exact @GlobalTheory.QLog.Chart.subst_μ_eq_inL_mul_inR | exact GlobalTheory.QLog.Chart.subst_μ_eq_inL_mul_inR | (intros; apply GlobalTheory.QLog.Chart.subst_μ_eq_inL_mul_inR <;> assumption)
