import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupChartLevelOneNilpotentModP
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pDivGroupChart_level_one_nilpotent_mod_p : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∃ N : ℕ, ∀ f : MvPowerSeries (Fin d) O, constantCoeff f = 0 → (p : G.A 1) ∣ c.ev 1 f ^ N := by
  first | exact @GlobalTheory.AugNil.aug_nil | exact GlobalTheory.AugNil.aug_nil | (intros; apply GlobalTheory.AugNil.aug_nil <;> assumption)
