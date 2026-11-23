import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueAddSmulMap
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasPAdicPowerSeriesValue_add_smul_map : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B) (f g : MvPowerSeries σ Q) (q r : Q), HasVal p z f q → (HasVal p z g r → HasVal p z (f + g) (q + r)) ∧ (∀ c : Q, HasVal p z (c • f) (c * q)) ∧ ∀ (B' Q' : Type) [CommRing B'] [CommRing Q'] [Algebra B' Q'] (ρ : B →+* B') (R : Q →+* Q'), (∀ b, R (algebraMap B Q b) = algebraMap B' Q' (ρ b)) → HasVal p (fun i => ρ (z i)) (map R f) (R q) := by
  first | exact @GlobalTheory.QLog.ValLin.hasVal_add_smul_map | exact GlobalTheory.QLog.ValLin.hasVal_add_smul_map | (intros; apply GlobalTheory.QLog.ValLin.hasVal_add_smul_map <;> assumption)
