import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PartnerPlaceInvolutiveNormConjEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partnerPlace_involutive_norm_conj_eq : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p = D.host.d → ∀ (τ : D.what₂.Tau), tauSg D (tauSg D τ) = τ ∧ tauSg D τ ≠ τ ∧ ∀ y : D.host.E, ‖tauEmb D lam (tauSg D τ) (D.host.conj y)‖ = ‖tauEmb D lam τ y‖ := by
  first | exact @GlobalTheory.KerStd.tauSg_invol_norm_conj_eq | exact GlobalTheory.KerStd.tauSg_invol_norm_conj_eq | (intros; apply GlobalTheory.KerStd.tauSg_invol_norm_conj_eq <;> assumption)
