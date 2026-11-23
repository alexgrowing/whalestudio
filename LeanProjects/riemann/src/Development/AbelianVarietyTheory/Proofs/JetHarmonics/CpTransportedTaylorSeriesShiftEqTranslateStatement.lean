import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesShiftEqTranslate
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cpTransportedTaylorSeries_shift_eq_translate : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω ζ : ℂ_[q]) (p : ℂ) (φ : ℂ → ℂ), M.MChart ω → M.At ω ζ p → Ell M.L φ → AnalyticAt ℂ φ 0 → Bdd (hat M.ι (C ω * logS) φ) → ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = φ (z + p)) ∧ hat M.ι (C ω * logS) ψ = shiftS ζ (hat M.ι (C ω * logS) φ) := by
  first | exact @GlobalTheory.MomOne.Transfer.shift_eq_hat_translate | exact GlobalTheory.MomOne.Transfer.shift_eq_hat_translate | (intros; apply GlobalTheory.MomOne.Transfer.shift_eq_hat_translate <;> assumption)
