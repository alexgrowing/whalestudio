import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSubValueZeroRapidDecay
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_sub_value_zero_rapid_decay : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ∀ (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι) {C : Set (GL ι 𝔸[k])} (hC : IsCompact C) (r : ℕ), ∃ M : ℝ, ∀ h ∈ C, ∀ t : {x : ℝ // 0 < x}, 1 ≤ (t : ℝ) →
      ‖thetaC F (scalC (moduleSection w t) * h) - F 0‖ ≤ ((t : ℝ) ^ r)⁻¹ * M := by
  first | exact @GlobalTheory.CompanionTheory.EisThCDecay.exists_norm_thetaC_sub_le | exact GlobalTheory.CompanionTheory.EisThCDecay.exists_norm_thetaC_sub_le | (intros; apply GlobalTheory.CompanionTheory.EisThCDecay.exists_norm_thetaC_sub_le <;> assumption)
