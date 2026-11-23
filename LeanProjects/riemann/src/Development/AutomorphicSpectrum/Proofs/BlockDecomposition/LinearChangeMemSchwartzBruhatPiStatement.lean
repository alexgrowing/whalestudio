import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearChangeMemSchwartzBruhatPi
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearChange_mem_schwartzBruhatPi : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ∀ {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι) (A : GL ι 𝔸[k]), ltr A F ∈ schwartzBruhatPi k ι := by
  first | exact @GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem | exact GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem | (intros; apply GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem <;> assumption)
