import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSummableMajorantLatticeSum
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_summable_majorant_lattice_sum : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ∀ {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι) {C : Set (GL ι 𝔸[k])} (hC : IsCompact C), ∃ u : (ι → k) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ ξ : ι → k,
      ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ)‖ ≤ u ξ := by
  first | exact @GlobalTheory.CompanionTheory.EisRkNBound.exists_summable_bound_thetaC | exact GlobalTheory.CompanionTheory.EisRkNBound.exists_summable_bound_thetaC | (intros; apply GlobalTheory.CompanionTheory.EisRkNBound.exists_summable_bound_thetaC <;> assumption)
