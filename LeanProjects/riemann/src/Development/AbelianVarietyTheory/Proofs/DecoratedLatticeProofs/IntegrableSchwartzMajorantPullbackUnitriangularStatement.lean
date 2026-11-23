import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableSchwartzMajorantPullbackUnitriangular
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_schwartzMajorant_pullback_unitriangular : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m ρ : ℕ) (vU : VolU D ρ) (x : Matrix (Fin m) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∃ N : ℕ, ∀ K : Set (Mx D m ρ), IsCompact K → Integrable (fun u : UX D ρ => maj θ K N ((rat x : Mx D m ρ) ⬝ u.1.1)) vU.ν := by
  first | exact @GlobalTheory.Unf.pull_integrable | exact GlobalTheory.Unf.pull_integrable | (intros; apply GlobalTheory.Unf.pull_integrable <;> assumption)
