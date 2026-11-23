import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairEmbeddingsCongrModRootMinusD
import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColR
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Inertia
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_embeddings_congr_mod_root_minus_d : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ (ι : ℂ ≃+* ℂ_[p]) (cE s : D.host.E ≃+* D.host.E) (δ : D.host.E), (∀ y, cE y = D.host.conj y) → δ ^ 2 = -(p : D.host.E) → s δ = -δ → (∀ y, s (s y) = y) → (∀ (t : HH D) (y : D.host.E), TaylorLogMetric.embT D (tauPl D (true, t)) y = TaylorLogMetric.embT D (tauPl D (false, t)) (s (cE y))) → (∀ (τ : D.what₂.Tau) (y : D.host.E), s y = y → ι (TaylorLogMetric.embT D τ y) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) → (‖ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))‖ ≤ 1 ∧ ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ)) ≠ 0) ∧ ∀ (t : HH D) (y : 𝓞 D.host.E), ‖GlobalTheory.DFrame.rho D ι (false, t) (D.host.conj (y : D.host.E)) - GlobalTheory.DFrame.rho D ι (true, t) (y : D.host.E)‖ ≤ ‖ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))‖ := by
  first | exact @GlobalTheory.DFrame.congr_at_d | exact GlobalTheory.DFrame.congr_at_d | (intros; apply GlobalTheory.DFrame.congr_at_d <;> assumption)
