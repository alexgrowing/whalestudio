import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualLocalBasesEigenframeAtRamifiedPrime
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLocalBases_eigenframe_at_ramifiedPrime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), p = D.host.d → ∀ ι : ℂ ≃+* ℂ_[p], Formalism.L2.KerInert.IotaExt lm ι → ∀ (cD : D.what₂.Tau → ℂ), IsDgen D cD → ∀ (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (κ : D.what₂.Tau → ℂ_[p]), GlobalTheory.KerStd.StdBases D lm L P → GlobalTheory.KerStd.StdBases D lm L' P' → (∀ τ, ‖κ τ‖ ≤ ‖TaylorLogMetric.lamC lm (cD τ)‖) → ∃ u : HH D → ℂ_[p], (∀ t, ‖u t‖ ≤ 1) ∧ ∀ L₁ L₁', TaylorLogMetric.admitted D N N' L₁ L₁' → TaylorLogMetric.EqAt D p L L₁ → TaylorLogMetric.EqAt D p L' L₁' → ∃ (J : Type) (_ : Fintype J) (v : J → DVar X.Tau N N' → ℂ) (A : J → (Bool × HH D) × Fin N × Fin N' → ℂ_[p]) (cE sE : D.host.E ≃+* D.host.E) (δE : D.host.E) (emb : Bool × HH D → (D.host.E →+* ℂ_[p])) (act : 𝓞 D.host.E → (DVar X.Tau N N' → ℂ) →ₗ[ℂ] (DVar X.Tau N N' → ℂ)), Formalism.L2.Th1.GD.IsEigenFrame ι (cmL a₀ b₀ D.host.d ha hd lam hlam) (ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))) (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF (TaylorLogMetric.tor0 D cc δ) L₁ L₁') D.host.E cE sE δE emb act v A u ∧ ∀ i x, frameM (ι : ℂ →+* ℂ_[p]) v A i x = κ (s.iT i.1) * TaylorLogMetric.chgB D lm P P' (s.iT i.1, i.2) ((0 : ZMod 1), (tauPl D x.1, x.2)) := by
  first | exact @GlobalTheory.Proof.dualLocalBases_eigenframe_at_ramifiedPrime.eigenframe_at_d | exact GlobalTheory.Proof.dualLocalBases_eigenframe_at_ramifiedPrime.eigenframe_at_d | (intros; apply GlobalTheory.Proof.dualLocalBases_eigenframe_at_ramifiedPrime.eigenframe_at_d <;> assumption)
