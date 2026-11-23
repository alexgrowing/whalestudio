import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLattices
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwU.XbEntire

theorem entire_of_pull : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a b : ℕ} (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (Θ K : TaylorLogMetric.VC D a b → ℂ) (s : ℂ), e * star e = 1 → e' * star e' = 1 → s ≠ 0 → Differentiable ℂ K → (∀ z, K z = s * TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) e e' Θ z) → Differentiable ℂ Θ := by
  intro D cc δ a b e e' Θ K s he he' hs hK hKΘ
  have hinv : ∀ z, Θ z = s⁻¹ * K (Formalism.L2.KerInert.PullbackComparison.tPullL cc δ (star e) (star e') z) := by
    intro z
    rw [hKΘ, ← mul_assoc, inv_mul_cancel₀ hs, one_mul, Formalism.L2.KerInert.PullbackComparison.tPullL_apply]
    show Θ z = Θ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) e e'
      (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (star e) (star e') z))
    rw [GlobalTheory.TwU.KerMove.tPull_tPull, mul_eq_one_comm.1 he, mul_eq_one_comm.1 he', GlobalTheory.TwU.KerMove.tPull_one]
  have hf : Θ = fun z => s⁻¹ * K (Formalism.L2.KerInert.PullbackComparison.tPullL cc δ (star e) (star e') z) := funext hinv
  rw [hf]
  exact ((hK.comp (Formalism.L2.KerInert.PullbackComparison.tPullL cc δ (star e) (star e')).differentiable).const_mul _)

end GlobalTheory.TwU.XbEntire
