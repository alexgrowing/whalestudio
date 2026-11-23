import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackContractionScalarsIdentity
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_contraction_scalars_identity : ∀ (m m' g g' k k' x x' A A' Δ Δ' : ℂ) (n n' c c' : ℤ), m ≠ 0 → m' ≠ 0 → g ≠ 0 → g' ≠ 0 → k ≠ 0 → k' ≠ 0 → x ≠ 0 → x' ≠ 0 → A ≠ 0 → A' ≠ 0 → Δ ≠ 0 → Δ' ≠ 0 → (g' * m' * k') * (g * m * k)⁻¹ * (Δ⁻¹ * A) ^ (-c) * (Δ'⁻¹ * A') ^ c' * ((Δ⁻¹ * A) ^ n' * (Δ'⁻¹ * A') ^ (-n))⁻¹ * (k * x' / (k' * x)) = (m⁻¹ * A ^ (-n')) * (m' * A' ^ n) * (x⁻¹ * g⁻¹ * Δ ^ (n' + c) * A ^ (-c)) * (x' * g' * Δ' ^ (-(n + c')) * A' ^ c') := by
  first | exact @GlobalTheory.TwV.DelB.pullback_contraction_scalars | exact GlobalTheory.TwV.DelB.pullback_contraction_scalars | (intros; apply GlobalTheory.TwV.DelB.pullback_contraction_scalars <;> assumption)
