import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrbitGLNearOne
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClopenCoset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZpowMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_orbit_GL_near_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ} (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k)) (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (U : Set (GL (Fin d) k)), U ∈ 𝓝 (1 : GL (Fin d) k) → ∀ x : Fin d → k, x ≠ 0 → ∃ s : ℕ, ∀ y : Fin d → k, y - x ∈ (latZ z (s : ℤ)).sub → ∃ g ∈ U, (g : Matrix (Fin d) (Fin d) k).mulVec x = y := by
  first | exact @GlobalTheory.CompanionTheory.BZCore.exists_mem_nhds_one_mulVec_eq | exact GlobalTheory.CompanionTheory.BZCore.exists_mem_nhds_one_mulVec_eq | (intros; apply GlobalTheory.CompanionTheory.BZCore.exists_mem_nhds_one_mulVec_eq <;> assumption)
