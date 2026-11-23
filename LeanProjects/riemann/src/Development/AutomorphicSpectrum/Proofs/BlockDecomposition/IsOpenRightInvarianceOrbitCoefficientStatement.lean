import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenRightInvarianceOrbitCoefficient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_right_invariance_orbit_coefficient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ),
  IsOpen {g : Mir k (i + (t + 1)) | ∀ m, eO ψ f (m * g) = eO ψ f m} := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.isOpen_eO_rightPeriods | exact GlobalTheory.CompanionTheory.BZPhiPG.isOpen_eO_rightPeriods | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.isOpen_eO_rightPeriods <;> assumption)
