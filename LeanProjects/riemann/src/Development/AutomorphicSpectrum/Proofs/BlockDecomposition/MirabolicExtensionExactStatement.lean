import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicExtensionExact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_extension_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A B C : MRep k n), MExt A B C → Ses A.ρ B.ρ C.ρ := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.ses_of_mext | exact GlobalTheory.CompanionTheory.LeibOrd.ses_of_mext | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.ses_of_mext <;> assumption)
