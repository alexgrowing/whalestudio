import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralLinearChangeModulus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_linear_change_modulus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (A : GL (Fin t) k) (φ : (Fin t → k) → W) (l : IsLocallyConstant φ) (c : HasCompactSupport φ), @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (_root_.borel _) _ _ (muD k t) (fun d => φ ((A⁻¹ : GL (Fin t) k).val *ᵥ d)) = ((dpow t 1 A : ℂˣ) : ℂ) • @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (_root_.borel _) _ _ (muD k t) φ := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_mulVec | exact GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_mulVec | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_mulVec <;> assumption)
