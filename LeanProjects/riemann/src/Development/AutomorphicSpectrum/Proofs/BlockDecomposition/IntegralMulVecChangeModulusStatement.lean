import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralMulVecChangeModulus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_mulVec_change_modulus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (w : GL (Fin n) k) (F : (Fin n → k) → W),
  IsLocallyConstant F → HasCompactSupport F →
  @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) (fun d => F ((w⁻¹ : GL (Fin n) k).1.mulVec d)) =
    ((dpow n 1 w : ℂˣ) : ℂ) • @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) F := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_subst | exact GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_subst | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_subst <;> assumption)
