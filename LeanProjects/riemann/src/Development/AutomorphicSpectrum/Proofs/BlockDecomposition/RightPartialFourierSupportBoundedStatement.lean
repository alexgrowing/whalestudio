import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightPartialFourierSupportBounded
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_partial_fourier_support_bounded : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ Φ ∈ LFS.SB F, ∀ h : GL (Fin 2) F, ∃ R : ℝ, ∀ z : GL (Fin 2) F, Rpart ψ (Pf Φ h z) ≠ 0 → (∀ i j, (modulus (z.val i j) : ℝ) ≤ R) ∧ (∀ i, (modulus (((z⁻¹ : GL (Fin 2) F).val *ᵥ e1) i) : ℝ) ≤ R) := by
  first | exact @GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Supp.support_bounded | exact GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Supp.support_bounded | (intros; apply GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Supp.support_bounded <;> assumption)
