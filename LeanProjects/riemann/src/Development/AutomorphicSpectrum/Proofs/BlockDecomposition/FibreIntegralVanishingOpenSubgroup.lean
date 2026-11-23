import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralIntertwinesUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UMLeviMulUMLevi
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibInvK

theorem fibV_mul_right_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (z : V ⊗[ℂ] W) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ (h : HPG k i t) (β : Mir k (i + t)), β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK → b.1.1.1 ((h : Mir k (i + t)) * β) = hRep τ σ h z) → (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → ∀ b' ∈ K₁, ∀ g : GL (Fin (i + t)) k, fibV b (g * b') = fibV b g := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ c K₁ hK z b hval hzero b' hb' g
  have hβ : GlobalTheory.BZMir.levi k (i + t) b' ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK := by
    show ∃ y ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt (i + t) c, ∃ a ∈ K₁,
      GlobalTheory.BZMir.levi k (i + t) b' = GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) y * GlobalTheory.BZMir.levi k (i + t) a
    exact ⟨0, zero_mem _, b', hb', by rw [GlobalTheory.CompanionTheory.BZPsiPG.uM_zero, one_mul]⟩
  have key : ∀ p : GlobalTheory.BZMir.Mir k (i + t), ∀ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK,
      b.1.1.1 (p * β) = b.1.1.1 p := by
    intro p β hβ
    by_cases hp : ∃ h : GlobalTheory.BZMir.Leib.HPG k i t,
        ∃ β₀ ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : GlobalTheory.BZMir.Mir k (i + t)) * β₀
    · obtain ⟨h, β₀, hβ₀, rfl⟩ := hp
      rw [mul_assoc, hval h (β₀ * β) (Subgroup.mul_mem _ hβ₀ hβ), hval h β₀ hβ₀]
    · have hp' : ¬ ∃ h : GlobalTheory.BZMir.Leib.HPG k i t,
          ∃ β₀ ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK,
            p * β = (h : GlobalTheory.BZMir.Mir k (i + t)) * β₀ := by
        rintro ⟨h, β₀, hβ₀, he⟩
        refine hp ⟨h, β₀ * β⁻¹, Subgroup.mul_mem _ hβ₀ (Subgroup.inv_mem _ hβ), ?_⟩
        rw [← mul_assoc, ← he, mul_inv_cancel_right]
      rw [hzero _ hp', hzero _ hp]
  funext v
  unfold GlobalTheory.CompanionTheory.BZPsiPG.fibV
  rw [map_mul, ← mul_assoc]
  exact key _ _ hβ

end GlobalTheory.CompanionTheory.BZPsiPG.FibInvK

end
