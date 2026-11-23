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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedNearIdentity
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.Stab

theorem hRep_fix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ z : V ⊗[ℂ] W, ∃ U ∈ nhds (1 : Mir k (i + t)), ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ U → hRep τ σ h z = z := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ z
  have hs : IsSmooth (hRep τ σ) :=
    isSmooth_comp (isSmooth_extTensor hτ hσ) _ (GlobalTheory.CompanionTheory.BZPhiPG.Onto.continuous_pgProj k i t)
  obtain ⟨O, hO, e⟩ := isOpen_induced_iff.1 (hs z)
  have hmem : ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ O ↔ hRep τ σ h z = z := fun h =>
    Set.ext_iff.1 e h
  have h1 : (1 : Mir k (i + t)) ∈ O := (hmem 1).2 (by simp)
  exact ⟨O, hO.mem_nhds h1, fun h hh => (hmem h).1 hh⟩

end GlobalTheory.CompanionTheory.BZPsiPG.Stab
